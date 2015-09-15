#include "lisc.h"

static void
loopmark(Blk *hd, Blk *b, Phi *p)
{
	int z, head;
	uint n, a;

	head = hd->id;
	if (b->id < head)
		return;
	for (; p; p=p->link)
		for (a=0; a<p->narg; a++)
			if (p->blk[a] == b)
			if (rtype(p->arg[a]) == RTmp)
				BSET(hd->gen, p->arg[a].val);
	if (b->visit == head)
		return;
	b->visit = head;
	b->loop *= 10;
	/* aggregate looping information at
	 * loop headers */
	for (z=0; z<BITS; z++)
		hd->gen.t[z] |= b->gen.t[z];
	if (b->nlive > hd->nlive)
		hd->nlive = b->nlive;
	for (n=0; n<b->npred; n++)
		loopmark(hd, b->pred[n], b->phi);
}

static void
tmpuse(Ref r, int use, int loop, Fn *fn)
{
	Tmp *t;

	if (rtype(r) != RTmp || r.val < Tmp0)
		return;
	t = &fn->tmp[r.val];
	t->nuse += use;
	t->ndef += !use;
	t->cost += loop;
}

/* evaluate spill costs of temporaries,
 * this also fills usage information
 * requires rpo, preds
 */
void
fillcost(Fn *fn)
{
	int n, hd;
	uint a;
	Blk *b;
	Ins *i;
	Tmp *t;
	Phi *p;

	for (b=fn->start; b; b=b->link) {
		b->loop = 1;
		b->visit = -1;
	}
	if (debug['S'])
		fprintf(stderr, "> Loop information:\n");
	for (n=0; n<fn->nblk; n++) {
		b = fn->rpo[n];
		hd = 0;
		for (a=0; a<b->npred; a++)
			if (b->pred[a]->id >= n) {
				loopmark(b, b->pred[a], b->phi);
				hd = 1;
			}
		if (hd && debug['S']) {
			fprintf(stderr, "\t%-10s", b->name);
			fprintf(stderr, " (% 3d) ", b->nlive);
			dumpts(&b->gen, fn->tmp, stderr);
		}
	}
	for (t=fn->tmp; t-fn->tmp < fn->ntmp; t++) {
		t->cost = t-fn->tmp < Tmp0 ? 1e6 : 0;
		t->nuse = 0;
		t->ndef = 0;
	}
	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link) {
			/* todo, the cost computation
			 * for p->to is not great... */
			tmpuse(p->to, 0, 0, fn);
			for (a=0; a<p->narg; a++) {
				n = p->blk[a]->loop;
				assert(b->npred==p->narg &&
					"wrong cfg");
				n /= b->npred;
				tmpuse(p->arg[a], 1, n, fn);
			}
		}
		n = b->loop;
		for (i=b->ins; i-b->ins < b->nins; i++) {
			tmpuse(i->to, 0, n, fn);
			tmpuse(i->arg[0], 1, n, fn);
			tmpuse(i->arg[1], 1, n, fn);
		}
		tmpuse(b->jmp.arg, 1, n, fn);
	}
	if (debug['S']) {
		fprintf(stderr, "\n> Spill costs:\n");
		for (n=Tmp0; n<fn->ntmp; n++)
			fprintf(stderr, "\t%-10s %d\n",
				fn->tmp[n].name,
				fn->tmp[n].cost);
		fprintf(stderr, "\n");
	}
}

int
bcnt(Bits *b) /* glad I can pull it :) */
{
	const uint64_t m1 = 0x5555555555555555;
	const uint64_t m2 = 0x3333333333333333;
	const uint64_t m3 = 0x0f0f0f0f0f0f0f0f;
	const uint64_t m4 = 0x00ff00ff00ff00ff;
	const uint64_t m5 = 0x0000ffff0000ffff;
	const uint64_t m6 = 0x00000000ffffffff;
	uint64_t tmp;
	int z, i;

	i = 0;
	for (z=0; z<BITS; z++) {
		tmp = b->t[z];
		if (!tmp)
			continue;
		tmp = (tmp&m1) + (tmp>> 1&m1);
		tmp = (tmp&m2) + (tmp>> 2&m2);
		tmp = (tmp&m3) + (tmp>> 4&m3);
		tmp = (tmp&m4) + (tmp>> 8&m4);
		tmp = (tmp&m5) + (tmp>>16&m5);
		tmp = (tmp&m6) + (tmp>>32&m6);
		i += tmp;
	}
	return i;
}

extern Ins insb[NIns], *curi; /* shared work buffer */
static Bits *f;   /* temps to prioritize in registers (for tcmp1) */
static Tmp *tmp;  /* current temporaries (for tcmpX) */
static int ntmp;  /* current # of temps (for limit) */
static int *svec; /* free slots vector */

static int
tcmp0(const void *pa, const void *pb)
{
	return tmp[*(int *)pb].cost - tmp[*(int *)pa].cost;
}

static int
tcmp1(const void *pa, const void *pb)
{
	int c;

	c = BGET(*f, *(int *)pb) - BGET(*f, *(int *)pa);
	return c ? c : tcmp0(pa, pb);
}

static Ref
slot(int t)
{
	int s;

	if (t < Tmp0)
		diag("spill: cannot spill register");
	s = tmp[t].spill;
	if (!s) {
		if (tmp[t].wide)
			s = slota(2, 1, svec);
		else
			s = slota(1, 0, svec);
		tmp[t].spill = s;
	}
	return SLOT(s);
}

static void
emit(Ins i)
{
	if (curi == insb)
		diag("spill: too many instructions");
	*--curi = i;
}

static void
store(Ref r, int s)
{
	if (tmp[r.val].wide)
		emit((Ins){OStorel, 0, R, {r, SLOT(s)}});
	else
		emit((Ins){OStorew, 0, R, {r, SLOT(s)}});
}

static int
limit(Bits *b, int k, Bits *fst)
{
	static int *tarr, maxt;
	int i, t, nt, w;

	nt = bcnt(b);
	if (nt <= k)
		return 0;
	if (nt > maxt) {
		free(tarr);
		tarr = alloc(nt * sizeof tarr[0]);
		maxt = nt;
	}
	i = 0;
	for (t=0; t<ntmp; t++)
		if (BGET(*b, t)) {
			BCLR(*b, t);
			tarr[i++] = t;
		}
	assert(i == nt);
	if (!fst)
		qsort(tarr, nt, sizeof tarr[0], tcmp0);
	else {
		f = fst;
		qsort(tarr, nt, sizeof tarr[0], tcmp1);
	}
	for (i=0; i<k && i<nt; i++)
		BSET(*b, tarr[i]);
	for (; i<nt; i++) {
		slot(tarr[i]);
		if (curi) {
			t = tarr[i];
			w = tmp[t].wide;
			emit((Ins){OLoad, w, TMP(t), {slot(t)}});
		}
	}
	return t;
}

static int
setloc(Ref *pr, Bits *v, Bits *w)
{
	int t;

	if (rtype(*pr) != RTmp)
		return 0;
	t = pr->val;
	BSET(*v, t);
	if (limit(v, NReg, w) == t)
		/* if t was spilled by limit,
		 * it was not live so we don't
		 * have to reload it */
		curi++;
	if (!BGET(*v, t)) {
		*pr = slot(t);
		return 1;
	} else {
		BSET(*w, t);
		return 0;
	}
}

static Bits
inregs(Blk *b, Blk *s) /* todo, move to live.c */
{
	Bits v;
	Phi *p;
	uint a;

	v = s->in;
	for (p=s->phi; p; p=p->link)
		for (a=0; a<p->narg; a++)
			if (p->blk[a] == b)
			if (rtype(p->arg[a]) == RTmp)
				BSET(v, p->arg[a].val);
	return v;
}

static Ins *
dopm(Blk *b, Ins *i, Bits *v)
{
	int j;
	Ins *i1;

	/* consecutive moves from
	 * registers need to handled
	 * as one large instruction
	 */
	i1 = i+1;
	for (;; i--) {
		if (!req(i->to, R))
			BCLR(*v, i->to.val);
		BSET(*v, i->arg[0].val);
		if (i == b->ins
		|| (i-1)->op != OCopy
		|| !isreg((i-1)->arg[0]))
			break;
	}
	if (i > b->ins && (i-1)->op == OCall) {
		calldef(*--i, &j);
		limit(v, NReg - NRSave + j, 0);
		v->t[0] &= ~calldef(*i, 0);
		v->t[0] |= calluse(*i, 0);
		setloc(&i->arg[0], v, &(Bits){{0}});
	} else
		limit(v, NReg, 0);
	do
		emit(*--i1);
	while (i1 != i);
	return i;
}

/* spill code insertion
 * requires spill costs, rpo, liveness
 *
 * Note: this will replace liveness
 * information (in, out) with temporaries
 * that must be in registers at block
 * borders
 *
 * Be careful with:
 * - OCopy instructions to ensure register
 *   constraints
 */
void
spill(Fn *fn)
{
	Blk *b, *s1, *s2, *hd;
	int n, z, l, t;
	Bits u, v, w;
	Ins *i;
	int j, s;
	Phi *p;

	svec = fn->svec;
	tmp = fn->tmp;
	ntmp = fn->ntmp;
	assert(ntmp < NBit*BITS);

	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link)
			tmp[p->to.val].wide = p->wide;
		for (i=b->ins; i-b->ins < b->nins; i++)
			if (rtype(i->to) == RTmp)
				tmp[i->to.val].wide = i->wide;
	}

	for (n=fn->nblk-1; n>=0; n--) {
		/* invariant: m>n => in,out of m updated */
		b = fn->rpo[n];

		/* 1. find temporaries in registers at
		 * the end of the block (put them in v) */
		curi = 0;
		s1 = b->s1;
		s2 = b->s2;
		v = (Bits){{0}};
		hd = 0;
		if (s1 && s1->id <= n)
			hd = s1;
		if (s2 && s2->id <= n)
		if (!hd || s2->id >= hd->id)
			hd = s2;
		if (hd) {
			/* back-edge */
			l = hd->nlive;
			for (z=0; z<BITS; z++)
				v.t[z] = hd->gen.t[z] & b->out.t[z];
			j = bcnt(&v);
			if (j < NReg) {
				w = b->out;
				for (z=0; z<BITS; z++)
					w.t[z] &= ~v.t[z];
				j = bcnt(&w);   /* live through */
				limit(&w, NReg - (l - j), 0);
				for (z=0; z<BITS; z++)
					v.t[z] |= w.t[z];
			} else if (j > NReg)
				limit(&v, NReg, 0);
		} else if (s1) {
			v = inregs(b, s1);
			w = v;
			if (s2) {
				u = inregs(b, s2);
				for (z=0; z<BITS; z++) {
					v.t[z] |= u.t[z];
					w.t[z] &= u.t[z];
				}
			}
			assert(bcnt(&w) <= NReg);
			limit(&v, NReg, &w);
		}
		b->out = v;
		assert(bcnt(&v) <= NReg);

		/* 2. process the block instructions */
		curi = &insb[NIns];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			assert(bcnt(&v) <= NReg);
			i--;
			if (i->op == OCopy && isreg(i->arg[0])) {
				i = dopm(b, i, &v);
				continue;
			}
			s = 0;
			w = (Bits){{0}};
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				t = i->to.val;
				if (BGET(v, t))
					BCLR(v, t);
				else
					limit(&v, NReg-1, 0);
				s = tmp[t].spill;
			}
			j = opdesc[i->op].nmem;
			if (!j && rtype(i->arg[0]) == RTmp)
				BSET(w, i->arg[0].val);
			j -= setloc(&i->arg[0], &v, &w);
			if (!j && rtype(i->arg[1]) == RTmp)
				BSET(w, i->arg[1].val);
			j -= setloc(&i->arg[1], &v, &w);
			if (s)
				store(i->to, s);
			emit(*i);
		}

		for (p=b->phi; p; p=p->link) {
			assert(rtype(p->to) == RTmp);
			t = p->to.val;
			if (BGET(v, t)) {
				BCLR(v, t);
				s = tmp[t].spill;
				if (s)
					store(p->to, s);
			} else
				p->to = slot(p->to.val);
		}
		b->in = v;
		free(b->ins);
		b->nins = &insb[NIns] - curi;
		b->ins = alloc(b->nins * sizeof(Ins));
		memcpy(b->ins, curi, b->nins * sizeof(Ins));
	}
}
