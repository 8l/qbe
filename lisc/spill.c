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
		fprintf(stderr, "\n> Loop information:\n");
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

static Bits *f;   /* temps to prioritize in registers (for tcmp1) */
static Tmp *tmp;  /* current temporaries (for tcmpX) */
static int ntmp;  /* current # of temps (for limit) */
static int locs;  /* stack size used by locals */
static int slot4; /* next slot of 4 bytes */
static int slot8; /* ditto, 8 bytes */

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
	s = tmp[t].slot;
	if (s == -1) {
		assert(NAlign == 3);
		/* nice logic to pack stack slots
		 * on demand, there can be only
		 * one hole and slot4 points to it
		 *
		 * invariant: slot4 <= slot8
		 */
		if (tmp[t].wide) {
			s = slot8;
			if (slot4 == slot8)
				slot4 += 2;
			slot8 += 2;
		} else {
			s = slot4;
			if (slot4 == slot8) {
				slot8 += 2;
				slot4 += 1;
			} else
				slot4 = slot8;
		}
		s += locs;
		tmp[t].slot = s;
	}
	return SLOT(s);
}

static void
store(Ref r, int s)
{
	if (tmp[r.val].wide)
		emit(OStorel, 0, R, r, SLOT(s));
	else
		emit(OStorew, 0, R, r, SLOT(s));
}

static void
limit(Bits *b, int k, Bits *fst)
{
	static int *tarr, maxt;
	int i, t, nt;

	nt = bcnt(b);
	if (nt <= k)
		return;
	if (nt > maxt) {
		free(tarr);
		tarr = emalloc(nt * sizeof tarr[0]);
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
	for (; i<nt; i++)
		slot(tarr[i]);
}

static void
sethint(Bits *u, ulong r)
{
	int t;

	for (t=Tmp0; t<ntmp; t++)
		if (BGET(*u, t))
			tmp[phicls(t, tmp)].hint.m |= r;
}

static void
reloads(Bits *u, Bits *v)
{
	int t;

	for (t=Tmp0; t<ntmp; t++)
		if (BGET(*u, t) && !BGET(*v, t))
			emit(OLoad, tmp[t].wide, TMP(t), slot(t), R);
}

static Ins *
dopm(Blk *b, Ins *i, Bits *v)
{
	int n, s, t;
	Bits u;
	Ins *i1;
	ulong r;

	/* consecutive copies from
	 * registers need to handled
	 * as one large instruction
	 *
	 * fixme: there is an assumption
	 * that calls are always followed
	 * by copy instructions here, this
	 * might not be true if previous
	 * passes change
	 */
	i1 = ++i;
	do {
		i--;
		t = i->to.val;
		if (!req(i->to, R))
		if (BGET(*v, t)) {
			BCLR(*v, t);
			s = tmp[t].slot;
			if (s != -1)
				store(i->to, s);
		}
		BSET(*v, i->arg[0].val);
	} while (i != b->ins &&
		(i-1)->op == OCopy &&
		isreg((i-1)->arg[0]));
	u = *v;
	if (i != b->ins && (i-1)->op == OCall) {
		v->t[0] &= ~calldef(*(i-1), 0);
		limit(v, NReg - NRSave, 0);
		r = 0;
		for (n=0; n<NRSave; n++)
			r |= BIT(rsave[n]);
		v->t[0] |= calluse(*(i-1), 0);
	} else {
		limit(v, NReg, 0);
		r = v->t[0];
	}
	sethint(v, r);
	reloads(&u, v);
	do
		emiti(*--i1);
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
	int n, m, z, l, t, lvarg[2];
	Bits u, v, w;
	Ins *i;
	int j, s;
	Phi *p;
	Mem *ma;
	ulong r;

	tmp = fn->tmp;
	ntmp = fn->ntmp;
	locs = fn->slot;
	slot4 = 0;
	slot8 = 0;
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
		BZERO(v);
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
			v = liveon(b, s1);
			w = v;
			if (s2) {
				u = liveon(b, s2);
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
		r = 0;
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			assert(bcnt(&v) <= NReg);
			i--;
			if (i->op == OCopy && isreg(i->arg[0])) {
				i = dopm(b, i, &v);
				continue;
			}
			s = -1;
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				t = i->to.val;
				if (BGET(v, t))
					BCLR(v, t);
				else {
					u = v;
					limit(&v, NReg-1, 0);
					reloads(&u, &v);
				}
				s = tmp[t].slot;
			}
			BZERO(w);
			j = opdesc[i->op].nmem;
			j -= rtype(i->arg[0]) == RAMem;
			j -= rtype(i->arg[1]) == RAMem;
			for (m=0; m<2; m++)
				switch (rtype(i->arg[m])) {
				case RAMem:
					t = i->arg[m].val;
					ma = &fn->mem[t & AMask];
					if (rtype(ma->base) == RTmp) {
						BSET(v, ma->base.val);
						BSET(w, ma->base.val);
					}
					if (rtype(ma->index) == RTmp) {
						BSET(v, ma->index.val);
						BSET(w, ma->index.val);
					}
					break;
				case RTmp:
					t = i->arg[m].val;
					lvarg[m] = BGET(v, t);
					BSET(v, t);
					if (j-- <= 0)
						BSET(w, t);
					break;
				}
			u = v;
			limit(&v, NReg, &w);
			for (m=0; m<2; m++)
				if (rtype(i->arg[m]) == RTmp) {
					t = i->arg[m].val;
					if (!BGET(v, t)) {
						/* do not reload if the
						 * the temporary was dead
						 */
						if (!lvarg[m])
							BCLR(u, t);
						i->arg[m] = slot(t);
					}
				}
			r = v.t[0] & (BIT(Tmp0)-1);
			if (r)
				sethint(&v, r);
			reloads(&u, &v);
			if (s != -1)
				store(i->to, s);
			emiti(*i);
		}
		assert(!r || b==fn->start);

		for (p=b->phi; p; p=p->link) {
			assert(rtype(p->to) == RTmp);
			t = p->to.val;
			if (BGET(v, t)) {
				BCLR(v, t);
				s = tmp[t].slot;
				if (s != -1)
					store(p->to, s);
			} else
				p->to = slot(p->to.val);
		}
		b->in = v;
		b->nins = &insb[NIns] - curi;
		idup(&b->ins, curi, b->nins);
	}

	/* align the locals to a 16 byte boundary */
	assert(NAlign == 3);
	slot8 += slot8 & 3;
	fn->slot += slot8;

	if (debug['S']) {
		fprintf(stderr, "\n> Block information:\n");
		for (b=fn->start; b; b=b->link) {
			printf("\t%-10s (% 5d) ", b->name, b->loop);
			dumpts(&b->out, fn->tmp, stdout);
		}
		fprintf(stderr, "\n> After spilling:\n");
		printfn(fn, stderr);
	}
}
