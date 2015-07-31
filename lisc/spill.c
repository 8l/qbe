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
			if (rtype(p->arg[a]) == RSym)
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
symuse(Ref r, int use, int loop, Fn *fn)
{
	Sym *s;

	if (rtype(r) != RSym)
		return;
	s = &fn->sym[r.val];
	if (s->type != STmp)
		return;
	if (use)
		s->nuse++;
	else
		s->ndef++;
	s->cost += loop;
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
	Sym *s;
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
			dumpss(&b->gen, fn->sym, stderr);
		}
	}
	for (s=fn->sym; s-fn->sym < fn->ntmp; s++) {
		s->cost = 0;
		s->nuse = 0;
		s->ndef = 0;
		if (s->type == SReg)
			s->cost = 100000;
	}
	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link) {
			/* zero cost for temporaries used
			 * in phi instructions */
			symuse(p->to, 0, 0, fn);
			for (a=0; a<p->narg; a++) {
				n = p->blk[a]->loop;
				assert(b->npred==p->narg &&
					"wrong cfg");
				n /= b->npred;
				symuse(p->arg[a], 1, n, fn);
			}
		}
		n = b->loop;
		for (i=b->ins; i-b->ins < b->nins; i++) {
			symuse(i->to, 0, n, fn);
			symuse(i->arg[0], 1, n, fn);
			symuse(i->arg[1], 1, n, fn);
		}
		symuse(b->jmp.arg, 1, n, fn);
	}
	if (debug['S']) {
		fprintf(stderr, "\n> Spill costs:\n");
		for (n=Tmp0; n<fn->ntmp; n++)
			fprintf(stderr, "\t%-10s %d\n",
				fn->sym[n].name,
				fn->sym[n].cost);
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
static Bits *f;  /* temps to prioritize in registers (for tcmp1) */
static Sym *sym; /* current symbol table (for tcmpX) */
static int ntmp; /* current # of temps (for limit) */
static uint ns;  /* current # of spill slots */

static int
tcmp0(const void *pa, const void *pb)
{
	return sym[*(int *)pb].cost - sym[*(int *)pa].cost;
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

	assert(sym[t].type == STmp);
	s = sym[t].spill;
	if (!s) {
		s = 1 + ns++;
		sym[t].spill = s;
	}
	return SLOT(s);
}

static void
emit(short op, Ref to, Ref arg0, Ref arg1)
{
	if (curi == insb)
		diag("spill: too many instructions");
	*--curi = (Ins){op, to, {arg0, arg1}};
}

static Bits
limit(Bits *b, int k, Bits *fst)
{
	static int *tmp, maxt;
	int i, t, nt;
	Bits res;

	nt = bcnt(b);
	if (nt <= k)
		return *b;
	if (nt > maxt) {
		free(tmp);
		tmp = alloc(nt * sizeof tmp[0]);
		maxt = nt;
	}
	i = 0;
	for (t=0; t<ntmp; t++)
		if (BGET(*b, t))
			tmp[i++] = t;
	assert(i == nt);
	if (!fst)
		qsort(tmp, nt, sizeof tmp[0], tcmp0);
	else {
		f = fst;
		qsort(tmp, nt, sizeof tmp[0], tcmp1);
	}
	res = (Bits){{0}};
	for (i=0; i<k && i<nt; i++)
		BSET(res, tmp[i]);
	for (; i<nt; i++) {
		slot(tmp[i]);
		if (curi)
			emit(OLoad, SYM(tmp[i]), slot(tmp[i]), R);
	}
	return res;
}

static void
setloc(Ref *pr, Bits *v, Bits *w)
{
	int t;

	/* <arch>
	 *   here we assume that the
	 *   machine can always support
	 *   instructions of the kind
	 *   reg = op slot, slot
	 *   if not, we need to add
	 *   't' to 'w' before calling
	 *   limit
	 */
	if (rtype(*pr) != RSym)
		return;
	t = pr->val;
	BSET(*v, t);
	*v = limit(v, NReg, w);
	if (curi->op == OLoad)
	if (curi->to.val == t)
		curi++;
	if (!BGET(*v, t))
		*pr = slot(t);
	else
		BSET(*w, t);
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
 * - Branching variables *must* be in
 *   register
 */
void
spill(Fn *fn)
{
	Blk *b, *s1, *s2, *hd;
	int n, z, l, t;
	Bits v, w;
	Ins *i;
	int j, s;
	Phi *p;

	ns = 0;
	sym = fn->sym;
	ntmp = fn->ntmp;
	assert(ntmp < NBit*BITS);

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
				w = limit(&w, NReg - (l - j), 0);
				for (z=0; z<BITS; z++)
					v.t[z] |= w.t[z];
			} else if (j > NReg)
				v = limit(&v, NReg, 0);
		} else if (s1) {
			v = s1->in;
			w = s1->in;
			if (s2)
				for (z=0; z<BITS; z++) {
					v.t[z] |= s2->in.t[z];
					w.t[z] &= s2->in.t[z];
				}
			assert(bcnt(&w) <= NReg);
			v = limit(&v, NReg, &w);
		}
		b->out = v;
		assert(bcnt(&v) <= NReg);

		/* 2. process the block instructions */
		if (rtype(b->jmp.arg) == RSym) {
			j = b->jmp.arg.val;
			if (!BGET(v, j) && l==NReg) {
				v = limit(&v, l-1, 0);
				b->out = v;
			}
			BSET(v, j);
		}
		curi = &insb[NIns];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			assert(bcnt(&v) <= NReg);
			i--;
			if (!req(i->to, R)) {
				assert(rtype(i->to)==RSym);
				j = i->to.val;
				if (BGET(v, j))
					BCLR(v, j);
				else
					v = limit(&v, NReg-1, &w);
				s = sym[j].spill;
			} else
				s = 0;
			w = (Bits){{0}};
			if (rtype(i->arg[1]) == RSym
			&& !req(i->to, R)
			&& opdesc[i->op].comm == F) {
				/* <arch>
				 *   here we make sure that we
				 *   will never have to compile
				 *   say: eax = sub ebx, eax
				 *   on a two-address machine
				 */
				BSET(w, i->to.val);
				BSET(v, i->to.val);
				setloc(&i->arg[1], &v, &w);
				BCLR(v, i->to.val);
				BCLR(w, i->to.val);
			} else
				setloc(&i->arg[1], &v, &w);
			setloc(&i->arg[0], &v, &w);
			if (s)
				emit(OStore, R, i->to, SLOT(s));
			emit(i->op, i->to, i->arg[0], i->arg[1]);
		}

		for (p=b->phi; p; p=p->link) {
			t = p->to.val;
			if (BGET(v, t)) {
				BCLR(v, t);
				s = sym[t].spill;
				if (s)
					emit(OStore, R, p->to, SLOT(s));
			} else
				p->to = slot(p->to.val);
		}
		free(b->ins);
		b->nins = &insb[NIns] - curi;
		b->ins = alloc(b->nins * sizeof(Ins));
		memcpy(b->ins, curi, b->nins * sizeof(Ins));
		b->in = v;
	}
	fn->nspill = ns;
}
