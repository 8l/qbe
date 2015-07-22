#include "lisc.h"


static void
loopmark(Blk **rpo, int head, int n)
{
	uint p;
	Blk *b;

	b = rpo[n];
	if (n <= head || b->visit == head)
		return;
	b->visit = head;
	b->loop *= 10;
	for (p=0; p<b->npred; p++)
		loopmark(rpo, head, b->pred[p]->id);
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
	int n, m;
	uint a;
	Blk *b;
	Ins *i;
	Sym *s;
	Phi *p;

	for (b=fn->start; b; b=b->link) {
		b->loop = 1;
		b->visit = -1;
	}
	for (n=0; n<fn->nblk; n++) {
		b = fn->rpo[n];
		for (a=0; a<b->npred; a++) {
			m = b->pred[a]->id;
			if (m >= n)
				loopmark(fn->rpo, n, m);
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
			assert(rtype(p->to) == RSym);
			assert(fn->sym[p->to.val].type == STmp);
			symuse(p->to, 0, 0, fn);
			for (a=0; a<p->narg; a++)
				symuse(p->arg[a], 1, 0, fn);
		}
		n = b->loop;
		for (i=b->ins; i-b->ins < b->nins; i++) {
			symuse(i->to, 0, n, fn);
			symuse(i->arg[0], 1, n, fn);
			symuse(i->arg[1], 1, n, fn);
		}
		symuse(b->jmp.arg, 1, n, fn);
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
	for (t=0/*Tmp0*/; t<ntmp; t++)
		if (BGET(*b, t)) {
			assert(sym[t].type == STmp);
			tmp[i++] = t;
		}
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
	return res;
}

static int
loopscan(Bits *use, Blk **rpo, int hd, int n)
{
	int z, pl;
	Blk *b;

	/* using a range to represent
	 * loops does not work:
	 * in the example above, when
	 * analyzing the block in the
	 * loop with the smallest rpo
	 * we will not account for the
	 * other one
	 *
	 * todo, use predecessors to
	 * fix that
	 */

	pl = 0;
	*use = (Bits){{0}};
	for (; hd<=n; hd++) {
		b = rpo[hd];
		if (b->nlive > pl)
			pl = b->nlive;
		for (z=0; z<BITS; z++)
			use->t[z] |= b->gen.t[z];
	}
	for (z=0; z<BITS; z++)
		use->t[z] &= rpo[n]->out.t[z];
	return pl;
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
	int n, z, k, pl;
	Bits v, w;
	Ins *i;
	int j;

	sym = fn->sym;
	ntmp = fn->ntmp;
	assert(ntmp < NBit*BITS);

	for (n=fn->nblk-1; n>=0; n--) {
		/* invariant: m>n => in,out of m updated */
		b = fn->rpo[n];

		/* 1. find temporaries in registers at
		 * the end of the block (put them in v) */
		s1 = b->s1;
		s2 = b->s2;
		// k = NReg - !req(b->jmp.arg, R);
		k = 4 - !req(b->jmp.arg, R);
		if (!s1) {
			assert(!s2);
			v = (Bits){{0}};
		} else if (s1->id <= n || (s2 && s2->id <= n)) {
			/* back-edge */
			hd = s1;
			if (s2 && s2->id <= hd->id)
				hd = s2;
			pl = loopscan(&v, fn->rpo, hd->id, n);
			j = bcnt(&v);
			if (j < k) {
				w = b->out;
				for (z=0; z<BITS; z++)
					w.t[z] &= ~v.t[z];
				j = bcnt(&w);   /* live through */
				w = limit(&w, k - (pl - j), 0);
				for (z=0; z<BITS; z++)
					v.t[z] |= w.t[z];
			} else if (j > k)
				v = limit(&v, k, 0);
		} else {
			v = s1->in;
			w = s1->in;
			if (s2)
				for (z=0; z<BITS; z++) {
					v.t[z] |= s2->in.t[z];
					w.t[z] &= s2->in.t[z];
				}
			for (z=0; z<BITS; z++) {
				assert(!(v.t[z] & ~b->out.t[z]));
				assert(!(w.t[z] & ~b->out.t[z]));
			}
			assert(bcnt(&w) <= NReg);
			assert(bcnt(&w) <= bcnt(&v));
			v = limit(&v, k, &w);
		}
		assert(bcnt(&v) <= k);
		b->out = v;

		/* 2. process the block instructions */
		curi = &insb[NIns];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			i--;
			;
		}
	}
}
