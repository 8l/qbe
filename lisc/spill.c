#include "lisc.h"


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
 * requires rpo
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

	/* todo, have somewhat proper loop
	 * detection for example on this
	 * cfg, it's bogus:
	 * +> loop <+
	 * |   /\   |
	 * +- a  b -+
	 */
	for (b=fn->start; b; b=b->link)
		b->loop = 1;
	for (n=fn->nblk-1; n>=0; n--) {
		b = fn->rpo[n];
		m = n;
		if (b->s1 && b->s1->id < m)
			m = b->s1->id;
		if (b->s2 && b->s2->id < m)
			m = b->s2->id;
		for (; m<n; m++)
			fn->rpo[m]->loop *= 10;
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
			symuse(i->arg[0], 1, n, fn);
		}
		symuse(b->jmp.arg, 1, n, fn);
	}
}

static int
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
static Bits w;
static Sym *sym;

#if 0
static void
emit(short op, Ref to, Ref arg0, Ref arg1)
{
	if (curi == insb)
		diag("spill: too many instructions");
	*curi-- = (Ins){op, to, {arg0, arg1}};
}
#endif

static int
tcmp(const void *pa, const void *pb)
{
	int a, b;

	/* so here, we make sure temporaries
	 * in w are sorted first in the list
	 * no matter their cost
	 */
	a = *(int *)pa;
	b = *(int *)pb;
	assert(sym[a].type==STmp && sym[b].type==STmp);
	if (BGET(w, a))
		return BGET(w, b) ? sym[b].cost-sym[a].cost : -1;
	else
		return BGET(w, b) ? +1 : sym[b].cost-sym[a].cost;
}

/* spill code insertion
 * requires spill costs and rpo
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
	Bits v;
	int n, z, j, k, l;
	Blk *b, *s1, *s2;
	Ins *i;
	int *tmp, maxt, nt;

	sym = fn->sym;
	tmp = 0;
	maxt = 0;
	for (n=fn->nblk-1; n>=0; n--) {
		/* invariant: m>n => in,out of m updated */
		b = fn->rpo[n];
		curi = &insb[NIns-1];

		/* 1. find temporaries in registers at
		 * the end of the block (put them in v) */
		s1 = b->s1;
		s2 = b->s2;
		k = NReg - !req(b->jmp.arg, R);

		if ((s1 && s1->id <= n) || (s2 && s2->id <= n)) {
			/* potential back-edge */
		} else {
			if (s1) {
				v = s1->in; /* could be in reg */
				w = s1->in; /* will be in reg */
			} else {
				w = (Bits){{0}};
				v = (Bits){{0}};
			}
			if (s2) {
				for (z=0; z<BITS; z++) {
					v.t[z] |= s2->in.t[z];
					w.t[z] &= s2->in.t[z];
				}
			}
/* #if 0 */
			for (z=0; z<BITS; z++) {
				assert(!(v.t[z] & ~b->out.t[z]));
				assert(!(w.t[z] & ~b->out.t[z]));
			}
			assert(bcnt(&w) <= NReg);
			assert(bcnt(&w) <= bcnt(&v));
/* #endif */
			nt = bcnt(&v);
			if (nt > maxt) {
				free(tmp);
				tmp = alloc(nt * sizeof tmp[0]);
				maxt = nt;
			}
			j=0;
			for (l=0/*Tmp0*/; l<fn->ntmp; l++)
				if (BGET(v, l)) {
					assert(fn->sym[l].type == STmp);
					tmp[j++] = l;
				}
			assert(j == nt);
			qsort(tmp, nt, sizeof tmp[0], tcmp);
			v = (Bits){{0}};
			for (j=0; j<k; j++)
				BSET(v, j);
		}

		/* 2. process the block instructions */
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			i--;
			;
		}
	}
	free(tmp);
}
