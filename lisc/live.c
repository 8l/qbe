#include "lisc.h"

static inline void
bset(Bits *b, Ref r)
{
	if (rtype(r) == RSym)
		BSET(*b, r.val);
}

/* liveness analysis
 * requires rpo computation
 */
void
filllive(Fn *f)
{
	Blk *b;
	Ins *i;
	Phi *p;
	int z, n, chg;
	uint a;
	Bits *kill, *use, *k, *u, bt;

	assert(f->ntmp <= NBit*BITS);
	kill = alloc(f->nblk * sizeof kill[0]);
	use = alloc(f->nblk * sizeof use[0]);
	for (b=f->start; b; b=b->link) {
		memset(&b->in, 0, sizeof(Bits));
		memset(&b->out, 0, sizeof(Bits));
	}
	for (b=f->start; b; b=b->link) {
		k = &kill[b->id];
		u = &use[b->id];
		for (p=b->phi; p; p=p->link) {
			for (a=0; a<p->narg; a++)
				bset(&p->blk[a]->out, p->arg[a]);
			bset(k, p->to);
		}
		for (i=b->ins; i-b->ins < b->nins; i++) {
			bset(k, i->to);
			bset(u, i->arg[0]);
			bset(u, i->arg[1]);
		}
		bset(u, b->jmp.arg);
	}
Again:
	chg = 0;
	for (n=f->nblk-1; n>=0; n--) {
		b = f->rpo[n];
		bt = b->out;
		if (b->s1)
			for (z=0; z<BITS; z++)
				b->out.t[z] |= b->s1->in.t[z];
		if (b->s2)
			for (z=0; z<BITS; z++)
				b->out.t[z] |= b->s2->in.t[z];
		chg |= memcmp(&b->out, &bt, sizeof(Bits)) != 0;
		k = &kill[n];
		u = &use[n];
		for (z=0; z<BITS; z++)
			b->in.t[z] = (b->out.t[z]|u->t[z]) & ~k->t[z];
	}
	if (chg)
		goto Again;
	free(kill);
	free(use);
}
