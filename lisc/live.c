#include "lisc.h"

static inline int
issym(Ref r)
{
	return !req(r, R) && r.type == RSym;
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
	kill = alloc(f->ntmp * sizeof kill[0]);
	use = alloc(f->ntmp * sizeof use[0]);
	for (b=f->start; b; b=b->link) {
		memset(&b->in, 0, sizeof(Bits));
		memset(&b->out, 0, sizeof(Bits));
	}
	for (b=f->start; b; b=b->link) {
		k = &kill[b->id];
		u = &use[b->id];
		for (p=b->phi; p; p=p->link) {
			for (a=0; a<p->narg; a++)
				if (issym(p->arg[a]))
					BSET(p->blk[a]->out, p->arg[a].val);
			BSET(*k, p->to.val);
		}
		for (i=b->ins; i-b->ins < b->nins; i++) {
			if (issym(i->to))
				BSET(*k, i->to.val);
			if (issym(i->arg[0]))
				BSET(*u, i->arg[0].val);
			if (issym(i->arg[1]))
				BSET(*u, i->arg[1].val);
		}
		if (issym(b->jmp.arg))
			BSET(*u, b->jmp.arg.val);
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
