#include "lisc.h"

static void
bset(Ref r, Blk *b, int *nlv)
{
	if (rtype(r) != RTmp)
		return;
	BSET(b->gen, r.val);
	if (!BGET(b->in, r.val)) {
		++*nlv;
		BSET(b->in, r.val);
	}
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
	int z, n, chg, nlv;
	uint a;
	Bits tb;

	assert(f->ntmp <= NBit*BITS);
	for (b=f->start; b; b=b->link) {
		b->in = (Bits){{0}};
		b->out = (Bits){{0}};
		b->gen = (Bits){{0}};
	}
	chg = 1;
Again:
	for (n=f->nblk-1; n>=0; n--) {
		b = f->rpo[n];

		tb = b->out;
		if (b->s1)
			for (z=0; z<BITS; z++)
				b->out.t[z] |= b->s1->in.t[z];
		if (b->s2)
			for (z=0; z<BITS; z++)
				b->out.t[z] |= b->s2->in.t[z];
		chg |= memcmp(&b->out, &tb, sizeof(Bits));

		b->in = b->out;
		nlv = bcnt(&b->in);
		bset(b->jmp.arg, b, &nlv);
		b->nlive = nlv;
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			i--;
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				nlv -= BGET(b->in, i->to.val);
				BCLR(b->in, i->to.val);
			}
			bset(i->arg[0], b, &nlv);
			bset(i->arg[1], b, &nlv);
			if (nlv > b->nlive)
				b->nlive = nlv;
		}

		for (p=b->phi; p; p=p->link) {
			BCLR(b->in, p->to.val);
			for (a=0; a<p->narg; a++)
				if (rtype(p->arg[a]) == RTmp)
					BSET(p->blk[a]->out, p->arg[a].val);
		}
	}
	if (chg) {
		chg = 0;
		goto Again;
	}
}
