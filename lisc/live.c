#include "lisc.h"

static void
bset(Ref r, Blk *b, Bits *rb, int *nlv)
{
	Bits *bs;

	switch (rtype(r)) {
	case RSym:
		bs = &b->in;
		BSET(b->gen, r.val);
		break;
	case RReg:
		bs = rb;
		break;
	default:
		diag("live: unhandled reference");
		return;
	}
	if (!BGET(*bs, r.val)) {
		++*nlv;
		BSET(*bs, r.val);
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
	Bits tb, rb;

	assert(f->nsym <= NBit*BITS);
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
		rb = (Bits){{0}};
		nlv = bcnt(&b->in);
		bset(b->jmp.arg, b, &rb, &nlv);
		b->nlive = nlv;
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			i--;
			switch (rtype(i->to)) {
			case RSym:
				nlv -= BGET(b->in, i->to.val);
				BCLR(b->in, i->to.val);
				break;
			case RReg:
				nlv -= BGET(rb, i->to.val);
				BCLR(rb, i->to.val);
			default:
				diag("live: unhandled destination");
			}
			bset(i->arg[0], b, &rb, &nlv);
			bset(i->arg[1], b, &rb, &nlv);
			if (nlv > b->nlive)
				b->nlive = nlv;
		}

		for (p=b->phi; p; p=p->link) {
			BCLR(b->in, p->to.val);
			for (a=0; a<p->narg; a++)
				if (rtype(p->arg[a]) == RSym)
					BSET(p->blk[a]->out, p->arg[a].val);
		}
	}
	if (chg) {
		chg = 0;
		goto Again;
	}
}
