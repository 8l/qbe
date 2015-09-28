#include "lisc.h"

Bits
liveon(Blk *b, Blk *s)
{
	Bits v;
	Phi *p;
	uint a;

	v = s->in;
	for (p=s->phi; p; p=p->link) {
		BCLR(v, p->to.val);
		for (a=0; a<p->narg; a++)
			if (p->blk[a] == b)
			if (rtype(p->arg[a]) == RTmp)
				BSET(v, p->arg[a].val);
	}
	return v;
}

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
	int t, z, m, n, chg, nlv;
	Bits u, v;
	ulong regs;

	assert(f->ntmp <= NBit*BITS);
	for (b=f->start; b; b=b->link) {
		b->in = (Bits){{0}};
		b->out = (Bits){{0}};
		b->gen = (Bits){{0}};
	}
	for (t=Tmp0; t<f->ntmp; t++)
		f->tmp[t].intr = 0;
	chg = 1;
Again:
	for (n=f->nblk-1; n>=0; n--) {
		b = f->rpo[n];

		u = b->out;
		if (b->s1) {
			v = liveon(b, b->s1);
			for (z=0; z<BITS; z++)
				b->out.t[z] |= v.t[z];
		}
		if (b->s2) {
			v = liveon(b, b->s2);
			for (z=0; z<BITS; z++)
				b->out.t[z] |= v.t[z];
		}
		chg |= memcmp(&b->out, &u, sizeof(Bits));

		b->in = b->out;
		nlv = bcnt(&b->in);
		bset(b->jmp.arg, b, &nlv);
		b->nlive = nlv;
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			if ((--i)->op == OCall) {
				b->in.t[0] &= ~calldef(*i, &m);
				nlv -= m;
				if (nlv + NRSave > b->nlive)
					b->nlive = nlv + NRSave;
				b->in.t[0] |= calluse(*i, &m);
				nlv += m;
			}
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				nlv -= BGET(b->in, i->to.val);
				BCLR(b->in, i->to.val);
			}
			bset(i->arg[0], b, &nlv);
			bset(i->arg[1], b, &nlv);
			if (nlv > b->nlive)
				b->nlive = nlv;
			if ((regs = b->in.t[0] & (BIT(Tmp0) - 1)))
				for (t=Tmp0; t<f->ntmp; t++)
					if (BGET(b->in, t))
						f->tmp[t].intr |= regs;
		}
	}
	if (chg) {
		chg = 0;
		goto Again;
	}
}
