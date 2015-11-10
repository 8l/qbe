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

static int
phitmp(int t, Tmp *tmp)
{
	int tp;

	tp = tmp[t].phi;
	return tp ? tp : t;
}

static void
phifix(int t1, short *phi, Tmp *tmp)
{
	int t, t2;

	/* detect temporaries arguments
	 * of the same phi node that
	 * interfere and separate them
	 */
	t = phitmp(t1, tmp);
	t2 = phi[t];
	if (t2 && t2 != t1) {
		if (t != t1) {
			tmp[t1].phi = 0;
			t = t1;
		} else {
			tmp[t2].phi = 0;
			phi[t2] = t2;
		}
	}
	phi[t] = t1;
}

static void
bset(Ref r, Blk *b, int *nlv, short *phi, Tmp *tmp)
{

	if (rtype(r) != RTmp)
		return;
	BSET(b->gen, r.val);
	phifix(r.val, phi, tmp);
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
	short *phi;
	Bits u, v;
	Mem *ma;

	assert(f->ntmp <= NBit*BITS);
	phi = emalloc(f->ntmp * sizeof phi[0]);
	for (b=f->start; b; b=b->link) {
		b->in = (Bits){{0}};
		b->out = (Bits){{0}};
		b->gen = (Bits){{0}};
	}
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

		memset(phi, 0, f->ntmp * sizeof phi[0]);
		b->in = b->out;
		nlv = bcnt(&b->in);
		for (t=0; t<f->ntmp; t++)
			if (BGET(b->in, t))
				phifix(t, phi, f->tmp);
		bset(b->jmp.arg, b, &nlv, phi, f->tmp);
		b->nlive = nlv;
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			if ((--i)->op == OCall)
			if (rtype(i->arg[1]) == RACall) {
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
				BSET(b->gen, i->to.val);
				BCLR(b->in, i->to.val);
				t = phitmp(i->to.val, f->tmp);
				phi[t] = 0;
			}
			for (m=0; m<2; m++)
				switch (rtype(i->arg[m])) {
				case RAMem:
					ma = &f->mem[i->arg[m].val & AMask];
					bset(ma->base, b, &nlv, phi, f->tmp);
					bset(ma->index, b, &nlv, phi, f->tmp);
					break;
				default:
					bset(i->arg[m], b, &nlv, phi, f->tmp);
					break;
				}
			if (nlv > b->nlive)
				b->nlive = nlv;
		}
	}
	if (chg) {
		chg = 0;
		goto Again;
	}
	free(phi);

	if (debug['L']) {
		fprintf(stderr, "\n> Liveness analysis:\n");
		for (b=f->start; b; b=b->link) {
			fprintf(stderr, "\t%-10sin:   ", b->name);
			dumpts(&b->in, f->tmp, stderr);
			fprintf(stderr, "\t          out:  ");
			dumpts(&b->out, f->tmp, stderr);
			fprintf(stderr, "\t          gen:  ");
			dumpts(&b->gen, f->tmp, stderr);
			fprintf(stderr, "\t          live: %d\n", b->nlive);
		}
	}
}
