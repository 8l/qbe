#include "lisc.h"

void
liveon(BSet *v, Blk *b, Blk *s)
{
	Phi *p;
	uint a;

	bscopy(v, s->in);
	for (p=s->phi; p; p=p->link) {
		bsclr(v, p->to.val);
		for (a=0; a<p->narg; a++)
			if (p->blk[a] == b)
			if (rtype(p->arg[a]) == RTmp)
				bsset(v, p->arg[a].val);
	}
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
			tmp[t1].phi = t1;
			t = t1;
		} else {
			tmp[t2].phi = t2;
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
	bsset(b->gen, r.val);
	phifix(r.val, phi, tmp);
	if (!bshas(b->in, r.val)) {
		nlv[KBASE(tmp[r.val].cls)]++;
		bsset(b->in, r.val);
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
	int k, t, m[2], n, chg, nlv[2];
	short *phi;
	BSet u[1], v[1];
	Mem *ma;

	bsinit(u, f->ntmp); /* todo, free those */
	bsinit(v, f->ntmp);
	phi = emalloc(f->ntmp * sizeof phi[0]);
	for (b=f->start; b; b=b->link) {
		bsinit(b->in, f->ntmp);
		bsinit(b->out, f->ntmp);
		bsinit(b->gen, f->ntmp);
	}
	chg = 1;
Again:
	for (n=f->nblk-1; n>=0; n--) {
		b = f->rpo[n];

		bscopy(u, b->out);
		if (b->s1) {
			liveon(v, b, b->s1);
			bsunion(b->out, v);
		}
		if (b->s2) {
			liveon(v, b, b->s2);
			bsunion(b->out, v);
		}
		chg |= !bsequal(b->out, u);

		memset(phi, 0, f->ntmp * sizeof phi[0]);
		memset(nlv, 0, sizeof nlv);
		bscopy(b->in, b->out);
		for (t=0; t<f->ntmp; t++)
			if (bshas(b->in, t)) {
				phifix(t, phi, f->tmp);
				nlv[KBASE(f->tmp[t].cls)]++;
			}
		bset(b->jmp.arg, b, nlv, phi, f->tmp);
		for (k=0; k<2; k++)
			b->nlive[k] = nlv[k];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			if ((--i)->op == OCall && rtype(i->arg[1]) == RACall) {
				b->in->t[0] &= ~calldef(*i, m);
				for (k=0; k<2; k++)
					nlv[k] -= m[k];
				if (nlv[0] + NISave > b->nlive[0])
					b->nlive[0] = nlv[0] + NISave;
				if (nlv[1] + NFSave > b->nlive[1])
					b->nlive[1] = nlv[1] + NFSave;
				b->in->t[0] |= calluse(*i, m);
				for (k=0; k<2; k++)
					nlv[k] += m[k];
			}
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				t = i->to.val;
				if (bshas(b->in, i->to.val))
					nlv[KBASE(f->tmp[t].cls)]--;
				bsset(b->gen, t);
				bsclr(b->in, t);
				phi[phitmp(t, f->tmp)] = 0;
			}
			for (k=0; k<2; k++)
				switch (rtype(i->arg[k])) {
				case RAMem:
					ma = &f->mem[i->arg[k].val & AMask];
					bset(ma->base, b, nlv, phi, f->tmp);
					bset(ma->index, b, nlv, phi, f->tmp);
					break;
				default:
					bset(i->arg[k], b, nlv, phi, f->tmp);
					break;
				}
			for (k=0; k<2; k++)
				if (nlv[k] > b->nlive[k])
					b->nlive[k] = nlv[k];
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
			dumpts(b->in, f->tmp, stderr);
			fprintf(stderr, "\t          out:  ");
			dumpts(b->out, f->tmp, stderr);
			fprintf(stderr, "\t          gen:  ");
			dumpts(b->gen, f->tmp, stderr);
			fprintf(stderr, "\t          live: ");
			fprintf(stderr, "%d %d\n", b->nlive[0], b->nlive[1]);
		}
	}
}
