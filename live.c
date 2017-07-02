#include "all.h"

void
liveon(BSet *v, Blk *b, Blk *s)
{
	Phi *p;
	uint a;

	bscopy(v, s->in);
	for (p=s->phi; p; p=p->link)
		if (rtype(p->to) == RTmp)
			bsclr(v, p->to.val);
	for (p=s->phi; p; p=p->link)
		for (a=0; a<p->narg; a++)
			if (p->blk[a] == b)
			if (rtype(p->arg[a]) == RTmp) {
				bsset(v, p->arg[a].val);
				bsset(b->gen, p->arg[a].val);
			}
}

static void
bset(Ref r, Blk *b, int *nlv, Tmp *tmp)
{

	if (rtype(r) != RTmp)
		return;
	bsset(b->gen, r.val);
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
	BSet u[1], v[1];
	Mem *ma;

	bsinit(u, f->ntmp);
	bsinit(v, f->ntmp);
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

		memset(nlv, 0, sizeof nlv);
		b->out->t[0] |= T.rglob;
		bscopy(b->in, b->out);
		for (t=0; bsiter(b->in, &t); t++)
			nlv[KBASE(f->tmp[t].cls)]++;
		if (rtype(b->jmp.arg) == RCall) {
			assert((int)bscount(b->in) == T.nrglob &&
				nlv[0] == T.nrglob &&
				nlv[1] == 0);
			b->in->t[0] |= T.retregs(b->jmp.arg, nlv);
		} else
			bset(b->jmp.arg, b, nlv, f->tmp);
		for (k=0; k<2; k++)
			b->nlive[k] = nlv[k];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			if ((--i)->op == Ocall && rtype(i->arg[1]) == RCall) {
				b->in->t[0] &= ~T.retregs(i->arg[1], m);
				for (k=0; k<2; k++) {
					nlv[k] -= m[k];
					/* caller-save registers are used
					 * by the callee, in that sense,
					 * right in the middle of the call,
					 * they are live: */
					nlv[k] += T.nrsave[k];
					if (nlv[k] > b->nlive[k])
						b->nlive[k] = nlv[k];
				}
				b->in->t[0] |= T.argregs(i->arg[1], m);
				for (k=0; k<2; k++) {
					nlv[k] -= T.nrsave[k];
					nlv[k] += m[k];
				}
			}
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				t = i->to.val;
				if (bshas(b->in, i->to.val))
					nlv[KBASE(f->tmp[t].cls)]--;
				bsset(b->gen, t);
				bsclr(b->in, t);
			}
			for (k=0; k<2; k++)
				switch (rtype(i->arg[k])) {
				case RMem:
					ma = &f->mem[i->arg[k].val];
					bset(ma->base, b, nlv, f->tmp);
					bset(ma->index, b, nlv, f->tmp);
					break;
				default:
					bset(i->arg[k], b, nlv, f->tmp);
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
