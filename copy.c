#include "all.h"

typedef struct RList RList;
struct RList {
	int t;
	RList *l;
};

static Ref
copyof(Ref r, Ref *cp)
{
	if (rtype(r) == RTmp)
		return cp[r.val];
	else
		return r;
}

static void
update(Ref r, Ref rcp, Ref *cp, RList **w)
{
	RList *l;

	if (!req(cp[r.val], rcp)) {
		cp[r.val] = rcp;
		l = emalloc(sizeof *l);
		l->t = r.val;
		l->l = *w;
		*w = l;
	}
}

static void
visitphi(Phi *p, Ref *cp, RList **w)
{
	uint a;
	Ref r, r1;

	r = R;
	for (a=0; a<p->narg; a++) {
		r1 = copyof(p->arg[a], cp);
		if (req(r1, R))
			continue;
		if (req(r, R) || req(r, r1))
			r = r1;
		else {
			r = p->to;
			break;
		}
	}
	assert(!req(r, R));
	update(p->to, r, cp, w);
}

static void
visitins(Ins *i, Ref *cp, RList **w)
{
	Ref r;

	if (i->op == OCopy) {
		r = copyof(i->arg[0], cp);
		update(i->to, r, cp, w);
	} else if (!req(i->to, R)) {
		assert(rtype(i->to) == RTmp);
		update(i->to, i->to, cp, w);
	}
}

void
copy(Fn *fn)
{
	Blk *b;
	Ref *cp, r;
	RList *w, *w1;
	Use *u, *u1;
	Ins *i;
	Phi *p, **pp;
	uint a;
	int t;

	w = 0;
	cp = emalloc(fn->ntmp * sizeof cp[0]);
	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link)
			visitphi(p, cp, &w);
		for (i=b->ins; i-b->ins < b->nins; i++)
			visitins(i, cp, &w);
	}
	while ((w1=w)) {
		t = w->t;
		w = w->l;
		free(w1);
		u = fn->tmp[t].use;
		u1 = u + fn->tmp[t].nuse;
		for (; u<u1; u++)
			switch (u->type) {
			default:
				diag("copy: invalid use");
			case UPhi:
				visitphi(u->u.phi, cp, &w);
				break;
			case UIns:
				visitins(u->u.ins, cp, &w);
				break;
			case UJmp:
				break;
			}
	}
	for (b=fn->start; b; b=b->link) {
		for (pp=&b->phi; (p=*pp);) {
			r = cp[p->to.val];
			if (!req(r, p->to)) {
				*pp = p->link;
				continue;
			}
			for (a=0; a<p->narg; a++)
				if (rtype(p->arg[a]) == RTmp) {
					r = cp[p->arg[a].val];
					assert(!req(r, R));
					p->arg[a] = r;
				}
			pp=&p->link;
		}
		for (i=b->ins; i-b->ins < b->nins; i++) {
			r = cp[i->to.val];
			if (!req(r, i->to)) {
				*i = (Ins){.op = ONop};
				continue;
			}
			for (a=0; a<2; a++)
				if (rtype(i->arg[a]) == RTmp) {
					r = cp[i->arg[a].val];
					assert(!req(r, R));
					i->arg[a] = r;
				}
		}
		if (rtype(b->jmp.arg) == RTmp) {
			r = cp[b->jmp.arg.val];
			assert(!req(r, R));
			b->jmp.arg = r;
		}
	}
	if (debug['C']) {
		fprintf(stderr, "\n> Copy information:");
		for (t=Tmp0; t<fn->ntmp; t++) {
			if (req(cp[t], R)) {
				fprintf(stderr, "\n%10s not seen!",
					fn->tmp[t].name);
			}
			else if (!req(cp[t], TMP(t))) {
				fprintf(stderr, "\n%10s copy of ",
					fn->tmp[t].name);
				printref(cp[t], fn, stderr);
			}
		}
		fprintf(stderr, "\n\n> After copy elimination:\n");
		printfn(fn, stderr);
	}
	free(cp);
}
