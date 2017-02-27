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
update(Ref r, Ref rcp, Ref *cp, RList ***pw)
{
	RList *l;

	if (!req(cp[r.val], rcp)) {
		cp[r.val] = rcp;
		l = emalloc(sizeof *l);
		l->t = r.val;
		l->l = 0;
		**pw = l;
		*pw = &l->l;
	}
}

static void
visitphi(Phi *p, Ref *cp, RList ***pw)
{
	uint a;
	Ref r, r1;

	r = R;
	for (a=0; a<p->narg; a++) {
		r1 = copyof(p->arg[a], cp);
		if (req(r1, R) || req(r1, p->to))
			continue;
		if (req(r, R) || req(r, r1))
			r = r1;
		else {
			r = p->to;
			break;
		}
	}
	update(p->to, r, cp, pw);
}

static int
iscopy(Ins *i, Ref r, Fn *fn)
{
	static bits extcpy[] = {
		[WFull] = 0,
		[Wsb] = BIT(Wsb) | BIT(Wsh) | BIT(Wsw),
		[Wub] = BIT(Wub) | BIT(Wuh) | BIT(Wuw),
		[Wsh] = BIT(Wsh) | BIT(Wsw),
		[Wuh] = BIT(Wuh) | BIT(Wuw),
		[Wsw] = BIT(Wsw),
		[Wuw] = BIT(Wuw),
	};
	bits b;
	Tmp *t;

	if (i->op == Ocopy)
		return 1;
	if (!isext(i->op) || rtype(r) != RTmp)
		return 0;
	if (i->op == Oextsw || i->op == Oextuw)
	if (i->cls == Kw)
		return 1;

	t = &fn->tmp[r.val];
	assert(KBASE(t->cls) == 0);
	if (i->cls == Kl && t->cls == Kw)
		return 0;
	b = extcpy[t->width];
	return (BIT(Wsb + (i->op-Oextsb)) & b) != 0;
}

static void
visitins(Ins *i, Ref *cp, RList ***pw, Fn *fn)
{
	Ref r;

	r = copyof(i->arg[0], cp);
	if (iscopy(i, r, fn)) {
		update(i->to, r, cp, pw);
	} else if (!req(i->to, R)) {
		assert(rtype(i->to) == RTmp);
		update(i->to, i->to, cp, pw);
	}
}

static void
subst(Ref *r, Ref *cp)
{
	assert((rtype(*r) != RTmp || !req(copyof(*r, cp), R)) && "ssa invariant broken");
	*r = copyof(*r, cp);
}

void
copy(Fn *fn)
{
	Blk *b;
	Ref *cp, r;
	RList *w, *w1, **pw;
	Use *u, *u1;
	Ins *i;
	Phi *p, **pp;
	uint a;
	int t;

	w = 0;
	pw = &w;
	cp = emalloc(fn->ntmp * sizeof cp[0]);
	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link)
			visitphi(p, cp, &pw);
		for (i=b->ins; i-b->ins < b->nins; i++)
			visitins(i, cp, &pw, fn);
	}
	while ((w1=w)) {
		t = w->t;
		u = fn->tmp[t].use;
		u1 = u + fn->tmp[t].nuse;
		for (; u<u1; u++)
			switch (u->type) {
			case UPhi:
				visitphi(u->u.phi, cp, &pw);
				break;
			case UIns:
				visitins(u->u.ins, cp, &pw, fn);
				break;
			case UJmp:
				break;
			default:
				die("invalid use %d", u->type);
			}
		w = w->l;
		free(w1);
	}
	for (b=fn->start; b; b=b->link) {
		for (pp=&b->phi; (p=*pp);) {
			r = cp[p->to.val];
			if (!req(r, p->to)) {
				*pp = p->link;
				continue;
			}
			for (a=0; a<p->narg; a++)
				subst(&p->arg[a], cp);
			pp=&p->link;
		}
		for (i=b->ins; i-b->ins < b->nins; i++) {
			r = copyof(i->to, cp);
			if (!req(r, i->to)) {
				*i = (Ins){.op = Onop};
				continue;
			}
			for (a=0; a<2; a++)
				subst(&i->arg[a], cp);
		}
		subst(&b->jmp.arg, cp);
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
