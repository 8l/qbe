#include "all.h"

static void
getalias(Alias *a, Ref r, Fn *fn)
{
	Con *c;

	switch (rtype(r)) {
	default:
		die("unreachable");
	case RTmp:
		*a = fn->tmp[r.val].alias;
		if (astack(a->type))
			a->type = a->slot->type;
		assert(a->type != ABot);
		break;
	case RCon:
		c = &fn->con[r.val];
		if (c->type == CAddr) {
			a->type = ASym;
			a->label = c->label;
		} else
			a->type = ACon;
		a->offset = c->bits.i;
		a->slot = 0;
		break;
	}
}

int
alias(Ref p, int sp, Ref q, int sq, int *delta, Fn *fn)
{
	Alias ap, aq;
	int ovlap;

	getalias(&ap, p, fn);
	getalias(&aq, q, fn);
	*delta = ap.offset - aq.offset;
	ovlap = ap.offset < aq.offset + sq && aq.offset < ap.offset + sp;

	if (astack(ap.type) && astack(aq.type)) {
		/* if both are offsets of the same
		 * stack slot, they alias iif they
		 * overlap */
		if (req(ap.base, aq.base) && ovlap)
			return MustAlias;
		return NoAlias;
	}

	if (ap.type == ASym && aq.type == ASym) {
		/* they conservatively alias if the
		 * symbols are different, or they
		 * alias for sure if they overlap */
		if (ap.label != aq.label)
			return MayAlias;
		if (ovlap)
			return MustAlias;
		return NoAlias;
	}

	if ((ap.type == ACon && aq.type == ACon)
	|| (ap.type == aq.type && req(ap.base, aq.base))) {
		assert(ap.type == ACon || ap.type == AUnk);
		/* if they have the same base, we
		 * can rely on the offsets only */
		if (ovlap)
			return MustAlias;
		return NoAlias;
	}

	/* if one of the two is unknown
	 * there may be aliasing unless
	 * the other is provably local */
	if (ap.type == AUnk && aq.type != ALoc)
		return MayAlias;
	if (aq.type == AUnk && ap.type != ALoc)
		return MayAlias;

	return NoAlias;
}

int
escapes(Ref r, Fn *fn)
{
	Alias *a;

	if (rtype(r) != RTmp)
		return 1;
	a = &fn->tmp[r.val].alias;
	return !astack(a->type) || a->slot->type == AEsc;
}

static void
esc(Ref r, Fn *fn)
{
	Alias *a;

	assert(rtype(r) <= RType);
	if (rtype(r) == RTmp) {
		a = &fn->tmp[r.val].alias;
		if (astack(a->type))
			a->slot->type = AEsc;
	}
}

void
fillalias(Fn *fn)
{
	uint n, m;
	Blk *b;
	Phi *p;
	Ins *i;
	Alias *a, a0, a1;

	for (n=0; n<fn->nblk; ++n) {
		b = fn->rpo[n];
		for (p=b->phi; p; p=p->link) {
			for (m=0; m<p->narg; m++)
				esc(p->arg[m], fn);
			assert(rtype(p->to) == RTmp);
			a = &fn->tmp[p->to.val].alias;
			assert(a->type == ABot);
			a->type = AUnk;
			a->base = p->to;
			a->offset = 0;
			a->slot = 0;
		}
		for (i=b->ins; i<&b->ins[b->nins]; ++i) {
			a = 0;
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				a = &fn->tmp[i->to.val].alias;
				assert(a->type == ABot);
				if (Oalloc <= i->op && i->op <= Oalloc1) {
					a->type = ALoc;
					a->slot = a;
				} else {
					a->type = AUnk;
					a->slot = 0;
				}
				a->base = i->to;
				a->offset = 0;
			}
			if (i->op == Ocopy) {
				assert(a);
				getalias(a, i->arg[0], fn);
			}
			if (i->op == Oadd) {
				getalias(&a0, i->arg[0], fn);
				getalias(&a1, i->arg[1], fn);
				if (a0.type == ACon) {
					*a = a1;
					a->offset += a0.offset;
				}
				else if (a1.type == ACon) {
					*a = a0;
					a->offset += a1.offset;
				}
			}
			if (req(i->to, R) || a->type == AUnk) {
				if (!isload(i->op))
					esc(i->arg[0], fn);
				if (!isstore(i->op))
					esc(i->arg[1], fn);
			}
		}
		esc(b->jmp.arg, fn);
	}
}
