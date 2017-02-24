#include "all.h"

static void
elimext(Ins *i, int ext, Fn *fn)
{
	Tmp *t;
	Use *u;

	assert(rtype(i->to) == RTmp);
	t = &fn->tmp[i->to.val];
	for (u=t->use; u<&t->use[t->nuse]; u++)
		if (u->type == UIns
		&& u->u.ins->op == ext
		&& (u->u.ins->cls == i->cls || i->cls == Kl)) {
			u->u.ins->op = Ocopy;
			elimext(u->u.ins, ext, fn);
		}
}

/* requires & preserves uses */
void
simpl(Fn *fn)
{
	Blk *b;
	Ins *i;
	int ext;

	for (b=fn->start; b; b=b->link)
		for (i=b->ins; i<&b->ins[b->nins]; i++)
			switch (i->op) {
			case Oloadsb:
			case Oloadub:
			case Oloadsh:
			case Oloaduh:
				ext = Oextsb + (i->op - Oloadsb);
				goto Elimext;
			case Oextsb:
			case Oextub:
			case Oextsh:
			case Oextuh:
				ext = i->op;
			Elimext:
				elimext(i, ext, fn);
				break;
			}
}
