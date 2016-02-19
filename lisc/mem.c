#include "lisc.h"

/* Memory optimization:
 *
 * - replace alloced slots used only in
 *   load/store operations
 *   Assumption: all the accesses have the
 *   same size (this could be wrong...)
 */

/* require use, maintains use counts */
void
memopt(Fn *fn)
{
	Blk *b;
	Ins *i, *l;
	Tmp *t;
	Use *u, *ue;
	int a;

	b = fn->start;
	for (i=b->ins; i-b->ins < b->nins; i++) {
		if (OAlloc > i->op || i->op > OAlloc1)
			continue;
		assert(NAlign == 3);
		assert(rtype(i->to) == RTmp);
		t = &fn->tmp[i->to.val];
		for (u=t->use; u != &t->use[t->nuse]; u++) {
			if (u->type != UIns)
				goto NextIns;
			l = u->u.ins;
			if (!isload(l->op)
			&& (!isstore(l->op) || req(i->to, l->arg[0])))
				goto NextIns;
		}
		/* get rid of the alloc and replace uses */
		*i = (Ins){.op = ONop};
		t->ndef--;
		ue = &t->use[t->nuse];
		for (u=t->use; u!=ue; u++) {
			l = u->u.ins;
			if (isstore(l->op)) {
				if (l->op == OStores)
					l->cls = Kd;
				else if (l->op == OStored)
					l->cls = Kd;
				else if (l->op == OStorel)
					l->cls = Kl;
				else
					l->cls = Kw;
				l->op = OCopy;
				l->to = l->arg[1];
				l->arg[1] = R;
				t->nuse--;
				t->ndef++;
			} else
				/* try to turn loads into copies so we
				 * can eliminate them later */
				switch(l->op) {
				case OLoad:
					l->op = OCopy;
					break;
				case OLoadsw:
				case OLoaduw:
					l->cls = Kw;
					l->op = OCopy;
					break;
				default:
					/* keep l->cls */
					a = l->op - OLoadsw;
					l->op = OExtsw + a;
					break;
				}
		}
	NextIns:;
	}
	if (debug['M']) {
		fprintf(stderr, "\n> After memory optimization:\n");
		printfn(fn, stderr);
	}
}
