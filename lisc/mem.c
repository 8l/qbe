#include "lisc.h"

/* Memory optimization:
 *
 * - replace alloced slots used only in
 *   load/store operations
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
			if (l->op < OStorel || l->op > OStoreb)
			if (l->op < OLoad || l->op > OLoad1)
				goto NextIns;
		}
		/* get rid of the alloc and replace uses */
		*i = (Ins){.op = ONop};
		t->ndef--;
		ue = &t->use[t->nuse];
		for (u=t->use; u != ue; u++) {
			l = u->u.ins;
			if (OStorel <= l->op && l->op <= OStoreb) {
				l->wide = (l->op == OStorel);
				l->op = OCopy;
				l->to = l->arg[1];
				l->arg[1] = R;
				t->nuse--;
				t->ndef++;
			} else
				switch(l->op) {
				case OLoad+Tl:
					l->wide = 1;
					l->op = OCopy;
					break;
				case OLoad+Tsw:
				case OLoad+Tuw:
					l->wide = 0;
					l->op = OCopy;
					break;
				default:
					/* keep l->wide */
					a = l->op - OLoad;
					l->op = OExt + a;
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
