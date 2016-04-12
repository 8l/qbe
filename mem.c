#include "all.h"

static int
loadsz(Ins *l)
{
	switch (l->op) {
	case OLoadsb: case OLoadub: return 1;
	case OLoadsh: case OLoaduh: return 2;
	case OLoadsw: case OLoaduw: return 4;
	case OLoad: return KWIDE(l->cls) ? 8 : 4;
	}
	die("unreachable");
}

static int
storesz(Ins *s)
{
	switch (s->op) {
	case OStoreb: return 1;
	case OStoreh: return 2;
	case OStorew: case OStores: return 4;
	case OStorel: case OStored: return 8;
	}
	die("unreachable");
}


/* require use, maintains use counts */
void
memopt(Fn *fn)
{
	Blk *b;
	Ins *i, *l;
	Tmp *t;
	Use *u, *ue;
	int s, k;

	/* promote uniform stack slots to temporaries */
	b = fn->start;
	for (i=b->ins; i-b->ins < b->nins; i++) {
		if (OAlloc > i->op || i->op > OAlloc1)
			continue;
		/* specific to NAlign == 3 */
		assert(rtype(i->to) == RTmp);
		t = &fn->tmp[i->to.val];
		k = -1;
		s = -1;
		for (u=t->use; u != &t->use[t->nuse]; u++) {
			if (u->type != UIns)
				goto Skip;
			l = u->u.ins;
			if (isload(l->op))
			if (s == -1 || s == loadsz(l)) {
				s = loadsz(l);
				continue;
			}
			if (isstore(l->op))
			if (req(i->to, l->arg[1]) && !req(i->to, l->arg[0]))
			if (s == -1 || s == storesz(l))
			if (k == -1 || k == opdesc[l->op].argcls[0][0]) {
				s = storesz(l);
				k = opdesc[l->op].argcls[0][0];
				continue;
			}
			goto Skip;
		}
		/* get rid of the alloc and replace uses */
		*i = (Ins){.op = ONop};
		t->ndef--;
		ue = &t->use[t->nuse];
		for (u=t->use; u!=ue; u++) {
			l = u->u.ins;
			if (isstore(l->op)) {
				l->cls = k;
				l->op = OCopy;
				l->to = l->arg[1];
				l->arg[1] = R;
				t->nuse--;
				t->ndef++;
			} else {
				if (k == -1)
					err("slot %%%s is read but never stored to",
						fn->tmp[l->arg[0].val].name);
				/* try to turn loads into copies so we
				 * can eliminate them later */
				switch(l->op) {
				case OLoad:
				case OLoadsw:
				case OLoaduw:
					if (KBASE(k) != KBASE(l->cls))
						l->op = OCast;
					else
						l->op = OCopy;
					break;
				default:
					l->op = OExtsb + (l->op - OLoadsb);
					break;
				}
			}
		}
	Skip:;
	}
	if (debug['M']) {
		fprintf(stderr, "\n> After memory optimization:\n");
		printfn(fn, stderr);
	}
}
