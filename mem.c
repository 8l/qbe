#include "all.h"

static int
loadsz(Ins *l)
{
	switch (l->op) {
	case Oloadsb: case Oloadub: return 1;
	case Oloadsh: case Oloaduh: return 2;
	case Oloadsw: case Oloaduw: return 4;
	case Oload: return KWIDE(l->cls) ? 8 : 4;
	}
	die("unreachable");
}

static int
storesz(Ins *s)
{
	switch (s->op) {
	case Ostoreb: return 1;
	case Ostoreh: return 2;
	case Ostorew: case Ostores: return 4;
	case Ostorel: case Ostored: return 8;
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
		if (Oalloc > i->op || i->op > Oalloc1)
			continue;
		/* specific to NAlign == 3 */
		assert(rtype(i->to) == RTmp);
		t = &fn->tmp[i->to.val];
		if (t->ndef != 1)
			goto Skip;
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
		*i = (Ins){.op = Onop};
		t->ndef--;
		ue = &t->use[t->nuse];
		for (u=t->use; u!=ue; u++) {
			l = u->u.ins;
			if (isstore(l->op)) {
				l->cls = k;
				l->op = Ocopy;
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
				case Oload:
				case Oloadsw:
				case Oloaduw:
					if (KBASE(k) != KBASE(l->cls))
						l->op = Ocast;
					else
						l->op = Ocopy;
					break;
				default:
					l->op = Oextsb + (l->op - Oloadsb);
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
