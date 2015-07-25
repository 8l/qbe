#include "lisc.h"

/* For x86_64, we have to:
 *
 * - check that constants are used only in
 *   places allowed by the machine
 *
 * - explicit machine register contraints
 *   on instructions like division.
 *
 * - lower calls (future, I have to think
 *   about their representation and the
 *   way I deal with structs/unions in the
 *   ABI)
 */

extern Ins insb[NIns], *curi; /* shared work buffer */

static void
emit(short op, Ref to, Ref arg0, Ref arg1)
{
	if (curi == insb)
		diag("isel: too many instructions");
	*--curi = (Ins){op, to, {arg0, arg1}};
}

static void
sel(Ins *i, Fn *fn)
{
	int t;
	Ref r0, r1;

	switch (i->op) {
	case ODiv:
		r0 = SYM(RAX);
		r1 = SYM(RDX);
	if (0) {
	case ORem:
		r0 = SYM(RDX);
		r1 = SYM(RAX);
	}
		emit(OCopy, i->to, r0, R);
		emit(OCopy, R, r1, R);
		if (rtype(i->arg[1]) == RConst) {
			/* immediates not allowed for
			 * divisions in x86
			 */
			t = fn->ntmp++;
			r0 = SYM(t);
		} else
			r0 = i->arg[1];
		emit(OIADiv, R, r0, R);
		emit(OIACltd, SYM(RDX), R, R);
		emit(OCopy, SYM(RAX), i->arg[0], R);
		if (rtype(i->arg[1]) == RConst)
			emit(OCopy, r0, i->arg[1], R);
		break;
	case OAdd:
	case OSub:
	case OCopy:
		emit(i->op, i->to, i->arg[0], i->arg[1]);
		break;
	default:
		diag("isel: non-exhaustive implementation");
	}
}

/* instruction selection
 */
void
isel(Fn *fn)
{
	Blk *b;
	Ins *i;
	int t0, t;
	uint nins;

	t0 = fn->ntmp;
	for (b=fn->start; b; b=b->link) {
		curi = &insb[NIns];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			sel(--i, fn);
		}
		nins = &insb[NIns] - curi;
		free(b->ins);
		b->ins = alloc(nins * sizeof b->ins[0]);
		memcpy(b->ins, curi, nins * sizeof b->ins[0]);
		b->nins = nins;
	}
	if (fn->ntmp == t0)
		return;
	fn->sym = realloc(fn->sym, fn->ntmp * sizeof(Sym));
	if (!fn->sym)
		diag("isel: out of memory");
	for (t=t0; t<fn->ntmp; t++) {
		fn->sym[t].type = STmp;
		sprintf(fn->sym[t].name, "isel%d", t-t0);
	}
}
