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

static int
newtmp(int type, Fn *fn)
{
	static int n;
	int t;

	t = fn->ntmp++;
	fn->tmp = realloc(fn->tmp, fn->ntmp * sizeof fn->tmp[0]);
	if (!fn->tmp)
		diag("isel: out of memory");
	fn->tmp[t] = (Tmp){.type = type};
	sprintf(fn->tmp[t].name, "isel%d", ++n);
	return t;
}

static void
sel(Ins i, Fn *fn)
{
	Ref r0, r1, ra, rd;
	int t, ty, c;

	switch (i.op) {
	case ODiv:
	case ORem:
		ty = fn->tmp[i.to.val].type;
		switch (ty) {
		default:
			diag("isel: invalid division");
		case TWord:
			ra = REG(EAX);
			rd = REG(EDX);
			break;
		case TLong:
			ra = REG(RAX);
			rd = REG(RDX);
			break;
		}
		r0 = i.op == ODiv ? ra : rd;
		r1 = i.op == ODiv ? rd : ra;
		emit(OCopy, i.to, r0, R);
		emit(OCopy, R, r1, R);
		if (rtype(i.arg[1]) == RCon) {
			/* immediates not allowed for
			 * divisions in x86
			 */
			t = newtmp(ty, fn);
			r0 = TMP(t);
		} else
			r0 = i.arg[1];
		emit(OXDiv, R, r0, R);
		emit(OSign, rd, ra, R);
		emit(OCopy, ra, i.arg[0], R);
		if (rtype(i.arg[1]) == RCon)
			emit(OCopy, r0, i.arg[1], R);
		break;
	case OAdd:
	case OSub:
	case OCopy:
		emit(i.op, i.to, i.arg[0], i.arg[1]);
		break;
	default:
		if (OCmp <= i.op && i.op <= OCmp1) {
			r0 = i.arg[0];
			c = i.op - OCmp;
			if (rtype(i.arg[0]) == RCon) {
				if (rtype(i.arg[1]) == RCon) {
					/* todo, use the constant
					 * size to dimension the
					 * constant */
					t = newtmp(TWord, fn);
					r0 = TMP(t);
				} else {
					r0 = i.arg[1];
					i.arg[1] = i.arg[0];
					c = CNEG(c);
				}
			}
			emit(OXSet+c, i.to, R, R);
			emit(OXCmp, R, i.arg[1], r0);
			if (!req(r0, i.arg[0]))
				emit(OCopy, r0, i.arg[0], R);
			break;
		}
		diag("isel: non-exhaustive implementation");
	}
}

/* instruction selection
 * requires use counts (as given by parsing)
 */
void
isel(Fn *fn)
{
	Blk *b;
	Ins *i;
	uint nins;

	for (b=fn->start; b; b=b->link) {
		curi = &insb[NIns];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			sel(*--i, fn);
		}
		nins = &insb[NIns] - curi;
		free(b->ins);
		b->ins = alloc(nins * sizeof b->ins[0]);
		memcpy(b->ins, curi, nins * sizeof b->ins[0]);
		b->nins = nins;
	}
}
