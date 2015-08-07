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

static int
islong(Ref r, Fn *fn)
{
	return rtype(r) == RTmp && fn->tmp[r.val].type == TLong;
}

static void
selcmp(Ref arg[2], Fn *fn)
{
	Ref r;
	int t;

	t = -1;
	if (rtype(arg[0]) == RCon) {
		r = arg[1];
		arg[1] = arg[0];
		arg[0] = r;
		if (rtype(r) == RCon) {
			/* todo, use the constant
			 * size to dimension the
			 * constant */
			t = newtmp(TWord, fn);
			arg[0] = TMP(t);
		}
	}
	if (islong(arg[0], fn) || islong(arg[1], fn))
		emit(OXCmpl, R, arg[1], arg[0]);
	else
		emit(OXCmpw, R, arg[1], arg[0]);
	if (t != -1)
		emit(OCopy, TMP(t), r, R);
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
	case ONop:
		break;
	default:
		if (OCmp <= i.op && i.op <= OCmp1) {
			c = i.op - OCmp;
			if (rtype(i.arg[0]) == RCon)
				c = COP(c);
			emit(OXSet+c, i.to, R, R);
			selcmp(i.arg, fn);
			break;
		}
		diag("isel: non-exhaustive implementation");
	}
}

static Ins *
flagi(Ins *i0, Ins *i)
{
	while (i>i0)
		switch ((--i)->op) {
		default:
			if (OCmp <= i->op && i->op <= OCmp1)
				return i;
			return 0;
		case OAdd:  /* <arch> flag-setting */
		case OSub:
			return i;
		case OCopy: /* <arch> flag-transparent */
		case OStore:
		case OLoad:;
		}
	return 0;
}

static void
seljmp(Blk *b, Fn *fn)
{
	Ref r;
	int c;
	Ins *fi;

	if (b->jmp.type != JJnz)
		return;
	r = b->jmp.arg;
	b->jmp.arg = R;
	assert(!req(r, R));
	if (rtype(r) == RCon) {
		b->jmp.type = JJmp;
		if (req(r, CON_Z))
			b->s1 = b->s2;
		b->s2 = 0;
		return;
	}
	fi = flagi(b->ins, &b->ins[b->nins]);
	if (fi && req(fi->to, r)) {
		if (OCmp <= fi->op && fi->op <= OCmp1) {
			c = fi->op - OCmp;
			if (rtype(fi->arg[0]) == RCon)
				c = COP(c);
			b->jmp.type = JXJc + c;
			if (fn->tmp[r.val].nuse == 1) {
				assert(fn->tmp[r.val].ndef==1);
				selcmp(fi->arg, fn);
				*fi = (Ins){ONop, R, {R, R}};
			}
		} else
			b->jmp.type = JXJc + Cne;
	} else {
		selcmp((Ref[2]){r, CON_Z}, fn);
		b->jmp.type = JXJc + Cne;
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
		seljmp(b, fn);
		for (i=&b->ins[b->nins]; i>b->ins;) {
			sel(*--i, fn);
		}
		nins = &insb[NIns] - curi;
		free(b->ins);
		b->ins = alloc(nins * sizeof b->ins[0]);
		memcpy(b->ins, curi, nins * sizeof b->ins[0]);
		b->nins = nins;
	}
}
