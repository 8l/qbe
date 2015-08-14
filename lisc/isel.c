#include "lisc.h"
#include <limits.h>

/* For x86_64, do the following:
 *
 * - check that constants are used only in
 *   places allowed
 * - ensure immediates always fit in 32b
 * - explicit machine register contraints
 *   on instructions like division.
 * - implement fast locals (the streak of
 *   constant allocX in the first basic block)
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

static Ref
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
	return TMP(t);
}

static Ref
newcon(int64_t val, Fn *fn)
{
	int c;

	for (c=0; c<fn->ncon; c++)
		if (fn->con[c].type == CNum && fn->con[c].val == val)
			return CON(c);
	fn->ncon++;
	fn->con = realloc(fn->con, fn->ncon * sizeof fn->con[0]);
	if (!fn->con)
		diag("isel: out of memory");
	fn->con[c] = (Con){.type = CNum, .val = val};
	return CON(c);
}

static int
noimm(Ref r, Fn *fn)
{
	int64_t val;

	assert(rtype(r) == RCon);
	switch (fn->con[r.val].type) {
	default:
		diag("isel: invalid constant");
	case CAddr:
		/* we only support the 'small'
		 * code model of the ABI, this
		 * means that we can always
		 * address data with 32bits
		 */
		return 0;
	case CNum:
		val = fn->con[r.val].val;
		return (val < INT32_MIN || val > INT32_MAX);
	}
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
	int lng;

	if (rtype(arg[0]) == RCon) {
		r = arg[1];
		arg[1] = arg[0];
		arg[0] = r;
	}
	assert(rtype(arg[0]) != RCon);
	lng = islong(arg[0], fn) || islong(arg[1], fn);
	emit(lng ? OXCmpl : OXCmpw, R, arg[1], arg[0]);
	r = arg[1];
	if (lng && rtype(r) == RCon && noimm(r, fn)) {
		curi->arg[0] = newtmp(TLong, fn);
		emit(OCopy, curi->arg[0], r, R);
	}
}

static void
sel(Ins i, Fn *fn)
{
	Ref r0, r1, ra, rd;
	int n, ty, c, s;
	int64_t val;
	struct {
		Ref r;
		int s;
	} cpy[2];

	for (n=0; n<2; n++) {
		r0 = i.arg[n];
		cpy[n].s = 0;
		if (rtype(r0) == RTmp)
		if ((s = fn->tmp[r0.val].spill)) {
			r0 = newtmp(TLong, fn);
			i.arg[n] = r0;
			cpy[n].r = r0;
			cpy[n].s = s;
		}
	}

	switch (i.op) {
	case ODiv:
	case ORem:
		ty = fn->tmp[i.to.val].type;
		switch (ty) {
		default:
			diag("isel: invalid division");
		case TWord:
			ra = TMP(EAX);
			rd = TMP(EDX);
			break;
		case TLong:
			ra = TMP(RAX);
			rd = TMP(RDX);
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
			r0 = newtmp(ty, fn);
		} else
			r0 = i.arg[1];
		emit(OXDiv, R, r0, R);
		emit(OSign, rd, ra, R);
		emit(OCopy, ra, i.arg[0], R);
		if (rtype(i.arg[1]) == RCon)
			emit(OCopy, r0, i.arg[1], R);
		break;
	case ONop:
		break;
	case OAdd:
	case OSub:
	case OCopy:
		if (fn->tmp[i.to.val].type == TLong)
			n = 2;
		else
			n = 0;
		goto Emit;
	case OStorel:
	case OStorew:
	case OStoreb:
	case OStores:
		if (cpy[1].s) {
			i.arg[1] = MEM(cpy[1].s);
			cpy[1].s = 0;
		}
		n = i.op == OStorel;
		goto Emit;
	case OLoad:
	case OLoadss:
	case OLoadus:
	case OLoadsb:
	case OLoadub:
		if (cpy[0].s) {
			i.arg[0] = MEM(cpy[0].s);
			cpy[0].s = 0;
		}
		n = 0;
Emit:
		emit(i.op, i.to, i.arg[0], i.arg[1]);
		while (n--) {
			/* load constants that do not fit in
			 * a 32bit signed integer into a
			 * long temporary
			 */
			r0 = i.arg[n];
			if (rtype(r0) == RCon && noimm(r0, fn)) {
				curi->arg[n] = newtmp(TLong, fn);
				emit(OCopy, curi->arg[n], r0, R);
			}
		}
		break;
	case OAlloc:
	case OAlloc+1:
	case OAlloc+2: /* == OAlloc1 */
		/* if this is not a fast alloc
		 * we need to make sure
		 * the stack remains aligned
		 * (rsp + 8 = 0) mod 16
		 */
		if (req(i.to, R))
			break;
		if (rtype(i.arg[0]) == RCon) {
			val = fn->con[i.arg[0].val].val;
			val = (val + 15)  & ~INT64_C(15);
			if (val < 0 || val > INT32_MAX)
				diag("isel: alloc too large");
			emit(OAlloc, i.to, newcon(val, fn), R);
		} else if (i.op < OAlloc1) {
			/* r0 = (i.arg[0] + 15) & -16 */
			r0 = newtmp(TLong, fn);
			r1 = newtmp(TLong, fn);
			emit(OAlloc, i.to, r0, R);
			emit(OAnd, r0, r1, newcon(-16, fn));
			emit(OAdd, r1, i.arg[0], newcon(15, fn));
		} else
			/* todo, support it! */
			diag("isel: unsupported alloc alignment");
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

	for (n=0; n<2; n++)
		if (cpy[n].s)
			emit(OCopy, cpy[n].r, MEM(cpy[n].s), R);
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
		case OAdd:  /* flag-setting */
		case OSub:
		case OAnd:
			return i;
		case OCopy: /* flag-transparent */
		case OStorel:
		case OStorew:
		case OStoreb:
		case OStores:
		case OLoad:
		case OLoadss:
		case OLoadus:
		case OLoadsb:
		case OLoadub:;
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

int
slot_(int sz, int al /* log2 */, Fn *fn)
{
	enum { N = sizeof fn->slot / sizeof fn->slot[0] };
	int j, k, s, l, a, ret;
	int *sa;

	sa = fn->slot;
	a = 1 << al;
	l = sz;

	if (l > a) {
		/* for large slots, we just
		 * tack them on the next max
		 * alignment slot available
		 * todo, could sophisticate
		 */
		l = (l + a-1) & ~(a-1);
		s = sa[N-1] + l;
		ret = s;
		for (j=0, k=1; j<N; j++, k*=2) {
			l = (l + k-1) & ~(k-1);
			sa[j] = sa[N-1] + l;
		}
	} else {
		j = al;
		s = sa[j] + a;
		ret = s;
	Shift:
		if (j < N-1 && s < sa[j+1])
			/* ........-----------...
			 * ^       ^          ^
			 * sa[j]  sa[j]+a    sa[j+1]
			 *
			 * we have to skip to the
			 * next large whole
			 */
			s = sa[j+1];

		for (k=0; k<=j; k++)
			/* move all smaller holes
			 * that we contain with us
			 */
			if (sa[k] == sa[j])
				sa[k] = s;

		if (j < N-1 && s > sa[j+1]) {
			/* we were in a bigger hole,
			 * it needs to shift further
			 */
			s = sa[++j] + (a *= 2);
			goto Shift;
		}
	}
	return ret;
}

/* instruction selection
 * requires use counts (as given by parsing)
 */
void
isel(Fn *fn)
{
	Blk *b;
	Ins *i;
	Phi *p;
	Ref *a;
	int n, al, s;
	int64_t sz;

	/* 1. assign slots to fast allocs */
	for (n=Tmp0; n<fn->ntmp; n++)
		fn->tmp[n].spill = 0;
	fn->slot[0] = 0;
	fn->slot[1] = 0;
	fn->slot[2] = 2;
	for (b=fn->start, i=b->ins; i-b->ins < b->nins; i++)
		if (OAlloc <= i->op && i->op <= OAlloc1) {
			if (rtype(i->arg[0]) != RCon)
				break;
			sz = fn->con[i->arg[0].val].val;
			if (sz < 0 || sz >= INT_MAX-3)
				diag("isel: invalid alloc size");
			sz = (sz + 3) / 4;
			al = i->op - OAlloc;
			s = slot_(sz, al, fn);
			assert(s > 0);
			fn->tmp[i->to.val].spill = s;
			i->to = R;
		}


	/* 2. select machine instructions */
	for (b=fn->start; b; b=b->link) {

		/* 2.1. process block instructions */
		curi = &insb[NIns];
		seljmp(b, fn);
		for (i=&b->ins[b->nins]; i>b->ins;) {
			sel(*--i, fn);
		}
		n = &insb[NIns] - curi;
		free(b->ins);
		b->ins = alloc(n * sizeof b->ins[0]);
		memcpy(b->ins, curi, n * sizeof b->ins[0]);
		b->nins = n;

		/* 2.2. fix fast local references in phis */
		for (p=b->phi; p; p=p->link)
			for (a=p->arg; a-p->arg < p->narg; a++)
				if (rtype(*a) == RTmp)
				if ((s = fn->tmp[a->val].spill))
					*a = MEM(s);
	}
}
