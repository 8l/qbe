#include "lisc.h"
#include <limits.h>

/* For x86_64, do the following:
 *
 * - lower calls
 * - check that constants are used only in
 *   places allowed
 * - ensure immediates always fit in 32b
 * - explicit machine register contraints
 *   on instructions like division.
 * - implement fast locals (the streak of
 *   constant allocX in the first basic block)
 * - recognize complex addressing modes
 *
 * Invariant: the use counts that are used
 *            in sel() must be sound.  This
 *            is not so trivial, maybe the
 *            dce should be moved out...
 */

typedef struct ANum ANum;
typedef struct AClass AClass;

struct ANum {
	char n, l, r;
	Ins *i;
	Ref mem;
};

static void amatch(Addr *, Ref, ANum *, Fn *, int);

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
	case CBits:
		val = fn->con[r.val].bits.i;
		return (val < INT32_MIN || val > INT32_MAX);
	}
}

static int
rslot(Ref r, Fn *fn)
{
	if (rtype(r) != RTmp)
		return -1;
	return fn->tmp[r.val].slot;
}

static int
argcls(Ins *i)
{
	/* fixme, not correct for some instructions (bcast) */
	return i->cls;
}

static void
fixarg(Ref *r, int k, int phi, Fn *fn)
{
	Addr a;
	Ref r0, r1;
	int s;

	r1 = r0 = *r;
	s = rslot(r0, fn);
	if (KBASE(k) == 1 && rtype(r0) == RCon) {
		/* load floating points from memory
	 	* slots, they can't be used as
	 	* immediates
	 	*/
		r1 = MEM(fn->nmem);
		vgrow(&fn->mem, ++fn->nmem);
		memset(&a, 0, sizeof a);
		a.offset.type = CAddr;
		sprintf(a.offset.label, ".fp%d", r0.val);
		fn->con[r0.val].emit = 1;
		fn->mem[fn->nmem-1] = a;
	}
	else if (!phi && rtype(r0) == RCon && noimm(r0, fn)) {
		/* load constants that do not fit in
	 	* a 32bit signed integer into a
	 	* long temporary
	 	*/
		r1 = newtmp("isel", fn);
		emit(OCopy, Kl, r1, r0, R);
	}
	else if (s != -1) {
		/* load fast locals' addresses into
	 	* temporaries right before the
	 	* instruction
	 	*/
		r1 = newtmp("isel", fn);
		emit(OAddr, Kl, r1, SLOT(s), R);
	}
	*r = r1;
}

static void
chuse(Ref r, int du, Fn *fn)
{
	if (rtype(r) == RTmp)
		fn->tmp[r.val].nuse += du;
}

static void
seladdr(Ref *r, ANum *an, Fn *fn)
{
	Addr a;
	Ref r0, r1;

	r0 = *r;
	if (rtype(r0) == RTmp) {
		chuse(r0, -1, fn);
		r1 = an[r0.val].mem;
		if (req(r1, R)) {
			amatch(&a, r0, an, fn, 1);
			vgrow(&fn->mem, ++fn->nmem);
			fn->mem[fn->nmem-1] = a;
			r1 = MEM(fn->nmem-1);
			chuse(a.base, +1, fn);
			chuse(a.index, +1, fn);
			if (rtype(a.base) != RTmp)
			if (rtype(a.index) != RTmp)
				an[r0.val].mem = r1;
		}
		*r = r1;
	}
}

static void
selcmp(Ref arg[2], int k, Fn *fn)
{
	Ref r;

	if (rtype(arg[0]) == RCon) {
		r = arg[1];
		arg[1] = arg[0];
		arg[0] = r;
	}
	assert(rtype(arg[0]) != RCon);
	emit(OXCmp, k, R, arg[1], arg[0]);
	fixarg(&curi->arg[0], argcls(curi), 0, fn);
}

static void
sel(Ins i, ANum *an, Fn *fn)
{
	Ref r0, r1;
	int x, k;
	int64_t val;
	Ins *i0;

	if (rtype(i.to) == RTmp)
	if (!isreg(i.to) && !isreg(i.arg[0]) && !isreg(i.arg[1]))
	if (fn->tmp[i.to.val].nuse == 0) {
		chuse(i.arg[0], -1, fn);
		chuse(i.arg[1], -1, fn);
		return;
	}
	i0 = curi;
	k = i.cls;
	switch (i.op) {
	case ODiv:
	case ORem:
		if (i.op == ODiv)
			r0 = TMP(RAX), r1 = TMP(RDX);
		else
			r0 = TMP(RDX), r1 = TMP(RAX);
		emit(OCopy, k, i.to, r0, R);
		emit(OCopy, k, R, r1, R);
		if (rtype(i.arg[1]) == RCon) {
			/* immediates not allowed for
			 * divisions in x86
			 */
			r0 = newtmp("isel", fn);
		} else
			r0 = i.arg[1];
		emit(OXDiv, k, R, r0, R);
		emit(OSign, k, TMP(RDX), TMP(RAX), R);
		emit(OCopy, k, TMP(RAX), i.arg[0], R);
		if (rtype(i.arg[1]) == RCon)
			emit(OCopy, k, r0, i.arg[1], R);
		break;
	case ONop:
		break;
	case OStorel:
	case OStorew:
	case OStoreh:
	case OStoreb:
		seladdr(&i.arg[1], an, fn);
		goto Emit;
	case_OLoad:
		seladdr(&i.arg[0], an, fn);
		goto Emit;
	case OXPush:
	case OCall:
	case OSAlloc:
	case OCopy:
	case OAdd:
	case OSub:
	case OMul:
	case OAnd:
	case OXTest:
	case_OExt:
Emit:
		emiti(i);
		fixarg(&curi->arg[0], argcls(curi), 0, fn);
		fixarg(&curi->arg[1], argcls(curi), 0, fn);
		break;
	case OAlloc:
	case OAlloc+1:
	case OAlloc+2: /* == OAlloc1 */
		/* we need to make sure
		 * the stack remains aligned
		 * (rsp = 0) mod 16
		 */
		if (rtype(i.arg[0]) == RCon) {
			assert(fn->con[i.arg[0].val].type == CBits);
			val = fn->con[i.arg[0].val].bits.i;
			val = (val + 15)  & ~INT64_C(15);
			if (val < 0 || val > INT32_MAX)
				diag("isel: alloc too large");
			emit(OAlloc, Kl, i.to, getcon(val, fn), R);
		} else {
			/* r0 = (i.arg[0] + 15) & -16 */
			r0 = newtmp("isel", fn);
			r1 = newtmp("isel", fn);
			emit(OSAlloc, Kl, i.to, r0, R);
			emit(OAnd, 1, r0, r1, getcon(-16, fn));
			emit(OAdd, 1, r1, i.arg[0], getcon(15, fn));
		}
		break;
	default:
		if (OExt <= i.op && i.op <= OExt1)
			goto case_OExt;
		if (OLoad <= i.op && i.op <= OLoad1)
			goto case_OLoad;
		if (OCmp <= i.op && i.op <= OCmp1) {
			x = i.op - OCmp;
			if (rtype(i.arg[0]) == RCon)
				x = COP(x);
			emit(OXSet+x, Kw, i.to, R, R);
			selcmp(i.arg, k, fn);
			break;
		}
		diag("isel: non-exhaustive implementation");
	}

	while (i0 > curi && --i0)
		if (rslot(i0->arg[0], fn) != -1
		||  rslot(i0->arg[1], fn) != -1)
			diag("isel: usupported address argument");
}

static Ins *
flagi(Ins *i0, Ins *i)
{
	while (i>i0)
		switch ((--i)->op) {
		default:
			if (OCmp <= i->op && i->op <= OCmp1)
				return i;
			if (OExt <= i->op && i->op <= OExt1)
				continue;
			if (OLoad <= i->op && i->op <= OLoad1)
				continue;
			return 0;
		case OAdd:  /* flag-setting */
		case OSub:
		case OAnd:
			return i;
		case OCopy: /* flag-transparent */
		case OStorel:
		case OStorew:
		case OStoreh:
		case OStoreb:;
		}
	return 0;
}

static void
seljmp(Blk *b, Fn *fn)
{
	Ref r;
	int c, w;
	Ins *fi;

	switch (b->jmp.type) {
	default:
		return;
	case JRetc:
		assert(!"retc todo");
	case JRetw:
	case JRetl:
		w = b->jmp.type == JRetl;
		b->jmp.type = JRet0;
		r = b->jmp.arg;
		b->jmp.arg = R;
		emit(OCopy, w ? Kl : Kw, TMP(RAX), r, R);
		return;
	case JJnz:;
	}
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
				assert(fn->tmp[r.val].ndef == 1);
				selcmp(fi->arg, fi->cls, fn);
				*fi = (Ins){.op = ONop};
			}
			return;
		}
		if (fi->op == OAnd && fn->tmp[r.val].nuse == 1
		&& (rtype(fi->arg[0]) == RTmp ||
		    rtype(fi->arg[1]) == RTmp)) {
			fi->op = OXTest;
			fi->to = R;
			b->jmp.type = JXJc + Cne;
			if (rtype(fi->arg[1]) == RCon) {
				r = fi->arg[1];
				fi->arg[1] = fi->arg[0];
				fi->arg[0] = r;
			}
			return;
		}
		if (fn->tmp[r.val].nuse > 1) {
			b->jmp.type = JXJc + Cne;
			return;
		}
	}
	selcmp((Ref[2]){r, CON_Z}, 0, fn); /* todo, add long branch if non-zero */
	b->jmp.type = JXJc + Cne;
}

struct AClass {
	int inmem;
	int align;
	uint size;
	int rty[2];
};

enum {
	RNone,
	RInt,
	RSse,
};

static void
aclass(AClass *a, Typ *t)
{
	int e, s, n, rty;
	uint sz, al;

	sz = t->size;
	al = 1u << t->align;

	/* the ABI requires sizes to be rounded
	 * up to the nearest multiple of 8, moreover
	 * it makes it easy load and store structures
	 * in registers
	 */
	if (al < 8)
		al = 8;
	sz = (sz + al-1) & -al;

	a->size = sz;
	a->align = t->align;

	if (t->dark || sz > 16) {
		/* large or unaligned structures are
		 * required to be passed in memory
		 */
		a->inmem = 1;
		return;
	}

	for (e=0, s=0; e<2; e++) {
		rty = RNone;
		for (n=0; n<8 && t->seg[s].len; s++) {
			if (t->seg[s].flt) {
				if (rty == RNone)
					rty = RSse;
			} else
				rty = RInt;
			n += t->seg[s].len;
		}
		assert(n <= 8);
		a->rty[e] = rty;
	}
}

static int
classify(Ins *i0, Ins *i1, AClass *ac, int op)
{
	int nint, ni, nsse, ns, n;
	AClass *a;
	Ins *i;

	nint = 6;
	nsse = 8;
	for (i=i0, a=ac; i<i1; i++, a++) {
		if (i->op == op) {
			if (nint > 0) {
				nint--;
				a->inmem = 0;
			} else
				a->inmem = 2;
			a->align = 3;
			a->size = 8;
			a->rty[0] = RInt;
		} else {
			n = i->arg[0].val & AMask;
			aclass(a, &typ[n]);
			if (a->inmem)
				continue;
			ni = ns = 0;
			for (n=0; n<2; n++)
				switch (a->rty[n]) {
				case RInt:
					ni++;
					break;
				case RSse:
					ns++;
					break;
				}
			if (nint > ni && nsse > ns) {
				nint -= ni;
				nsse -= ns;
			} else
				a->inmem = 1;
		}
	}

	return (6-nint) << 4;
}

int rsave[NRSave] = {
	RDI, RSI, RDX, RCX, R8, R9, R10, R11, RAX,
	XMM0, XMM1, XMM2, XMM3, XMM4, XMM5, XMM6, XMM7, XMM8,
	XMM9, XMM10, XMM11, XMM12, XMM13, XMM14, /* XMM15 */
};
int rclob[NRClob] = {RBX, R12, R13, R14, R15};

ulong
calldef(Ins i, int p[2])
{
	ulong b;
	int ni, nf;

	b = 0;
	ni = i.arg[1].val & 3;
	nf = (i.arg[1].val >> 2) & 3;
	if (ni >= 1)
		b |= BIT(RAX);
	if (ni >= 2)
		b |= BIT(RDX);
	if (nf >= 1)
		b |= BIT(XMM0);
	if (nf >= 2)
		b |= BIT(XMM1);
	if (p) {
		p[0] = ni;
		p[1] = nf;
	}
	return b;
}

ulong
calluse(Ins i, int p[2])
{
	ulong b;
	int j, ni, nf;

	b = 0;
	ni = (i.arg[1].val >> 4) & 15;
	nf = (i.arg[1].val >> 8) & 15;
	for (j=0; j<ni; j++)
		b |= BIT(rsave[j]);
	for (j=0; j<nf; j++)
		b |= BIT(XMM0+j);
	if (p) {
		p[0] = ni;
		p[1] = nf;
	}
	return b;
}

static void
selcall(Fn *fn, Ins *i0, Ins *i1)
{
	Ins *i;
	AClass *ac, *a;
	int ci, ni;
	uint stk, sz;
	Ref r, r1;

	ac = alloc((i1-i0) * sizeof ac[0]);
	ci = classify(i0, i1, ac, OArg);

	for (stk=0, a=&ac[i1-i0]; a>ac;)
		if ((--a)->inmem) {
			assert(a->align <= 4);
			stk += a->size;
			if (a->align == 4) /* todo, bigger alignments */
				stk += stk & 15;
		}
	stk += stk & 15;

	if (!req(i1->arg[1], R))
		diag("struct-returning function not implemented");
	if (stk) {
		r = getcon(-(int64_t)stk, fn);
		emit(OSAlloc, Kl, R, r, R);
	}
	emit(OCopy, i1->cls, i1->to, TMP(RAX), R);
	emit(OCall, i1->cls, R, i1->arg[0], CALL(1 + ci));

	for (i=i0, a=ac, ni=0; i<i1; i++, a++) {
		if (a->inmem)
			continue;
		if (i->op == OArgc) {
			if (a->rty[0] == RSse || a->rty[1] == RSse)
				diag("isel: unsupported float struct");
			if (a->size > 8) {
				r = TMP(rsave[ni+1]);
				r1 = newtmp("isel", fn);
				emit(OLoadl, Kl, r, r1, R);
				r = getcon(8, fn);
				emit(OAdd, Kl, r1, i->arg[1], r);
				r = TMP(rsave[ni]);
				ni += 2;
			} else
				r = TMP(rsave[ni++]);
			emit(OLoadl, Kl, r, i->arg[1], R);
		} else {
			r = TMP(rsave[ni++]);
			emit(OCopy, i->cls, r, i->arg[0], R);
		}
	}
	for (i=i0, a=ac; i<i1; i++, a++) {
		if (!a->inmem)
			continue;
		sz = a->size;
		if (a->align == 4)
			sz += (stk-sz) & 15;
		stk -= sz;
		if (i->op == OArgc) {
			assert(!"argc todo 1");
		} else {
			emit(OXPush, Kl, R, i->arg[0], R);
		}
	}
	if (stk) {
		assert(stk == 8);
		emit(OXPush, Kl, R, CON_Z, R);
	}
}

static void
selpar(Fn *fn, Ins *i0, Ins *i1)
{
	AClass *ac, *a;
	Ins *i;
	int ni, stk, al;
	Ref r, r1, r2;

	ac = alloc((i1-i0) * sizeof ac[0]);
	classify(i0, i1, ac, OPar);

	curi = insb;
	ni = 0;
	assert(NAlign == 3);
	stk = -2;
	for (i=i0, a=ac; i<i1; i++, a++) {
		switch (a->inmem) {
		case 1:
			assert(!"argc todo 2");
			continue;
		case 2:
			stk -= 2;
			*curi++ = (Ins){OLoad, i->to, {SLOT(stk)}, i->cls};
			continue;
		}
		r = TMP(rsave[ni++]);
		if (i->op == OParc) {
			if (a->rty[0] == RSse || a->rty[1] == RSse)
				diag("isel: unsupported float struct");
			r1 = newtmp("isel", fn);
			*curi++ = (Ins){OCopy, r1, {r}, Kl};
			a->rty[0] = r1.val;
			if (a->size > 8) {
				r = TMP(rsave[ni++]);
				r1 = newtmp("isel", fn);
				*curi++ = (Ins){OCopy, r1, {r}, Kl};
				a->rty[1] = r1.val;
			}
		} else
			*curi++ = (Ins){OCopy, i->to, {r}, i->cls};
	}
	for (i=i0, a=ac; i<i1; i++, a++) {
		if (i->op != OParc || a->inmem)
			continue;
		assert(NAlign == 3);
		for (al=0; a->align >> (al+2); al++)
			;
		r1 = i->to;
		r = TMP(a->rty[0]);
		r2 = getcon(a->size, fn);
		*curi++ = (Ins){OAlloc+al, r1, {r2}, Kl};
		*curi++ = (Ins){OStorel, R, {r, r1}, 0};
		if (a->size > 8) {
			r = newtmp("isel", fn);
			r2 = getcon(8, fn);
			*curi++ = (Ins){OAdd, r, {r1, r2}, Kl};
			r1 = TMP(a->rty[1]);
			*curi++ = (Ins){OStorel, R, {r1, r}, 0};
		}
	}
}

static int
aref(Ref r, ANum *ai)
{
	switch (rtype(r)) {
	default:
		diag("isel: aref defaulted");
	case RCon:
		return 2;
	case RTmp:
		return ai[r.val].n;
	}
}

static int
ascale(Ref r, Con *con)
{
	int64_t n;

	if (rtype(r) != RCon)
		return 0;
	if (con[r.val].type != CBits)
		return 0;
	n = con[r.val].bits.i;
	return n == 1 || n == 2 || n == 4 || n == 8;
}

static void
anumber(ANum *ai, Blk *b, Con *con)
{
	/* This should be made obsolete by a proper
	 * reassoc pass.
	 *
	 * Rules:
	 *
	 *   RTmp(_) -> 0    tmp
	 *   ( RTmp(_) -> 1    slot )
	 *   RCon(_) -> 2    con
	 *   0 * 2   -> 3    s * i (when constant is 1,2,4,8)
	 */
	static char add[10][10] = {
		[2] [2] = 2,              /* folding */
		[2] [5] = 5, [5] [2] = 5,
		[2] [6] = 6, [6] [2] = 6,
		[0] [0] = 4,              /* b + s * i */
		/* [0] [1] = 4, [1] [0] = 4, */
		[0] [3] = 4, [3] [0] = 4,
		[2] [3] = 5, [3] [2] = 5, /* o + s * i */
		[2] [4] = 6, [4] [2] = 6, /* o + b + s * i */
		[0] [5] = 6, [5] [0] = 6,
		/* [1] [5] = 6, [5] [1] = 6, */
	};
	int a, a1, a2, n1, n2, t1, t2;
	Ins *i;

	for (i=b->ins; i-b->ins < b->nins; i++) {
		if (rtype(i->to) == RTmp)
			ai[i->to.val].i = i;
		if (i->op != OAdd && i->op != OMul)
			continue;
		a1 = aref(i->arg[0], ai);
		a2 = aref(i->arg[1], ai);
		t1 = a1 != 1 && a1 != 2;
		t2 = a2 != 1 && a2 != 2;
		if (i->op == OAdd) {
			a = add[n1 = a1][n2 = a2];
			if (t1 && a < add[0][a2])
				a = add[n1 = 0][n2 = a2];
			if (t2 && a < add[a1][0])
				a = add[n1 = a1][n2 = 0];
			if (t1 && t2 && a < add[0][0])
				a = add[n1 = 0][n2 = 0];
		} else {
			n1 = n2 = a = 0;
			if (ascale(i->arg[0], con) && t2)
				a = 3, n1 = 2, n2 = 0;
			if (t1 && ascale(i->arg[1], con))
				a = 3, n1 = 0, n2 = 2;
		}
		ai[i->to.val].n = a;
		ai[i->to.val].l = n1;
		ai[i->to.val].r = n2;
	}
}

static void
amatch(Addr *a, Ref r, ANum *ai, Fn *fn, int top)
{
	Ins *i;
	int nl, nr, t, s;
	Ref al, ar;

	if (top)
		memset(a, 0, sizeof *a);
	if (rtype(r) == RCon) {
		addcon(&a->offset, &fn->con[r.val]);
		return;
	}
	assert(rtype(r) == RTmp);
	i = ai[r.val].i;
	nl = ai[r.val].l;
	nr = ai[r.val].r;
	if (i) {
		if (nl > nr) {
			al = i->arg[1];
			ar = i->arg[0];
			t = nl, nl = nr, nr = t;
		} else {
			al = i->arg[0];
			ar = i->arg[1];
		}
	}
	switch (ai[r.val].n) {
	default:
		diag("isel: amatch defaulted");
	case 3: /* s * i */
		if (!top) {
			a->index = al;
			a->scale = fn->con[ar.val].bits.i;
		} else
			a->base = r;
		break;
	case 4: /* b + s * i */
		switch (nr) {
		case 0:
			if (fn->tmp[ar.val].slot != -1) {
				al = i->arg[1];
				ar = i->arg[0];
			}
			a->index = ar;
			a->scale = 1;
			break;
		case 3:
			amatch(a, ar, ai, fn, 0);
			break;
		}
		r = al;
	case 0:
		s = fn->tmp[r.val].slot;
		if (s != -1)
			r = SLOT(s);
		a->base = r;
		break;
	case 2: /* constants */
	case 5: /* o + s * i */
	case 6: /* o + b + s * i */
		amatch(a, ar, ai, fn, 0);
		amatch(a, al, ai, fn, 0);
		break;
	}
}

/* instruction selection
 * requires use counts (as given by parsing)
 */
void
isel(Fn *fn)
{
	Blk *b, **sb;
	Ins *i, *i0, *ip;
	Phi *p;
	uint a;
	int n, m, al;
	int64_t sz;
	ANum *ainfo;

	for (n=0; n<fn->ntmp; n++)
		fn->tmp[n].slot = -1;
	fn->slot = 0;

	/* lower arguments */
	for (b=fn->start, i=b->ins; i-b->ins < b->nins; i++)
		if (i->op != OPar && i->op != OParc)
			break;
	selpar(fn, b->ins, i);
	n = b->nins - (i - b->ins) + (curi - insb);
	i0 = alloc(n * sizeof(Ins));
	ip = icpy(ip = i0, insb, curi - insb);
	ip = icpy(ip, i, &b->ins[b->nins] - i);
	b->nins = n;
	b->ins = i0;

	/* lower function calls */
	for (b=fn->start; b; b=b->link) {
		curi = &insb[NIns];
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			if ((--i)->op == OCall) {
				for (i0=i; i0>b->ins; i0--)
					if ((i0-1)->op != OArg)
					if ((i0-1)->op != OArgc)
						break;
				selcall(fn, i0, i);
				i = i0;
				continue;
			}
			assert(i->op != OArg && i->op != OArgc);
			emiti(*i);
		}
		b->nins = &insb[NIns] - curi;
		idup(&b->ins, curi, b->nins);
	}

	if (debug['A']) {
		fprintf(stderr, "\n> After call lowering:\n");
		printfn(fn, stderr);
	}

	/* assign slots to fast allocs */
	b = fn->start;
	assert(NAlign == 3 && "change n=4 and sz /= 4 below");
	for (al=OAlloc, n=4; al<=OAlloc1; al++, n*=2)
		for (i=b->ins; i-b->ins < b->nins; i++)
			if (i->op == al) {
				if (rtype(i->arg[0]) != RCon)
					break;
				sz = fn->con[i->arg[0].val].bits.i;
				if (sz < 0 || sz >= INT_MAX-3)
					diag("isel: invalid alloc size");
				sz = (sz + n-1) & -n;
				sz /= 4;
				fn->tmp[i->to.val].slot = fn->slot;
				fn->slot += sz;
				*i = (Ins){.op = ONop};
			}

	/* process basic blocks */
	n = fn->ntmp;
	ainfo = emalloc(n * sizeof ainfo[0]);
	for (b=fn->start; b; b=b->link) {
		for (sb=(Blk*[3]){b->s1, b->s2, 0}; *sb; sb++)
			for (p=(*sb)->phi; p; p=p->link) {
				for (a=0; p->blk[a] != b; a++)
					assert(a+1 < p->narg);
				fixarg(&p->arg[a], p->cls, 1, fn);
			}
		for (m=0; m<n; m++)
			ainfo[m] = (ANum){.n = 0, .i = 0};
		anumber(ainfo, b, fn->con);
		curi = &insb[NIns];
		seljmp(b, fn);
		for (i=&b->ins[b->nins]; i!=b->ins;)
			sel(*--i, ainfo, fn);
		b->nins = &insb[NIns] - curi;
		idup(&b->ins, curi, b->nins);
	}
	free(ainfo);

	if (debug['I']) {
		fprintf(stderr, "\n> After instruction selection:\n");
		printfn(fn, stderr);
	}
}
