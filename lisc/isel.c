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
 */


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

static void
selcmp(Ref arg[2], int w, Fn *fn)
{
	Ref r;

	if (rtype(arg[0]) == RCon) {
		r = arg[1];
		arg[1] = arg[0];
		arg[0] = r;
	}
	assert(rtype(arg[0]) != RCon);
	emit(OXCmp, w, R, arg[1], arg[0]);
	r = arg[1];
	if (w && rtype(r) == RCon && noimm(r, fn)) {
		curi->arg[0] = newtmp("isel", fn);
		emit(OCopy, w, curi->arg[0], r, R);
	}
}

static int
rslot(Ref r, Fn *fn)
{
	if (rtype(r) != RTmp)
		return -1;
	return fn->tmp[r.val].slot;
}

static void
sel(Ins i, Fn *fn)
{
	Ref r0, r1;
	int n, c, s, w;
	int64_t val;
	struct {
		Ref r;
		int s;
	} cpy[2];

	for (n=0; n<2; n++) {
		r0 = i.arg[n];
		cpy[n].s = -1;
		s = rslot(r0, fn);
		if (s != -1) {
			r0 = newtmp("isel", fn);
			i.arg[n] = r0;
			cpy[n].r = r0;
			cpy[n].s = s;
		}
	}

	w = i.wide;
	switch (i.op) {
	case ODiv:
	case ORem:
		if (i.op == ODiv)
			r0 = TMP(RAX), r1 = TMP(RDX);
		else
			r0 = TMP(RDX), r1 = TMP(RAX);
		emit(OCopy, w, i.to, r0, R);
		emit(OCopy, w, R, r1, R);
		if (rtype(i.arg[1]) == RCon) {
			/* immediates not allowed for
			 * divisions in x86
			 */
			r0 = newtmp("isel", fn);
		} else
			r0 = i.arg[1];
		emit(OXDiv, w, R, r0, R);
		emit(OSign, w, TMP(RDX), TMP(RAX), R);
		emit(OCopy, w, TMP(RAX), i.arg[0], R);
		if (rtype(i.arg[1]) == RCon)
			emit(OCopy, w, r0, i.arg[1], R);
		break;
	case ONop:
		break;
	case OXPush:
		n = 1;
		goto Emit;
	case OCall:
	case OSAlloc:
	case OCopy:
	case_OExt:
		n = 0;
		goto Emit;
	case OAdd:
	case OSub:
	case OMul:
	case OAnd:
	case OXTest:
		n = w ? 2 : 0;
		goto Emit;
	case OStorel:
	case OStorew:
	case OStoreb:
	case OStores:
		if (cpy[1].s != -1) {
			i.arg[1] = SLOT(cpy[1].s);
			cpy[1].s = -1;
		}
		n = i.op == OStorel;
		goto Emit;
	case_OLoad:
		if (cpy[0].s != -1) {
			i.arg[0] = SLOT(cpy[0].s);
			cpy[0].s = -1;
		}
		n = 0;
Emit:
		emiti(i);
		while (n--) {
			/* load constants that do not fit in
			 * a 32bit signed integer into a
			 * long temporary
			 */
			r0 = i.arg[n];
			if (rtype(r0) == RCon && noimm(r0, fn)) {
				curi->arg[n] = newtmp("isel", fn);
				emit(OCopy, 1, curi->arg[n], r0, R);
			}
		}
		break;
	case OAlloc:
	case OAlloc+1:
	case OAlloc+2: /* == OAlloc1 */
		/* we need to make sure
		 * the stack remains aligned
		 * (rsp = 0) mod 16
		 */
		if (rtype(i.arg[0]) == RCon) {
			val = fn->con[i.arg[0].val].val;
			val = (val + 15)  & ~INT64_C(15);
			if (val < 0 || val > INT32_MAX)
				diag("isel: alloc too large");
			emit(OAlloc, 0, i.to, getcon(val, fn), R);
		} else {
			/* r0 = (i.arg[0] + 15) & -16 */
			r0 = newtmp("isel", fn);
			r1 = newtmp("isel", fn);
			emit(OSAlloc, 0, i.to, r0, R);
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
			c = i.op - OCmp;
			if (rtype(i.arg[0]) == RCon)
				c = COP(c);
			emit(OXSet+c, 0, i.to, R, R);
			selcmp(i.arg, w, fn);
			break;
		}
		diag("isel: non-exhaustive implementation");
	}

	for (n=0; n<2; n++)
		if (cpy[n].s != -1)
			emit(OAddr, 1, cpy[n].r, SLOT(cpy[n].s), R);
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
		case OStoreb:
		case OStores:;
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
		emit(OCopy, w, TMP(RAX), r, R);
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
				selcmp(fi->arg, fi->wide, fn);
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

typedef struct AClass AClass;

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

int rsave[NRSave] = {RDI, RSI, RDX, RCX, R8, R9, R10, R11, RAX};
int rclob[NRClob] = {RBX, R12, R13, R14, R15};

ulong
calldef(Ins i, int *p)
{
	ulong b;
	int n;

	n = i.arg[1].val & 15;
	b = BIT(RAX);
	if (n == 2)
		b |= BIT(RDX);
	if (p)
		*p = n;
	return b;
}

ulong
calluse(Ins i, int *p)
{
	ulong b;
	int j, n;

	n = (i.arg[1].val >> 4) & 15;
	for (j = 0, b = 0; j < n; j++)
		b |= BIT(rsave[j]);
	if (p)
		*p = n;
	return b;
}

ulong
callclb(Ins i, int *p)
{
	ulong b;
	int j, n;

	n = (i.arg[1].val >> 4) & 15;
	for (j = n, b = 0; j < NRSave; j++)
		b |= BIT(rsave[j]);
	if (p)
		*p = n;
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
		emit(OSAlloc, 0, R, r, R);
	}
	emit(OCopy, i1->wide, i1->to, TMP(RAX), R);
	emit(OCall, 0, R, i1->arg[0], CALL(1 + ci));

	for (i=i0, a=ac, ni=0; i<i1; i++, a++) {
		if (a->inmem)
			continue;
		if (i->op == OArgc) {
			if (a->rty[0] == RSse || a->rty[1] == RSse)
				diag("isel: unsupported float struct");
			if (a->size > 8) {
				r = TMP(rsave[ni+1]);
				r1 = newtmp("isel", fn);
				emit(OLoad, 1, r, r1, R);
				r = getcon(8, fn);
				emit(OAdd, 1, r1, i->arg[1], r);
				r = TMP(rsave[ni]);
				ni += 2;
			} else
				r = TMP(rsave[ni++]);
			emit(OLoad, 1, r, i->arg[1], R);
		} else {
			r = TMP(rsave[ni++]);
			emit(OCopy, i->wide, r, i->arg[0], R);
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
			emit(OXPush, 1, R, i->arg[0], R);
		}
	}
	if (stk) {
		assert(stk == 8);
		emit(OXPush, 1, R, CON_Z, R);
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
			*curi++ = (Ins){OLoad, i->wide, i->to, {SLOT(stk)}};
			continue;
		}
		r = TMP(rsave[ni++]);
		if (i->op == OParc) {
			if (a->rty[0] == RSse || a->rty[1] == RSse)
				diag("isel: unsupported float struct");
			r1 = newtmp("isel", fn);
			*curi++ = (Ins){OCopy, 1, r1, {r}};
			a->rty[0] = r1.val;
			if (a->size > 8) {
				r = TMP(rsave[ni++]);
				r1 = newtmp("isel", fn);
				*curi++ = (Ins){OCopy, 1, r1, {r}};
				a->rty[1] = r1.val;
			}
		} else
			*curi++ = (Ins){OCopy, i->wide, i->to, {r}};
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
		*curi++ = (Ins){OAlloc+al, 1, r1, {r2}};
		*curi++ = (Ins){OStorel, 0, R, {r, r1}};
		if (a->size > 8) {
			r = newtmp("isel", fn);
			r2 = getcon(8, fn);
			*curi++ = (Ins){OAdd, 1, r, {r1, r2}};
			r1 = TMP(a->rty[1]);
			*curi++ = (Ins){OStorel, 0, R, {r1, r}};
		}
	}
}

int
abase(Ref r, int *an, Con *c)
{
	int64_t n;

	switch (rtype(r)) {
	case RTmp: return an[r.val] & 15;
	case RCon:
		if (c[r.val].type == CNum) {
			n = c[r.val].val;
			if (n == 1 || n == 2
			||  n == 4 || n == 8)
				return 1;
		}
		return 2;
	}
	return 9;
}

static void
anumber(int *an, Blk *b, Con *c)
{
	static char addtbl[10][10] = {
		[0] [0] = 4,
		[0] [3] = 4, [3] [0] = 4,
		[2] [3] = 5, [3] [2] = 5,
		[1] [3] = 5, [3] [1] = 5,
		[2] [4] = 6, [4] [2] = 6,
		[1] [4] = 6, [4] [1] = 6,
		[0] [5] = 6, [5] [0] = 6,
	};
	int a, a1, a2, n1, n2, t1, t2;
	Ins *i;

	/* This numbering will become useless
	 * once a proper reassoc pass is ready.
	 */

	/* Tree automaton rules:
	 *
	 *   RTmp(_) -> 0    tmp
	 *   RCon(1) -> 1
	 *   RCon(2) -> 1
	 *   RCon(4) -> 1    scale
	 *   RCon(8) -> 1
	 *   RCon(_) -> 2    con
	 *   0 * 1   -> 3    s * i
	 *   0 + 0   -> 4    b + (1 *) i
	 *   0 + 3   -> 4
	 *   2 + 3   -> 5    o + s * i
	 *   1 + 3   -> 5
	 *   2 + 4   -> 6    o + b + s * i
	 *   1 + 4   -> 6
	 *   0 + 5   -> 6
	 */

	for (i=b->ins; i<&b->ins[b->nins]; i++) {
		if (i->op != OAdd && i->op != OMul)
			continue;
		a1 = abase(i->arg[0], an, c);
		a2 = abase(i->arg[1], an, c);
		t1 = rtype(i->arg[0]) == RTmp;
		t2 = rtype(i->arg[1]) == RTmp;
		if (i->op == OAdd) {
			a = addtbl[n1 = a1][n2 = a2];
			if (t1 && a < addtbl[0][a2])
				a = addtbl[n1 = 0][n2 = a2];
			if (t2 && a < addtbl[a1][0])
				a = addtbl[n1 = a1][n2 = 0];
			if (t1 && t2 && a < addtbl[0][0])
				a = addtbl[n1 = 0][n2 = 0];
			an[i->to.val] = a + (n1 << 4) + (n2 << 8);
		}
		if (i->op == OMul && a1 == 1 && t2)
			an[i->to.val] = 3 + (1 << 4) + (0 << 8);
		if (i->op == OMul && t1 && a2 == 1)
			an[i->to.val] = 3 + (0 << 4) + (1 << 8);
	}
}

typedef struct Addr Addr;

struct Addr {
	Ref offset;
	Ref base;
	Ref index;
	int scale;
};

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
	int n, al, s;
	int64_t sz;
	int *anum;

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
		for (i=&b->ins[b->nins]; i>b->ins;) {
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
			emit(i->op, i->wide, i->to, i->arg[0], i->arg[1]);
		}
		b->nins = &insb[NIns] - curi;
		idup(&b->ins, curi, b->nins);
	}

	if (debug['C']) {
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
				sz = fn->con[i->arg[0].val].val;
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
	anum = emalloc(n * sizeof anum[0]);
	for (b=fn->start; b; b=b->link) {
		for (sb=(Blk*[3]){b->s1, b->s2, 0}; *sb; sb++)
			for (p=(*sb)->phi; p; p=p->link) {
				for (a=0; p->blk[a] != b; a++)
					assert(a+1 < p->narg);
				s = rslot(p->arg[a], fn);
				if (s != -1) {
					p->arg[a] = newtmp("isel", fn);
					emit(OAddr, 1, p->arg[a], SLOT(s), R);
				}
			}
		memset(anum, 0, n * sizeof anum[0]);
		anumber(anum, b, fn->con);
		curi = &insb[NIns];
		seljmp(b, fn);
		for (i=&b->ins[b->nins]; i>b->ins;)
			sel(*--i, fn);
		b->nins = &insb[NIns] - curi;
		idup(&b->ins, curi, b->nins);
	}
	free(anum);

	if (debug['I']) {
		fprintf(stderr, "\n> After instruction selection:\n");
		printfn(fn, stderr);
	}
}
