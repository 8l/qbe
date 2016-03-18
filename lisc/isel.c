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
typedef struct RAlloc RAlloc;

struct ANum {
	char n, l, r;
	Ins *i;
	Ref mem;
};

static void amatch(Addr *, Ref, ANum *, Fn *, int);

static int
fcmptoi(int fc)
{
	switch (fc) {
	default:   diag("isel: fcmptoi defaulted");
	case FCle: return ICule;
	case FClt: return ICult;
	case FCgt: return ICugt;
	case FCge: return ICuge;
	case FCne: return ICne;
	case FCeq: return ICeq;
	case FCo:  return ICXnp;
	case FCuo: return ICXp;
	}
}

static int
iscmp(int op, int *pk, int *pc)
{
	int k, c;

	if (OCmpw <= op && op <= OCmpw1) {
		c = op - OCmpw;
		k = Kw;
	}
	else if (OCmpl <= op && op <= OCmpl1) {
		c = op - OCmpl;
		k = Kl;
	}
	else if (OCmps <= op && op <= OCmps1) {
		c = fcmptoi(op - OCmps);
		k = Ks;
	}
	else if (OCmpd <= op && op <= OCmpd1) {
		c = fcmptoi(op - OCmpd);
		k = Kd;
	}
	else
		return 0;
	if (pk)
		*pk = k;
	if (pc)
		*pc = c;
	return 1;
}

static int
noimm(Ref r, Fn *fn)
{
	int64_t val;

	if (rtype(r) != RCon)
		return 0;
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
argcls(Ins *i, int n)
{
	return opdesc[i->op].argcls[n][i->cls];
}

static void
fixarg(Ref *r, int k, int phi, Fn *fn)
{
	Addr a;
	Ref r0, r1;
	int s, n;

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
		n = stashfp(fn->con[r0.val].bits.i, KWIDE(k));
		sprintf(a.offset.label, ".Lfp%d", n);
		fn->mem[fn->nmem-1] = a;
	}
	else if (!phi && k == Kl && noimm(r0, fn)) {
		/* load constants that do not fit in
		 * a 32bit signed integer into a
		 * long temporary
		 */
		r1 = newtmp("isel", Kl, fn);
		emit(OCopy, Kl, r1, r0, R);
	}
	else if (s != -1) {
		/* load fast locals' addresses into
		 * temporaries right before the
		 * instruction
		 */
		r1 = newtmp("isel", Kl, fn);
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
	fixarg(&curi->arg[0], k, 0, fn);
}

static void
sel(Ins i, ANum *an, Fn *fn)
{
	Ref r0, r1;
	int x, k, kc;
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
	case OUDiv:
	case OURem:
		if (i.op == ODiv || i.op == OUDiv)
			r0 = TMP(RAX), r1 = TMP(RDX);
		else
			r0 = TMP(RDX), r1 = TMP(RAX);
		emit(OCopy, k, i.to, r0, R);
		emit(OCopy, k, R, r1, R);
		if (rtype(i.arg[1]) == RCon) {
			/* immediates not allowed for
			 * divisions in x86
			 */
			r0 = newtmp("isel", k, fn);
		} else
			r0 = i.arg[1];
		if (i.op == ODiv || i.op == ORem) {
			emit(OXIDiv, k, R, r0, R);
			emit(OSign, k, TMP(RDX), TMP(RAX), R);
		} else {
			emit(OXDiv, k, R, r0, R);
			emit(OCopy, k, TMP(RDX), CON_Z, R);
		}
		emit(OCopy, k, TMP(RAX), i.arg[0], R);
		if (rtype(i.arg[1]) == RCon)
			emit(OCopy, k, r0, i.arg[1], R);
		break;
	case OSar:
	case OShr:
	case OShl:
		if (rtype(i.arg[1]) == RCon)
			goto Emit;
		r0 = i.arg[1];
		i.arg[1] = TMP(RCX);
		emit(OCopy, Kw, R, TMP(RCX), R);
		emiti(i);
		emit(OCopy, Kw, TMP(RCX), r0, R);
		break;
	case ONop:
		break;
	case OStored:
		if (rtype(i.arg[0]) == RCon)
			i.op = OStorel;
	case OStores:
		if (rtype(i.arg[0]) == RCon)
			i.op = OStorew;
	case OStorel:
	case OStorew:
	case OStoreh:
	case OStoreb:
		seladdr(&i.arg[1], an, fn);
		goto Emit;
	case_OLoad:
		seladdr(&i.arg[0], an, fn);
		goto Emit;
	case OCall:
	case OSAlloc:
	case OCopy:
	case OAdd:
	case OSub:
	case OMul:
	case OAnd:
	case OOr:
	case OXor:
	case OXTest:
	case OFtosi:
	case OSitof:
	case OExts:
	case OTruncd:
	case OCast:
	case_OExt:
Emit:
		emiti(i);
		fixarg(&curi->arg[0], argcls(curi, 0), 0, fn);
		fixarg(&curi->arg[1], argcls(curi, 1), 0, fn);
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
			r0 = newtmp("isel", Kl, fn);
			r1 = newtmp("isel", Kl, fn);
			emit(OSAlloc, Kl, i.to, r0, R);
			emit(OAnd, Kl, r0, r1, getcon(-16, fn));
			emit(OAdd, Kl, r1, i.arg[0], getcon(15, fn));
		}
		break;
	default:
		if (isext(i.op))
			goto case_OExt;
		if (isload(i.op))
			goto case_OLoad;
		if (iscmp(i.op, &kc, &x)) {
			if (rtype(i.arg[0]) == RCon)
				x = icmpop(x);
			emit(OXSet+x, k, i.to, R, R);
			selcmp(i.arg, kc, fn);
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
	while (i>i0) {
		i--;
		if (opdesc[i->op].sflag)
			return i;
		if (opdesc[i->op].lflag)
			continue;
		return 0;
	}
	return 0;
}

struct AClass {
	int inmem;
	int align;
	uint size;
	int cls[2];
};

static void
aclass(AClass *a, Typ *t)
{
	int e, s, n, cls;
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

	a->inmem = 0;
	for (e=0, s=0; e<2; e++) {
		cls = -1;
		for (n=0; n<8 && t->seg[s].len; s++) {
			if (t->seg[s].flt) {
				if (cls == -1)
					cls = Kd;
			} else
				cls = Kl;
			n += t->seg[s].len;
		}
		assert(n <= 8);
		a->cls[e] = cls;
	}
}

static void
blit(Ref rstk, uint soff, Ref rsrc, uint sz, Fn *fn)
{
	Ref r, r1;
	uint boff;

	/* it's an impolite blit, we might go across the end
	 * of the source object a little bit... */
	for (boff=0; sz>0; sz-=8, soff+=8, boff+=8) {
		r = newtmp("abi", Kl, fn);
		r1 = newtmp("abi", Kl, fn);
		emit(OStorel, 0, R, r, r1);
		emit(OAdd, Kl, r1, rstk, getcon(soff, fn));
		r1 = newtmp("abi", Kl, fn);
		emit(OLoad, Kl, r, r1, R);
		emit(OAdd, Kl, r1, rsrc, getcon(boff, fn));
		chuse(rsrc, +1, fn);
		chuse(rstk, +1, fn);
	}
}

static void
retr(Ref reg[2], AClass *aret)
{
	static int retreg[2][2] = {{RAX, RDX}, {XMM0, XMM0+1}};
	int n, k, nr[2];

	nr[0] = nr[1] = 0;
	for (n=0; aret->cls[n]>=0 && n<2; n++) {
		k = KBASE(aret->cls[n]);
		reg[n] = TMP(retreg[k][nr[k]++]);
	}
}

static void
selret(Blk *b, Fn *fn)
{
	int j, k;
	Ref r, r0, reg[2];
	AClass aret;

	j = b->jmp.type;

	if (!isret(j) || j == JRet0)
		return;

	r0 = b->jmp.arg;
	b->jmp.arg = R;
	b->jmp.type = JRet0;

	if (j == JRetc) {
		aclass(&aret, &typ[fn->retty]);
		if (aret.inmem) {
			assert(rtype(fn->retr) == RTmp);
			emit(OCopy, Kl, TMP(RAX), fn->retr, R);
			chuse(fn->retr, +1, fn);
			blit(fn->retr, 0, r0, aret.size, fn);
		} else {
			retr(reg, &aret);
			if (aret.size > 8) {
				r = newtmp("abi", Kl, fn);
				emit(OLoad, Kl, reg[1], r, R);
				emit(OAdd, Kl, r, r0, getcon(8, fn));
				chuse(r0, +1, fn);
			}
			emit(OLoad, Kl, reg[0], r0, R);
		}
	} else {
		k = j - JRetw;
		if (KBASE(k) == 0)
			emit(OCopy, k, TMP(RAX), r0, R);
		else
			emit(OCopy, k, TMP(XMM0), r0, R);
	}
}

static void
seljmp(Blk *b, Fn *fn)
{
	Ref r;
	int c, k;
	Ins *fi;

	if (b->jmp.type == JRet0 || b->jmp.type == JJmp)
		return;
	assert(b->jmp.type == JJnz);
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
		if (iscmp(fi->op, &k, &c)) {
			if (rtype(fi->arg[0]) == RCon)
				c = icmpop(c);
			b->jmp.type = JXJc + c;
			if (fn->tmp[r.val].nuse == 1) {
				assert(fn->tmp[r.val].ndef == 1);
				selcmp(fi->arg, k, fn);
				*fi = (Ins){.op = ONop};
			}
			return;
		}
		if (fi->op == OAnd && fn->tmp[r.val].nuse == 1
		&& (rtype(fi->arg[0]) == RTmp ||
		    rtype(fi->arg[1]) == RTmp)) {
			fi->op = OXTest;
			fi->to = R;
			b->jmp.type = JXJc + ICne;
			if (rtype(fi->arg[1]) == RCon) {
				r = fi->arg[1];
				fi->arg[1] = fi->arg[0];
				fi->arg[0] = r;
			}
			return;
		}
		/* since flags are not tracked in liveness,
		 * the result of the flag-setting instruction
		 * has to be marked as live
		 */
		if (fn->tmp[r.val].nuse == 1)
			emit(OCopy, Kw, R, r, R);
		b->jmp.type = JXJc + ICne;
		return;
	}
	selcmp((Ref[2]){r, CON_Z}, Kw, fn); /* todo, add long branch if non-zero */
	b->jmp.type = JXJc + ICne;
}

static int
classify(Ins *i0, Ins *i1, AClass *ac, int op, AClass *aret)
{
	int nint, ni, nsse, ns, n, *pn;
	AClass *a;
	Ins *i;

	if (aret && aret->inmem)
		nint = 5; /* hidden argument */
	else
		nint = 6;
	nsse = 8;
	for (i=i0, a=ac; i<i1; i++, a++) {
		if (i->op == op) {
			if (KBASE(i->cls) == 0)
				pn = &nint;
			else
				pn = &nsse;
			if (*pn > 0) {
				--*pn;
				a->inmem = 0;
			} else
				a->inmem = 2;
			a->align = 3;
			a->size = 8;
			a->cls[0] = i->cls;
		} else {
			n = i->arg[0].val & AMask;
			aclass(a, &typ[n]);
			if (a->inmem)
				continue;
			ni = ns = 0;
			for (n=0; n<2; n++)
				if (KBASE(a->cls[n]) == 0)
					ni++;
				else
					ns++;
			if (nint >= ni && nsse >= ns) {
				nint -= ni;
				nsse -= ns;
			} else
				a->inmem = 1;
		}
	}

	return ((6-nint) << 4) | ((8-nsse) << 8);
}

int rsave[] = {
	RDI, RSI, RDX, RCX, R8, R9, R10, R11, RAX,
	XMM0, XMM1, XMM2, XMM3, XMM4, XMM5, XMM6, XMM7,
	XMM8, XMM9, XMM10, XMM11, XMM12, XMM13, XMM14
};
int rclob[] = {RBX, R12, R13, R14, R15};

MAKESURE(rsave_has_correct_size, sizeof rsave == NRSave * sizeof(int));
MAKESURE(rclob_has_correct_size, sizeof rclob == NRClob * sizeof(int));

bits
calldef(Ins i, int p[2])
{
	bits b;
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

bits
calluse(Ins i, int p[2])
{
	bits b;
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

static Ref
rarg(int ty, int *ni, int *ns)
{
	if (KBASE(ty) == 0)
		return TMP(rsave[(*ni)++]);
	else
		return TMP(XMM0 + (*ns)++);
}

struct RAlloc {
	Ins i;
	RAlloc *link;
};

static void
selcall(Fn *fn, Ins *i0, Ins *i1, RAlloc **rap)
{
	Ins *i;
	AClass *ac, *a, aret;
	int ca, ni, ns;
	uint stk, off;
	Ref r, r1, r2, reg[2], regcp[2];
	RAlloc *ra;

	ac = alloc((i1-i0) * sizeof ac[0]);
	if (!req(i1->arg[1], R)) {
		assert(rtype(i1->arg[1]) == RAType);
		aclass(&aret, &typ[i1->arg[1].val & AMask]);
		ca = classify(i0, i1, ac, OArg, &aret);
	} else
		ca = classify(i0, i1, ac, OArg, 0);

	for (stk=0, a=&ac[i1-i0]; a>ac;)
		if ((--a)->inmem) {
			assert(a->align <= 4);
			stk += a->size;
			if (a->align == 4)
				stk += stk & 15;
		}
	stk += stk & 15;
	if (stk) {
		r = getcon(-(int64_t)stk, fn);
		emit(OSAlloc, Kl, R, r, R);
	}

	if (!req(i1->arg[1], R)) {
		if (aret.inmem) {
			/* get the return location from eax
			 * it saves one callee-save reg */
			r1 = newtmp("abi", Kl, fn);
			emit(OCopy, Kl, i1->to, TMP(RAX), R);
			ca += 1;
		} else {
			if (aret.size > 8) {
				r = newtmp("abi", Kl, fn);
				regcp[1] = newtmp("abi", aret.cls[1], fn);
				emit(OStorel, 0, R, regcp[1], r);
				emit(OAdd, Kl, r, i1->to, getcon(8, fn));
				chuse(i1->to, +1, fn);
				ca += 1 << (2 * KBASE(aret.cls[1]));
			}
			regcp[0] = newtmp("abi", aret.cls[0], fn);
			emit(OStorel, 0, R, regcp[0], i1->to);
			ca += 1 << (2 * KBASE(aret.cls[0]));
			retr(reg, &aret);
			if (aret.size > 8)
				emit(OCopy, aret.cls[1], regcp[1], reg[1], R);
			emit(OCopy, aret.cls[0], regcp[0], reg[0], R);
			r1 = i1->to;
		}
		/* allocate return pad */
		ra = alloc(sizeof *ra);
		assert(NAlign == 3);
		aret.align -= 2;
		if (aret.align < 0)
			aret.align = 0;
		ra->i.op = OAlloc + aret.align;
		ra->i.cls = Kl;
		ra->i.to = r1;
		ra->i.arg[0] = getcon(aret.size, fn);
		ra->link = (*rap);
		*rap = ra;
	} else {
		ra = 0;
		if (KBASE(i1->cls) == 0) {
			emit(OCopy, i1->cls, i1->to, TMP(RAX), R);
			ca += 1;
		} else {
			emit(OCopy, i1->cls, i1->to, TMP(XMM0), R);
			ca += 1 << 2;
		}
	}
	emit(OCall, i1->cls, R, i1->arg[0], CALL(ca));
	emit(OCopy, Kw, TMP(RAX), getcon((ca >> 8) & 15, fn), R);

	ni = ns = 0;
	if (ra && aret.inmem)
		emit(OCopy, Kl, rarg(Kl, &ni, &ns), ra->i.to, R); /* pass hidden argument */
	for (i=i0, a=ac; i<i1; i++, a++) {
		if (a->inmem)
			continue;
		r1 = rarg(a->cls[0], &ni, &ns);
		if (i->op == OArgc) {
			if (a->size > 8) {
				r2 = rarg(a->cls[1], &ni, &ns);
				r = newtmp("abi", Kl, fn);
				emit(OLoad, a->cls[1], r2, r, R);
				emit(OAdd, Kl, r, i->arg[1], getcon(8, fn));
				chuse(i->arg[1], +1, fn);
			}
			emit(OLoad, a->cls[0], r1, i->arg[1], R);
		} else
			emit(OCopy, i->cls, r1, i->arg[0], R);
	}

	if (!stk)
		return;

	r = newtmp("abi", Kl, fn);
	chuse(r, -1, fn);
	for (i=i0, a=ac, off=0; i<i1; i++, a++) {
		if (!a->inmem)
			continue;
		if (i->op == OArgc) {
			if (a->align == 4)
				off += off & 15;
			blit(r, off, i->arg[1], a->size, fn);
		} else {
			r1 = newtmp("abi", Kl, fn);
			emit(OStorel, 0, R, i->arg[0], r1);
			emit(OAdd, Kl, r1, r, getcon(off, fn));
			chuse(r, +1, fn);
		}
		off += a->size;
	}
	emit(OSAlloc, Kl, r, getcon(stk, fn), R);
}

static void
selpar(Fn *fn, Ins *i0, Ins *i1)
{
	AClass *ac, *a, aret;
	Ins *i;
	int ni, ns, s, al;
	Ref r, r1;

	ac = alloc((i1-i0) * sizeof ac[0]);
	curi = insb;
	ni = ns = 0;

	if (fn->retty >= 0) {
		aclass(&aret, &typ[fn->retty]);
		if (aret.inmem) {
			r = newtmp("abi", Kl, fn);
			*curi++ = (Ins){OCopy, r, {rarg(Kl, &ni, &ns)}, Kl};
			fn->retr = r;
		}
		classify(i0, i1, ac, OPar, &aret);
	} else
		classify(i0, i1, ac, OPar, 0);

	assert(NAlign == 3);

	s = 4;
	for (i=i0, a=ac; i<i1; i++, a++) {
		switch (a->inmem) {
		case 1:
			assert(a->align <= 4);
			if (a->align == 4)
				s = (s+3) & -4;
			fn->tmp[i->to.val].slot = -s; /* HACK! */
			s += a->size;
			continue;
		case 2:
			*curi++ = (Ins){OLoad, i->to, {SLOT(-s)}, i->cls};
			s += 2;
			continue;
		}
		r1 = rarg(a->cls[0], &ni, &ns);
		if (i->op == OParc) {
			r = newtmp("abi", Kl, fn);
			*curi++ = (Ins){OCopy, r, {r1}, Kl};
			a->cls[0] = r.val;
			if (a->size > 8) {
				r1 = rarg(a->cls[1], &ni, &ns);
				r = newtmp("abi", Kl, fn);
				*curi++ = (Ins){OCopy, r, {r1}, Kl};
				a->cls[1] = r.val;
			}
		} else
			*curi++ = (Ins){OCopy, i->to, {r1}, i->cls};
	}
	for (i=i0, a=ac; i<i1; i++, a++) {
		if (i->op != OParc || a->inmem)
			continue;
		assert(NAlign == 3);
		for (al=0; a->align >> (al+2); al++)
			;
		r = TMP(a->cls[0]);
		r1 = i->to;
		*curi++ = (Ins){OAlloc+al, r1, {getcon(a->size, fn)}, Kl};
		*curi++ = (Ins){OStorel, R, {r, r1}, 0};
		if (a->size > 8) {
			r = newtmp("abi", Kl, fn);
			*curi++ = (Ins){OAdd, r, {r1, getcon(8, fn)}, Kl};
			r1 = TMP(a->cls[1]);
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
		[2] [7] = 7, [7] [2] = 7,
		[0] [0] = 4,              /* 4: b + s * i */
		[0] [3] = 4, [3] [0] = 4,
		[2] [3] = 5, [3] [2] = 5, /* 5: o + s * i */
		[0] [2] = 6, [2] [0] = 6, /* 6: o + b */
		[2] [4] = 7, [4] [2] = 7, /* 7: o + b + s * i */
		[0] [5] = 7, [5] [0] = 7,
		[6] [3] = 7, [3] [6] = 7,

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
	case 6: /* o + b */
	case 7: /* o + b + s * i */
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
	int n, al;
	int64_t sz;
	ANum *ainfo;
	RAlloc *ral;

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

	/* lower function calls and returns */
	ral = 0;
	b = fn->start;
	do {
		if (!(b = b->link))
			b = fn->start; /* do it last */
		curi = &insb[NIns];
		selret(b, fn);
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			if ((--i)->op == OCall) {
				for (i0=i; i0>b->ins; i0--)
					if ((i0-1)->op != OArg)
					if ((i0-1)->op != OArgc)
						break;
				selcall(fn, i0, i, &ral);
				i = i0;
				continue;
			}
			assert(i->op != OArg && i->op != OArgc);
			emiti(*i);
		}
		if (b == fn->start)
			for (; ral; ral=ral->link)
				emiti(ral->i);
		b->nins = &insb[NIns] - curi;
		idup(&b->ins, curi, b->nins);
	} while (b != fn->start);

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
		curi = &insb[NIns];
		for (sb=(Blk*[3]){b->s1, b->s2, 0}; *sb; sb++)
			for (p=(*sb)->phi; p; p=p->link) {
				for (a=0; p->blk[a] != b; a++)
					assert(a+1 < p->narg);
				fixarg(&p->arg[a], p->cls, 1, fn);
			}
		memset(ainfo, 0, n * sizeof ainfo[0]);
		anumber(ainfo, b, fn->con);
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
