#include "all.h"
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
	default:   die("invalid fp comparison %d", fc);
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
	default:
		die("invalid constant");
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
		a.offset.local = 1;
		n = stashfp(fn->con[r0.val].bits.i, KWIDE(k));
		sprintf(a.offset.label, "fp%d", n);
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
	fixarg(&curi->arg[1], k, 0, fn);
}

static void
sel(Ins i, ANum *an, Fn *fn)
{
	Ref r0, r1;
	int x, k, kc;
	int64_t sz;
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
	case OStores:
	case OStorel:
	case OStorew:
	case OStoreh:
	case OStoreb:
		if (rtype(i.arg[0]) == RCon) {
			if (i.op == OStored)
				i.op = OStorel;
			if (i.op == OStores)
				i.op = OStorew;
		}
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
			sz = fn->con[i.arg[0].val].bits.i;
			if (sz < 0 || sz >= INT_MAX-15)
				err("invalid alloc size %"PRId64, sz);
			sz = (sz + 15)  & -16;
			emit(OSAlloc, Kl, i.to, getcon(sz, fn), R);
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
		die("unknown instruction");
	}

	while (i0 > curi && --i0) {
		assert(rslot(i0->arg[0], fn) == -1);
		assert(rslot(i0->arg[1], fn) == -1);
	}
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
	assert(!req(r, R) && rtype(r) != RCon);
	if (b->s1 == b->s2) {
		b->jmp.type = JJmp;
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
aref(Ref r, ANum *ai)
{
	switch (rtype(r)) {
	case RCon:
		return 2;
	case RTmp:
		return ai[r.val].n;
	default:
		die("constant or temporary expected");
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
	default:
		die("unreachable");
	}
}

/* instruction selection
 * requires use counts (as given by parsing)
 */
void
isel(Fn *fn)
{
	Blk *b, **sb;
	Ins *i;
	Phi *p;
	uint a;
	int n, al;
	int64_t sz;
	ANum *ainfo;

	/* assign slots to fast allocs */
	b = fn->start;
	/* specific to NAlign == 3 */ /* or change n=4 and sz /= 4 below */
	for (al=OAlloc, n=4; al<=OAlloc1; al++, n*=2)
		for (i=b->ins; i-b->ins < b->nins; i++)
			if (i->op == al) {
				if (rtype(i->arg[0]) != RCon)
					break;
				sz = fn->con[i->arg[0].val].bits.i;
				if (sz < 0 || sz >= INT_MAX-15)
					err("invalid alloc size %"PRId64, sz);
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
