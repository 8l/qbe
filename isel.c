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
	case FCo:  return ICxnp;
	case FCuo: return ICxp;
	}
}

static int
iscmp(int op, int *pk, int *pc)
{
	int k, c;

	if (Ocmpw <= op && op <= Ocmpw1) {
		c = op - Ocmpw;
		k = Kw;
	}
	else if (Ocmpl <= op && op <= Ocmpl1) {
		c = op - Ocmpl;
		k = Kl;
	}
	else if (Ocmps <= op && op <= Ocmps1) {
		c = fcmptoi(op - Ocmps);
		k = Ks;
	}
	else if (Ocmpd <= op && op <= Ocmpd1) {
		c = fcmptoi(op - Ocmpd);
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
		emit(Ocopy, Kl, r1, r0, R);
	}
	else if (s != -1) {
		/* load fast locals' addresses into
		 * temporaries right before the
		 * instruction
		 */
		r1 = newtmp("isel", Kl, fn);
		emit(Oaddr, Kl, r1, SLOT(s), R);
	}
	*r = r1;
}

static void
seladdr(Ref *r, ANum *an, Fn *fn)
{
	Addr a;
	Ref r0;

	r0 = *r;
	if (rtype(r0) == RTmp) {
		amatch(&a, r0, an, fn, 1);
		if (req(a.base, R) || req(a.base, r0))
			return;
		chuse(r0, -1, fn);
		vgrow(&fn->mem, ++fn->nmem);
		fn->mem[fn->nmem-1] = a;
		chuse(a.base, +1, fn);
		chuse(a.index, +1, fn);
		*r = MEM(fn->nmem-1);
	}
}

static void
selcmp(Ref arg[2], int k, Fn *fn)
{
	Ref r, *iarg;

	if (rtype(arg[0]) == RCon) {
		r = arg[1];
		arg[1] = arg[0];
		arg[0] = r;
	}
	assert(rtype(arg[0]) != RCon);
	emit(Oxcmp, k, R, arg[1], arg[0]);
	iarg = curi->arg;
	fixarg(&iarg[0], k, 0, fn);
	fixarg(&iarg[1], k, 0, fn);
}

static void
sel(Ins i, ANum *an, Fn *fn)
{
	Ref r0, r1, *iarg;
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
	case Odiv:
	case Orem:
	case Oudiv:
	case Ourem:
		if (i.op == Odiv || i.op == Oudiv)
			r0 = TMP(RAX), r1 = TMP(RDX);
		else
			r0 = TMP(RDX), r1 = TMP(RAX);
		emit(Ocopy, k, i.to, r0, R);
		emit(Ocopy, k, R, r1, R);
		if (rtype(i.arg[1]) == RCon) {
			/* immediates not allowed for
			 * divisions in x86
			 */
			r0 = newtmp("isel", k, fn);
		} else
			r0 = i.arg[1];
		if (fn->tmp[r0.val].slot != -1)
			err("unlikely argument %%%s in %s",
				fn->tmp[r0.val].name, opdesc[i.op].name);
		if (i.op == Odiv || i.op == Orem) {
			emit(Oxidiv, k, R, r0, R);
			emit(Osign, k, TMP(RDX), TMP(RAX), R);
		} else {
			emit(Oxdiv, k, R, r0, R);
			emit(Ocopy, k, TMP(RDX), CON_Z, R);
		}
		emit(Ocopy, k, TMP(RAX), i.arg[0], R);
		fixarg(&curi->arg[0], k, 0, fn);
		if (rtype(i.arg[1]) == RCon)
			emit(Ocopy, k, r0, i.arg[1], R);
		break;
	case Osar:
	case Oshr:
	case Oshl:
		if (rtype(i.arg[1]) == RCon)
			goto Emit;
		r0 = i.arg[1];
		i.arg[1] = TMP(RCX);
		emit(Ocopy, Kw, R, TMP(RCX), R);
		emiti(i);
		emit(Ocopy, Kw, TMP(RCX), r0, R);
		break;
	case Onop:
		break;
	case Ostored:
	case Ostores:
	case Ostorel:
	case Ostorew:
	case Ostoreh:
	case Ostoreb:
		if (rtype(i.arg[0]) == RCon) {
			if (i.op == Ostored)
				i.op = Ostorel;
			if (i.op == Ostores)
				i.op = Ostorew;
		}
		seladdr(&i.arg[1], an, fn);
		goto Emit;
	case_Oload:
		seladdr(&i.arg[0], an, fn);
		goto Emit;
	case Ocall:
	case Osalloc:
	case Ocopy:
	case Oadd:
	case Osub:
	case Omul:
	case Oand:
	case Oor:
	case Oxor:
	case Oxtest:
	case Ostosi:
	case Odtosi:
	case Oswtof:
	case Osltof:
	case Oexts:
	case Otruncd:
	case Ocast:
	case_OExt:
Emit:
		emiti(i);
		iarg = curi->arg;
		fixarg(&iarg[0], argcls(&i, 0), 0, fn);
		fixarg(&iarg[1], argcls(&i, 1), 0, fn);
		break;
	case Oalloc:
	case Oalloc+1:
	case Oalloc+2: /* == Oalloc1 */
		/* we need to make sure
		 * the stack remains aligned
		 * (rsp = 0) mod 16
		 */
		if (rtype(i.arg[0]) == RCon) {
			sz = fn->con[i.arg[0].val].bits.i;
			if (sz < 0 || sz >= INT_MAX-15)
				err("invalid alloc size %"PRId64, sz);
			sz = (sz + 15)  & -16;
			emit(Osalloc, Kl, i.to, getcon(sz, fn), R);
		} else {
			/* r0 = (i.arg[0] + 15) & -16 */
			r0 = newtmp("isel", Kl, fn);
			r1 = newtmp("isel", Kl, fn);
			emit(Osalloc, Kl, i.to, r0, R);
			emit(Oand, Kl, r0, r1, getcon(-16, fn));
			emit(Oadd, Kl, r1, i.arg[0], getcon(15, fn));
			if (fn->tmp[i.arg[0].val].slot != -1)
				err("unlikely argument %%%s in %s",
					fn->tmp[i.arg[0].val].name, opdesc[i.op].name);
		}
		break;
	default:
		if (isext(i.op))
			goto case_OExt;
		if (isload(i.op))
			goto case_Oload;
		if (iscmp(i.op, &kc, &x)) {
			if (rtype(i.arg[0]) == RCon)
				x = icmpop(x);
			emit(Oxset+x, k, i.to, R, R);
			selcmp(i.arg, kc, fn);
			break;
		}
		die("unknown instruction %s", opdesc[i.op].name);
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
	Tmp *t;

	if (b->jmp.type == Jret0 || b->jmp.type == Jjmp)
		return;
	assert(b->jmp.type == Jjnz);
	r = b->jmp.arg;
	t = &fn->tmp[r.val];
	b->jmp.arg = R;
	assert(!req(r, R) && rtype(r) != RCon);
	if (b->s1 == b->s2) {
		chuse(r, -1, fn);
		b->jmp.type = Jjmp;
		b->s2 = 0;
		return;
	}
	fi = flagi(b->ins, &b->ins[b->nins]);
	if (fi && req(fi->to, r)) {
		if (iscmp(fi->op, &k, &c)) {
			if (rtype(fi->arg[0]) == RCon)
				c = icmpop(c);
			b->jmp.type = Jxjc + c;
			if (t->nuse == 1) {
				selcmp(fi->arg, k, fn);
				*fi = (Ins){.op = Onop};
			}
			return;
		}
		if (fi->op == Oand && t->nuse == 1
		&& (rtype(fi->arg[0]) == RTmp ||
		    rtype(fi->arg[1]) == RTmp)) {
			fi->op = Oxtest;
			fi->to = R;
			b->jmp.type = Jxjc + ICne;
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
		if (t->nuse == 1)
			emit(Ocopy, Kw, R, r, R);
		b->jmp.type = Jxjc + ICne;
		return;
	}
	selcmp((Ref[2]){r, CON_Z}, Kw, fn); /* todo, add long branch if non-zero */
	b->jmp.type = Jxjc + ICne;
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
		if (i->op != Oadd && i->op != Omul)
			continue;
		a1 = aref(i->arg[0], ai);
		a2 = aref(i->arg[1], ai);
		t1 = a1 != 1 && a1 != 2;
		t2 = a2 != 1 && a2 != 2;
		if (i->op == Oadd) {
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
	for (al=Oalloc, n=4; al<=Oalloc1; al++, n*=2)
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
				*i = (Ins){.op = Onop};
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
		for (n=0; n<fn->ntmp; ++n) {
			if (strcmp(fn->tmp[n].name, "i") == 0)
				fprintf(stderr, ">> nuse for i: %d\n", fn->tmp[n].nuse);
		}
	}
}
