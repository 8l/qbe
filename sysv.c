#include "all.h"

typedef struct AClass AClass;
typedef struct RAlloc RAlloc;

struct AClass {
	int inmem;
	int align;
	uint size;
	int cls[2];
	Ref ref[2];
};

struct RAlloc {
	Ins i;
	RAlloc *link;
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

	if (t->dark || sz > 16 || sz == 0) {
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
			if (t->seg[s].ispad) {
				/* don't change anything */
			}
			else if (t->seg[s].isflt) {
				if (cls == -1)
					cls = Kd;
			}
			else
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
	}
}

static int
retr(Ref reg[2], AClass *aret)
{
	static int retreg[2][2] = {{RAX, RDX}, {XMM0, XMM0+1}};
	int n, k, ca, nr[2];

	nr[0] = nr[1] = 0;
	ca = 0;
	for (n=0; (uint)n*8<aret->size; n++) {
		k = KBASE(aret->cls[n]);
		reg[n] = TMP(retreg[k][nr[k]++]);
		ca += 1 << (2 * k);
	}
	return ca;
}

static void
selret(Blk *b, Fn *fn)
{
	int j, k, ca;
	Ref r, r0, reg[2];
	AClass aret;

	j = b->jmp.type;

	if (!isret(j) || j == JRet0)
		return;

	r0 = b->jmp.arg;
	b->jmp.type = JRet0;

	if (j == JRetc) {
		aclass(&aret, &typ[fn->retty]);
		if (aret.inmem) {
			assert(rtype(fn->retr) == RTmp);
			emit(OCopy, Kl, TMP(RAX), fn->retr, R);
			blit(fn->retr, 0, r0, aret.size, fn);
			ca = 1;
		} else {
			ca = retr(reg, &aret);
			if (aret.size > 8) {
				r = newtmp("abi", Kl, fn);
				emit(OLoad, Kl, reg[1], r, R);
				emit(OAdd, Kl, r, r0, getcon(8, fn));
			}
			emit(OLoad, Kl, reg[0], r0, R);
		}
	} else {
		k = j - JRetw;
		if (KBASE(k) == 0) {
			emit(OCopy, k, TMP(RAX), r0, R);
			ca = 1;
		} else {
			emit(OCopy, k, TMP(XMM0), r0, R);
			ca = 1 << 2;
		}
	}

	b->jmp.arg = CALL(ca);
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
			for (n=0; (uint)n*8<a->size; n++)
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
retregs(Ref r, int p[2])
{
	bits b;
	int ni, nf;

	assert(rtype(r) == RCall);
	b = 0;
	ni = r.val & 3;
	nf = (r.val >> 2) & 3;
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
argregs(Ref r, int p[2])
{
	bits b;
	int j, ni, nf;

	assert(rtype(r) == RCall);
	b = 0;
	ni = (r.val >> 4) & 15;
	nf = (r.val >> 8) & 15;
	for (j=0; j<ni; j++)
		b |= BIT(rsave[j]);
	for (j=0; j<nf; j++)
		b |= BIT(XMM0+j);
	if (p) {
		p[0] = ni + 1;
		p[1] = nf;
	}
	return b | BIT(RAX);
}

static Ref
rarg(int ty, int *ni, int *ns)
{
	if (KBASE(ty) == 0)
		return TMP(rsave[(*ni)++]);
	else
		return TMP(XMM0 + (*ns)++);
}

static void
selcall(Fn *fn, Ins *i0, Ins *i1, RAlloc **rap)
{
	Ins *i;
	AClass *ac, *a, aret;
	int ca, ni, ns, al;
	uint stk, off;
	Ref r, r1, r2, reg[2];
	RAlloc *ra;

	ac = alloc((i1-i0) * sizeof ac[0]);
	if (!req(i1->arg[1], R)) {
		assert(rtype(i1->arg[1]) == RType);
		aclass(&aret, &typ[i1->arg[1].val]);
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
				aret.ref[1] = newtmp("abi", aret.cls[1], fn);
				emit(OStorel, 0, R, aret.ref[1], r);
				emit(OAdd, Kl, r, i1->to, getcon(8, fn));
			}
			aret.ref[0] = newtmp("abi", aret.cls[0], fn);
			emit(OStorel, 0, R, aret.ref[0], i1->to);
			ca += retr(reg, &aret);
			if (aret.size > 8)
				emit(OCopy, aret.cls[1], aret.ref[1], reg[1], R);
			emit(OCopy, aret.cls[0], aret.ref[0], reg[0], R);
			r1 = i1->to;
		}
		/* allocate return pad */
		ra = alloc(sizeof *ra);
		/* specific to NAlign == 3 */
		al = aret.align >= 2 ? aret.align - 2 : 0;
		ra->i = (Ins){OAlloc+al, r1, {getcon(aret.size, fn)}, Kl};
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
			}
			emit(OLoad, a->cls[0], r1, i->arg[1], R);
		} else
			emit(OCopy, i->cls, r1, i->arg[0], R);
	}

	if (!stk)
		return;

	r = newtmp("abi", Kl, fn);
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
	Ref r;

	ac = alloc((i1-i0) * sizeof ac[0]);
	curi = &insb[NIns];
	ni = ns = 0;

	if (fn->retty >= 0) {
		aclass(&aret, &typ[fn->retty]);
		classify(i0, i1, ac, OPar, &aret);
	} else
		classify(i0, i1, ac, OPar, 0);

	for (i=i0, a=ac; i<i1; i++, a++) {
		if (i->op != OParc || a->inmem)
			continue;
		if (a->size > 8) {
			r = newtmp("abi", Kl, fn);
			a->ref[1] = newtmp("abi", Kl, fn);
			emit(OStorel, 0, R, a->ref[1], r);
			emit(OAdd, Kl, r, i->to, getcon(8, fn));
		}
		a->ref[0] = newtmp("abi", Kl, fn);
		emit(OStorel, 0, R, a->ref[0], i->to);
		/* specific to NAlign == 3 */
		al = a->align >= 2 ? a->align - 2 : 0;
		emit(OAlloc+al, Kl, i->to, getcon(a->size, fn), R);
	}

	if (fn->retty >= 0 && aret.inmem) {
		r = newtmp("abi", Kl, fn);
		emit(OCopy, Kl, r, rarg(Kl, &ni, &ns), R);
		fn->retr = r;
	}

	for (i=i0, a=ac, s=4; i<i1; i++, a++) {
		switch (a->inmem) {
		case 1:
			assert(a->align <= 4);
			if (a->align == 4)
				s = (s+3) & -4;
			fn->tmp[i->to.val].slot = -s;
			s += a->size / 4;
			continue;
		case 2:
			emit(OLoad, i->cls, i->to, SLOT(-s), R);
			s += 2;
			continue;
		}
		r = rarg(a->cls[0], &ni, &ns);
		if (i->op == OParc) {
			emit(OCopy, Kl, a->ref[0], r, R);
			if (a->size > 8) {
				r = rarg(a->cls[1], &ni, &ns);
				emit(OCopy, Kl, a->ref[1], r, R);
			}
		} else
			emit(OCopy, i->cls, i->to, r, R);
	}
}

void
abi(Fn *fn)
{
	Blk *b;
	Ins *i, *i0, *ip;
	RAlloc *ral;
	int n;

	/* lower arguments */
	for (b=fn->start, i=b->ins; i-b->ins < b->nins; i++)
		if (i->op != OPar && i->op != OParc)
			break;
	selpar(fn, b->ins, i);
	n = b->nins - (i - b->ins) + (&insb[NIns] - curi);
	i0 = alloc(n * sizeof(Ins));
	ip = icpy(ip = i0, curi, &insb[NIns] - curi);
	ip = icpy(ip, i, &b->ins[b->nins] - i);
	b->nins = n;
	b->ins = i0;

	/* lower calls and returns */
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
		fprintf(stderr, "\n> After ABI lowering:\n");
		printfn(fn, stderr);
	}
}
