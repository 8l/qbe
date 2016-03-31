#include "all.h"

typedef struct AClass AClass;
typedef struct RAlloc RAlloc;

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
		chuse(rsrc, +1, fn);
		chuse(rstk, +1, fn);
	}
}

static int
retr(Ref reg[2], AClass *aret)
{
	static int retreg[2][2] = {{RAX, RDX}, {XMM0, XMM0+1}};
	int n, k, ca, nr[2];

	nr[0] = nr[1] = 0;
	ca = 0;
	for (n=0; aret->cls[n]>=0 && n<2; n++) {
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
			chuse(fn->retr, +1, fn);
			blit(fn->retr, 0, r0, aret.size, fn);
			ca = 1;
		} else {
			ca = retr(reg, &aret);
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
retregs(Ref r, int p[2])
{
	bits b;
	int ni, nf;

	assert(rtype(r) == RACall);
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

	assert(rtype(r) == RACall);
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
		/* specific to NAlign == 3 */
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

	/* specific to NAlign == 3 */

	s = 4;
	for (i=i0, a=ac; i<i1; i++, a++) {
		switch (a->inmem) {
		case 1:
			assert(a->align <= 4);
			if (a->align == 4)
				s = (s+3) & -4;
			fn->tmp[i->to.val].slot = -s; /* HACK! */
			s += a->size / 4;
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
	n = b->nins - (i - b->ins) + (curi - insb);
	i0 = alloc(n * sizeof(Ins));
	ip = icpy(ip = i0, insb, curi - insb);
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
