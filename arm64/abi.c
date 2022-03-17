#include "all.h"

typedef struct Class Class;
typedef struct Insl Insl;
typedef struct Params Params;

enum {
	Cstk = 1, /* pass on the stack */
	Cptr = 2, /* replaced by a pointer */
};

struct Class {
	char class;
	char ishfa;
	struct {
		char base;
		uchar size;
	} hfa;
	uint size;
	Typ *t;
	uchar nreg;
	uchar ngp;
	uchar nfp;
	int reg[4];
	int cls[4];
};

struct Insl {
	Ins i;
	Insl *link;
};

struct Params {
	uint ngp;
	uint nfp;
	uint nstk;
};

static int gpreg[12] = {R0, R1, R2, R3, R4, R5, R6, R7};
static int fpreg[12] = {V0, V1, V2, V3, V4, V5, V6, V7};

/* layout of call's second argument (RCall)
 *
 *         13
 *  29   14 |    9    5   2  0
 *  |0.00|x|x|xxxx|xxxx|xxx|xx|                  range
 *        | |    |    |   |  ` gp regs returned (0..2)
 *        | |    |    |   ` fp regs returned    (0..4)
 *        | |    |    ` gp regs passed          (0..8)
 *        | |     ` fp regs passed              (0..8)
 *        | ` indirect result register x8 used  (0..1)
 *        ` env pointer passed in x9            (0..1)
 */

static int
isfloatv(Typ *t, char *cls)
{
	Field *f;
	uint n;

	for (n=0; n<t->nunion; n++)
		for (f=t->fields[n]; f->type != FEnd; f++)
			switch (f->type) {
			case Fs:
				if (*cls == Kd)
					return 0;
				*cls = Ks;
				break;
			case Fd:
				if (*cls == Ks)
					return 0;
				*cls = Kd;
				break;
			case FTyp:
				if (isfloatv(&typ[f->len], cls))
					break;
				/* fall through */
			default:
				return 0;
			}
	return 1;
}

static void
typclass(Class *c, Typ *t, int *gp, int *fp)
{
	uint64_t sz;
	uint n;

	sz = (t->size + 7) & -8;
	c->t = t;
	c->class = 0;
	c->ngp = 0;
	c->nfp = 0;

	if (t->align > 4)
		err("alignments larger than 16 are not supported");

	if (t->isdark || sz > 16 || sz == 0) {
		/* large structs are replaced by a
		 * pointer to some caller-allocated
		 * memory */
		c->class |= Cptr;
		c->size = 8;
		c->ngp = 1;
		*c->reg = *gp;
		*c->cls = Kl;
		return;
	}

	c->size = sz;
	c->hfa.base = Kx;
	c->ishfa = isfloatv(t, &c->hfa.base);
	c->hfa.size = t->size/(KWIDE(c->hfa.base) ? 8 : 4);

	if (c->ishfa)
		for (n=0; n<c->hfa.size; n++, c->nfp++) {
			c->reg[n] = *fp++;
			c->cls[n] = c->hfa.base;
		}
	else
		for (n=0; n<sz/8; n++, c->ngp++) {
			c->reg[n] = *gp++;
			c->cls[n] = Kl;
		}

	c->nreg = n;
}

static void
sttmps(Ref tmp[], int cls[], uint nreg, Ref mem, Fn *fn)
{
	static int st[] = {
		[Kw] = Ostorew, [Kl] = Ostorel,
		[Ks] = Ostores, [Kd] = Ostored
	};
	uint n;
	uint64_t off;
	Ref r;

	assert(nreg <= 4);
	off = 0;
	for (n=0; n<nreg; n++) {
		tmp[n] = newtmp("abi", cls[n], fn);
		r = newtmp("abi", Kl, fn);
		emit(st[cls[n]], 0, R, tmp[n], r);
		emit(Oadd, Kl, r, mem, getcon(off, fn));
		off += KWIDE(cls[n]) ? 8 : 4;
	}
}

/* todo, may read out of bounds */
static void
ldregs(int reg[], int cls[], int n, Ref mem, Fn *fn)
{
	int i;
	uint64_t off;
	Ref r;

	off = 0;
	for (i=0; i<n; i++) {
		r = newtmp("abi", Kl, fn);
		emit(Oload, cls[i], TMP(reg[i]), r, R);
		emit(Oadd, Kl, r, mem, getcon(off, fn));
		off += KWIDE(cls[i]) ? 8 : 4;
	}
}

static void
selret(Blk *b, Fn *fn)
{
	int j, k, cty;
	Ref r;
	Class cr;

	j = b->jmp.type;

	if (!isret(j) || j == Jret0)
		return;

	r = b->jmp.arg;
	b->jmp.type = Jret0;

	if (j == Jretc) {
		typclass(&cr, &typ[fn->retty], gpreg, fpreg);
		if (cr.class & Cptr) {
			assert(rtype(fn->retr) == RTmp);
			blit0(fn->retr, r, cr.t->size, fn);
			cty = 0;
		} else {
			ldregs(cr.reg, cr.cls, cr.nreg, r, fn);
			cty = (cr.nfp << 2) | cr.ngp;
		}
	} else {
		k = j - Jretw;
		if (KBASE(k) == 0) {
			emit(Ocopy, k, TMP(R0), r, R);
			cty = 1;
		} else {
			emit(Ocopy, k, TMP(V0), r, R);
			cty = 1 << 2;
		}
	}

	b->jmp.arg = CALL(cty);
}

static int
argsclass(Ins *i0, Ins *i1, Class *carg)
{
	int envc, ngp, nfp, *gp, *fp;
	Class *c;
	Ins *i;

	envc = 0;
	gp = gpreg;
	fp = fpreg;
	ngp = 8;
	nfp = 8;
	for (i=i0, c=carg; i<i1; i++, c++)
		switch (i->op) {
		case Opar:
		case Oarg:
			*c->cls = i->cls;
			c->size = 8;
			if (KBASE(i->cls) == 0 && ngp > 0) {
				ngp--;
				*c->reg = *gp++;
				break;
			}
			if (KBASE(i->cls) == 1 && nfp > 0) {
				nfp--;
				*c->reg = *fp++;
				break;
			}
			c->class |= Cstk;
			break;
		case Oparc:
		case Oargc:
			typclass(c, &typ[i->arg[0].val], gp, fp);
			if (c->ngp <= ngp) {
				if (c->nfp <= nfp) {
					ngp -= c->ngp;
					nfp -= c->nfp;
					gp += c->ngp;
					fp += c->nfp;
					break;
				} else
					nfp = 0;
			} else
				ngp = 0;
			c->class |= Cstk;
			break;
		case Opare:
		case Oarge:
			*c->reg = R9;
			*c->cls = Kl;
			envc = 1;
			break;
		case Oargv:
			break;
		default:
			die("unreachable");
		}

	return envc << 14 | (gp-gpreg) << 5 | (fp-fpreg) << 9;
}

bits
arm64_retregs(Ref r, int p[2])
{
	bits b;
	int ngp, nfp;

	assert(rtype(r) == RCall);
	ngp = r.val & 3;
	nfp = (r.val >> 2) & 7;
	if (p) {
		p[0] = ngp;
		p[1] = nfp;
	}
	b = 0;
	while (ngp--)
		b |= BIT(R0+ngp);
	while (nfp--)
		b |= BIT(V0+nfp);
	return b;
}

bits
arm64_argregs(Ref r, int p[2])
{
	bits b;
	int ngp, nfp, x8, x9;

	assert(rtype(r) == RCall);
	ngp = (r.val >> 5) & 15;
	nfp = (r.val >> 9) & 15;
	x8 = (r.val >> 13) & 1;
	x9 = (r.val >> 14) & 1;
	if (p) {
		p[0] = ngp + x8 + x9;
		p[1] = nfp;
	}
	b = 0;
	while (ngp--)
		b |= BIT(R0+ngp);
	while (nfp--)
		b |= BIT(V0+nfp);
	return b | ((bits)x8 << R8) | ((bits)x9 << R9);
}

static void
stkblob(Ref r, Class *c, Fn *fn, Insl **ilp)
{
	Insl *il;
	int al;
	uint64_t sz;

	il = alloc(sizeof *il);
	al = c->t->align - 2; /* NAlign == 3 */
	if (al < 0)
		al = 0;
	sz = c->class & Cptr ? c->t->size : c->size;
	il->i = (Ins){Oalloc+al, Kl, r, {getcon(sz, fn)}};
	il->link = *ilp;
	*ilp = il;
}

static void
selcall(Fn *fn, Ins *i0, Ins *i1, Insl **ilp)
{
	Ins *i;
	Class *ca, *c, cr;
	int cty;
	uint n;
	uint64_t stk, off;
	Ref r, rstk, tmp[4];

	ca = alloc((i1-i0) * sizeof ca[0]);
	cty = argsclass(i0, i1, ca);

	stk = 0;
	for (i=i0, c=ca; i<i1; i++, c++) {
		if (c->class & Cptr) {
			i->arg[0] = newtmp("abi", Kl, fn);
			stkblob(i->arg[0], c, fn, ilp);
			i->op = Oarg;
		}
		if (c->class & Cstk)
			stk += c->size;
	}
	stk += stk & 15;
	rstk = getcon(stk, fn);
	if (stk)
		emit(Oadd, Kl, TMP(SP), TMP(SP), rstk);

	if (!req(i1->arg[1], R)) {
		typclass(&cr, &typ[i1->arg[1].val], gpreg, fpreg);
		stkblob(i1->to, &cr, fn, ilp);
		cty |= (cr.nfp << 2) | cr.ngp;
		if (cr.class & Cptr) {
			/* spill & rega expect calls to be
			 * followed by copies from regs,
			 * so we emit a dummy
			 */
			cty |= 1 << 13 | 1;
			emit(Ocopy, Kw, R, TMP(R0), R);
		} else {
			sttmps(tmp, cr.cls, cr.nreg, i1->to, fn);
			for (n=0; n<cr.nreg; n++) {
				r = TMP(cr.reg[n]);
				emit(Ocopy, cr.cls[n], tmp[n], r, R);
			}
		}
	} else {
		if (KBASE(i1->cls) == 0) {
			emit(Ocopy, i1->cls, i1->to, TMP(R0), R);
			cty |= 1;
		} else {
			emit(Ocopy, i1->cls, i1->to, TMP(V0), R);
			cty |= 1 << 2;
		}
	}

	emit(Ocall, 0, R, i1->arg[0], CALL(cty));

	if (cty & (1 << 13))
		/* struct return argument */
		emit(Ocopy, Kl, TMP(R8), i1->to, R);

	for (i=i0, c=ca; i<i1; i++, c++) {
		if ((c->class & Cstk) != 0)
			continue;
		if (i->op == Oarg || i->op == Oarge)
			emit(Ocopy, *c->cls, TMP(*c->reg), i->arg[0], R);
		if (i->op == Oargc)
			ldregs(c->reg, c->cls, c->nreg, i->arg[1], fn);
	}

	/* populate the stack */
	off = 0;
	for (i=i0, c=ca; i<i1; i++, c++) {
		if ((c->class & Cstk) == 0)
			continue;
		if (i->op == Oarg) {
			r = newtmp("abi", Kl, fn);
			emit(Ostorel, 0, R, i->arg[0], r);
			emit(Oadd, Kl, r, TMP(SP), getcon(off, fn));
		}
		if (i->op == Oargc)
			blit(TMP(SP), off, i->arg[1], 0, c->size, fn);
		off += c->size;
	}
	if (stk)
		emit(Osub, Kl, TMP(SP), TMP(SP), rstk);

	for (i=i0, c=ca; i<i1; i++, c++)
		if (c->class & Cptr)
			blit0(i->arg[0], i->arg[1], c->t->size, fn);
}

static Params
selpar(Fn *fn, Ins *i0, Ins *i1)
{
	Class *ca, *c, cr;
	Insl *il;
	Ins *i;
	int n, s, cty;
	Ref r, tmp[16], *t;

	ca = alloc((i1-i0) * sizeof ca[0]);
	curi = &insb[NIns];

	cty = argsclass(i0, i1, ca);
	fn->reg = arm64_argregs(CALL(cty), 0);

	il = 0;
	t = tmp;
	for (i=i0, c=ca; i<i1; i++, c++) {
		if (i->op != Oparc || (c->class & (Cptr|Cstk)))
			continue;
		sttmps(t, c->cls, c->nreg, i->to, fn);
		stkblob(i->to, c, fn, &il);
		t += c->nreg;
	}
	for (; il; il=il->link)
		emiti(il->i);

	if (fn->retty >= 0) {
		typclass(&cr, &typ[fn->retty], gpreg, fpreg);
		if (cr.class & Cptr) {
			fn->retr = newtmp("abi", Kl, fn);
			emit(Ocopy, Kl, fn->retr, TMP(R8), R);
			fn->reg |= BIT(R8);
		}
	}

	t = tmp;
	s = 2;
	for (i=i0, c=ca; i<i1; i++, c++)
		if (i->op == Oparc && !(c->class & Cptr)) {
			if (c->class & Cstk) {
				fn->tmp[i->to.val].slot = -s;
				s += c->size / 8;
			} else
				for (n=0; n<c->nreg; n++) {
					r = TMP(c->reg[n]);
					emit(Ocopy, c->cls[n], *t++, r, R);
				}
		} else if (c->class & Cstk) {
			emit(Oload, *c->cls, i->to, SLOT(-s), R);
			s++;
		} else {
			emit(Ocopy, *c->cls, i->to, TMP(*c->reg), R);
		}

	return (Params){
		.nstk = s - 2,
		.ngp = (cty >> 5) & 15,
		.nfp = (cty >> 9) & 15
	};
}

static Blk *
split(Fn *fn, Blk *b)
{
	Blk *bn;

	++fn->nblk;
	bn = blknew();
	bn->nins = &insb[NIns] - curi;
	idup(&bn->ins, curi, bn->nins);
	curi = &insb[NIns];
	bn->visit = ++b->visit;
	(void)!snprintf(bn->name, NString, "%s.%d", b->name, b->visit);
	bn->loop = b->loop;
	bn->link = b->link;
	b->link = bn;
	return bn;
}

static void
chpred(Blk *b, Blk *bp, Blk *bp1)
{
	Phi *p;
	uint a;

	for (p=b->phi; p; p=p->link) {
		for (a=0; p->blk[a]!=bp; a++)
			assert(a+1<p->narg);
		p->blk[a] = bp1;
	}
}

static void
selvaarg(Fn *fn, Blk *b, Ins *i)
{
	Ref loc, lreg, lstk, nr, r0, r1, c8, c16, c24, c28, ap;
	Blk *b0, *bstk, *breg;
	int isgp;

	c8 = getcon(8, fn);
	c16 = getcon(16, fn);
	c24 = getcon(24, fn);
	c28 = getcon(28, fn);
	ap = i->arg[0];
	isgp = KBASE(i->cls) == 0;

	/* @b [...]
	       r0 =l add ap, (24 or 28)
	       nr =l loadsw r0
	       r1 =w csltw nr, 0
	       jnz r1, @breg, @bstk
	   @breg
	       r0 =l add ap, (8 or 16)
	       r1 =l loadl r0
	       lreg =l add r1, nr
	       r0 =w add nr, (8 or 16)
	       r1 =l add ap, (24 or 28)
	       storew r0, r1
	   @bstk
	       lstk =l loadl ap
	       r0 =l add lstk, 8
	       storel r0, ap
	   @b0
	       %loc =l phi @breg %lreg, @bstk %lstk
	       i->to =(i->cls) load %loc
	*/

	loc = newtmp("abi", Kl, fn);
	emit(Oload, i->cls, i->to, loc, R);
	b0 = split(fn, b);
	b0->jmp = b->jmp;
	b0->s1 = b->s1;
	b0->s2 = b->s2;
	if (b->s1)
		chpred(b->s1, b, b0);
	if (b->s2 && b->s2 != b->s1)
		chpred(b->s2, b, b0);

	lreg = newtmp("abi", Kl, fn);
	nr = newtmp("abi", Kl, fn);
	r0 = newtmp("abi", Kw, fn);
	r1 = newtmp("abi", Kl, fn);
	emit(Ostorew, Kw, R, r0, r1);
	emit(Oadd, Kl, r1, ap, isgp ? c24 : c28);
	emit(Oadd, Kw, r0, nr, isgp ? c8 : c16);
	r0 = newtmp("abi", Kl, fn);
	r1 = newtmp("abi", Kl, fn);
	emit(Oadd, Kl, lreg, r1, nr);
	emit(Oload, Kl, r1, r0, R);
	emit(Oadd, Kl, r0, ap, isgp ? c8 : c16);
	breg = split(fn, b);
	breg->jmp.type = Jjmp;
	breg->s1 = b0;

	lstk = newtmp("abi", Kl, fn);
	r0 = newtmp("abi", Kl, fn);
	emit(Ostorel, Kw, R, r0, ap);
	emit(Oadd, Kl, r0, lstk, c8);
	emit(Oload, Kl, lstk, ap, R);
	bstk = split(fn, b);
	bstk->jmp.type = Jjmp;
	bstk->s1 = b0;

	b0->phi = alloc(sizeof *b0->phi);
	*b0->phi = (Phi){
		.cls = Kl, .to = loc,
		.narg = 2,
		.blk = vnew(2, sizeof b0->phi->blk[0], Pfn),
		.arg = vnew(2, sizeof b0->phi->arg[0], Pfn),
	};
	b0->phi->blk[0] = bstk;
	b0->phi->blk[1] = breg;
	b0->phi->arg[0] = lstk;
	b0->phi->arg[1] = lreg;
	r0 = newtmp("abi", Kl, fn);
	r1 = newtmp("abi", Kw, fn);
	b->jmp.type = Jjnz;
	b->jmp.arg = r1;
	b->s1 = breg;
	b->s2 = bstk;
	emit(Ocmpw+Cislt, Kw, r1, nr, CON_Z);
	emit(Oloadsw, Kl, nr, r0, R);
	emit(Oadd, Kl, r0, ap, isgp ? c24 : c28);
}

static void
selvastart(Fn *fn, Params p, Ref ap)
{
	Ref r0, r1, rsave;

	rsave = newtmp("abi", Kl, fn);

	r0 = newtmp("abi", Kl, fn);
	emit(Ostorel, Kw, R, r0, ap);
	emit(Oadd, Kl, r0, rsave, getcon(p.nstk*8 + 192, fn));

	r0 = newtmp("abi", Kl, fn);
	r1 = newtmp("abi", Kl, fn);
	emit(Ostorel, Kw, R, r1, r0);
	emit(Oadd, Kl, r1, rsave, getcon(64, fn));
	emit(Oadd, Kl, r0, ap, getcon(8, fn));

	r0 = newtmp("abi", Kl, fn);
	r1 = newtmp("abi", Kl, fn);
	emit(Ostorel, Kw, R, r1, r0);
	emit(Oadd, Kl, r1, rsave, getcon(192, fn));
	emit(Oaddr, Kl, rsave, SLOT(-1), R);
	emit(Oadd, Kl, r0, ap, getcon(16, fn));

	r0 = newtmp("abi", Kl, fn);
	emit(Ostorew, Kw, R, getcon((p.ngp-8)*8, fn), r0);
	emit(Oadd, Kl, r0, ap, getcon(24, fn));

	r0 = newtmp("abi", Kl, fn);
	emit(Ostorew, Kw, R, getcon((p.nfp-8)*16, fn), r0);
	emit(Oadd, Kl, r0, ap, getcon(28, fn));
}

void
arm64_abi(Fn *fn)
{
	Blk *b;
	Ins *i, *i0, *ip;
	Insl *il;
	int n;
	Params p;

	for (b=fn->start; b; b=b->link)
		b->visit = 0;

	/* lower parameters */
	for (b=fn->start, i=b->ins; i<&b->ins[b->nins]; i++)
		if (!ispar(i->op))
			break;
	p = selpar(fn, b->ins, i);
	n = b->nins - (i - b->ins) + (&insb[NIns] - curi);
	i0 = alloc(n * sizeof(Ins));
	ip = icpy(ip = i0, curi, &insb[NIns] - curi);
	ip = icpy(ip, i, &b->ins[b->nins] - i);
	b->nins = n;
	b->ins = i0;

	/* lower calls, returns, and vararg instructions */
	il = 0;
	b = fn->start;
	do {
		if (!(b = b->link))
			b = fn->start; /* do it last */
		if (b->visit)
			continue;
		curi = &insb[NIns];
		selret(b, fn);
		for (i=&b->ins[b->nins]; i!=b->ins;)
			switch ((--i)->op) {
			default:
				emiti(*i);
				break;
			case Ocall:
				for (i0=i; i0>b->ins; i0--)
					if (!isarg((i0-1)->op))
						break;
				selcall(fn, i0, i, &il);
				i = i0;
				break;
			case Ovastart:
				selvastart(fn, p, i->arg[0]);
				break;
			case Ovaarg:
				selvaarg(fn, b, i);
				break;
			case Oarg:
			case Oargc:
				die("unreachable");
			}
		if (b == fn->start)
			for (; il; il=il->link)
				emiti(il->i);
		b->nins = &insb[NIns] - curi;
		idup(&b->ins, curi, b->nins);
	} while (b != fn->start);

	if (debug['A']) {
		fprintf(stderr, "\n> After ABI lowering:\n");
		printfn(fn, stderr);
	}
}
