#include "all.h"

/* the risc-v lp64d abi */

typedef struct Class Class;
typedef struct Insl Insl;
typedef struct Params Params;

enum {
	Cptr  = 1, /* replaced by a pointer */
	Cstk1 = 2, /* pass first XLEN on the stack */
	Cstk2 = 4, /* pass second XLEN on the stack */
	Cstk = Cstk1 | Cstk2,
	Cfpint = 8, /* float passed like integer */
};

struct Class {
	char class;
	Typ *type;
	int reg[2];
	int cls[2];
	int off[2];
	char ngp; /* only valid after typclass() */
	char nfp; /* ditto */
	char nreg;
};

struct Insl {
	Ins i;
	Insl *link;
};

struct Params {
	int ngp;
	int nfp;
	int stk; /* stack offset for varargs */
};

static int gpreg[10] = {A0, A1, A2, A3, A4, A5, A6, A7};
static int fpreg[10] = {FA0, FA1, FA2, FA3, FA4, FA5, FA6, FA7};

/* layout of call's second argument (RCall)
 *
 *  29   12    8    4  2  0
 *  |0.00|x|xxxx|xxxx|xx|xx|                  range
 *        |   |    |  |  ` gp regs returned (0..2)
 *        |   |    |  ` fp regs returned    (0..2)
 *        |   |    ` gp regs passed         (0..8)
 *        |    ` fp regs passed             (0..8)
 *        ` env pointer passed in t5        (0..1)
 */

bits
rv64_retregs(Ref r, int p[2])
{
	bits b;
	int ngp, nfp;

	assert(rtype(r) == RCall);
	ngp = r.val & 3;
	nfp = (r.val >> 2) & 3;
	if (p) {
		p[0] = ngp;
		p[1] = nfp;
	}
	b = 0;
	while (ngp--)
		b |= BIT(A0+ngp);
	while (nfp--)
		b |= BIT(FA0+nfp);
	return b;
}

bits
rv64_argregs(Ref r, int p[2])
{
	bits b;
	int ngp, nfp, t5;

	assert(rtype(r) == RCall);
	ngp = (r.val >> 4) & 15;
	nfp = (r.val >> 8) & 15;
	t5 = (r.val >> 12) & 1;
	if (p) {
		p[0] = ngp + t5;
		p[1] = nfp;
	}
	b = 0;
	while (ngp--)
		b |= BIT(A0+ngp);
	while (nfp--)
		b |= BIT(FA0+nfp);
	return b | ((bits)t5 << T5);
}

static int
fpstruct(Typ *t, int off, Class *c)
{
	Field *f;
	int n;

	if (t->isunion)
		return -1;

	for (f=*t->fields; f->type != FEnd; f++)
		if (f->type == FPad)
			off += f->len;
		else if (f->type == FTyp) {
			if (fpstruct(&typ[f->len], off, c) == -1)
				return -1;
		}
		else {
			n = c->nfp + c->ngp;
			if (n == 2)
				return -1;
			switch (f->type) {
			default: die("unreachable");
			case Fb:
			case Fh:
			case Fw: c->cls[n] = Kw; c->ngp++; break;
			case Fl: c->cls[n] = Kl; c->ngp++; break;
			case Fs: c->cls[n] = Ks; c->nfp++; break;
			case Fd: c->cls[n] = Kd; c->nfp++; break;
			}
			c->off[n] = off;
			off += f->len;
		}

	return c->nfp;
}

static void
typclass(Class *c, Typ *t, int fpabi, int *gp, int *fp)
{
	uint n;
	int i;

	c->type = t;
	c->class = 0;
	c->ngp = 0;
	c->nfp = 0;

	if (t->align > 4)
		err("alignments larger than 16 are not supported");

	if (t->isdark || t->size > 16 || t->size == 0) {
		/* large structs are replaced by a
		 * pointer to some caller-allocated
		 * memory
		 */
		c->class |= Cptr;
		*c->cls = Kl;
		*c->off = 0;
		c->ngp = 1;
	}
	else if (!fpabi || fpstruct(t, 0, c) <= 0) {
		for (n=0; 8*n<t->size; n++) {
			c->cls[n] = Kl;
			c->off[n] = 8*n;
		}
		c->nfp = 0;
		c->ngp = n;
	}

	c->nreg = c->nfp + c->ngp;
	for (i=0; i<c->nreg; i++)
		if (KBASE(c->cls[i]) == 0)
			c->reg[i] = *gp++;
		else
			c->reg[i] = *fp++;
}

static void
sttmps(Ref tmp[], int ntmp, Class *c, Ref mem, Fn *fn)
{
	static int st[] = {
		[Kw] = Ostorew, [Kl] = Ostorel,
		[Ks] = Ostores, [Kd] = Ostored
	};
	int i;
	Ref r;

	assert(ntmp > 0);
	assert(ntmp <= 2);
	for (i=0; i<ntmp; i++) {
		tmp[i] = newtmp("abi", c->cls[i], fn);
		r = newtmp("abi", Kl, fn);
		emit(st[c->cls[i]], 0, R, tmp[i], r);
		emit(Oadd, Kl, r, mem, getcon(c->off[i], fn));
	}
}

static void
ldregs(Class *c, Ref mem, Fn *fn)
{
	int i;
	Ref r;

	for (i=0; i<c->nreg; i++) {
		r = newtmp("abi", Kl, fn);
		emit(Oload, c->cls[i], TMP(c->reg[i]), r, R);
		emit(Oadd, Kl, r, mem, getcon(c->off[i], fn));
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
		typclass(&cr, &typ[fn->retty], 1, gpreg, fpreg);
		if (cr.class & Cptr) {
			assert(rtype(fn->retr) == RTmp);
			blit0(fn->retr, r, cr.type->size, fn);
			cty = 0;
		} else {
			ldregs(&cr, r, fn);
			cty = (cr.nfp << 2) | cr.ngp;
		}
	} else {
		k = j - Jretw;
		if (KBASE(k) == 0) {
			emit(Ocopy, k, TMP(A0), r, R);
			cty = 1;
		} else {
			emit(Ocopy, k, TMP(FA0), r, R);
			cty = 1 << 2;
		}
	}

	b->jmp.arg = CALL(cty);
}

static int
argsclass(Ins *i0, Ins *i1, Class *carg, int retptr)
{
	int ngp, nfp, *gp, *fp, vararg, envc;
	Class *c;
	Typ *t;
	Ins *i;

	gp = gpreg;
	fp = fpreg;
	ngp = 8;
	nfp = 8;
	vararg = 0;
	envc = 0;
	if (retptr) {
		gp++;
		ngp--;
	}
	for (i=i0, c=carg; i<i1; i++, c++) {
		switch (i->op) {
		case Opar:
		case Oarg:
			*c->cls = i->cls;
			if (!vararg && KBASE(i->cls) == 1 && nfp > 0) {
				nfp--;
				*c->reg = *fp++;
			} else if (ngp > 0) {
				if (KBASE(i->cls) == 1)
					c->class |= Cfpint;
				ngp--;
				*c->reg = *gp++;
			} else
				c->class |= Cstk1;
			break;
		case Oargv:
			vararg = 1;
			break;
		case Oparc:
		case Oargc:
			t = &typ[i->arg[0].val];
			typclass(c, t, 1, gp, fp);
			if (c->nfp > 0)
			if (c->nfp >= nfp || c->ngp >= ngp)
				typclass(c, t, 0, gp, fp);
			assert(c->nfp <= nfp);
			if (c->ngp <= ngp) {
				ngp -= c->ngp;
				nfp -= c->nfp;
				gp += c->ngp;
				fp += c->nfp;
			} else if (ngp > 0) {
				assert(c->ngp == 2);
				assert(c->class == 0);
				c->class |= Cstk2;
				c->nreg = 1;
				ngp--;
				gp++;
			} else {
				c->class |= Cstk1;
				if (c->nreg > 1)
					c->class |= Cstk2;
				c->nreg = 0;
			}
			break;
		case Opare:
		case Oarge:
			*c->reg = T5;
			*c->cls = Kl;
			envc = 1;
			break;
		}
	}
	return envc << 12 | (gp-gpreg) << 4 | (fp-fpreg) << 8;
}

static void
stkblob(Ref r, Typ *t, Fn *fn, Insl **ilp)
{
	Insl *il;
	int al;
	uint64_t sz;

	il = alloc(sizeof *il);
	al = t->align - 2; /* specific to NAlign == 3 */
	if (al < 0)
		al = 0;
	sz = (t->size + 7) & ~7;
	il->i = (Ins){Oalloc+al, Kl, r, {getcon(sz, fn)}};
	il->link = *ilp;
	*ilp = il;
}

static void
selcall(Fn *fn, Ins *i0, Ins *i1, Insl **ilp)
{
	Ins *i;
	Class *ca, *c, cr;
	int j, k, cty;
	uint64_t stk, off;
	Ref r, r1, tmp[2];

	ca = alloc((i1-i0) * sizeof ca[0]);
	cr.class = 0;

	if (!req(i1->arg[1], R))
		typclass(&cr, &typ[i1->arg[1].val], 1, gpreg, fpreg);

	cty = argsclass(i0, i1, ca, cr.class & Cptr);
	stk = 0;
	for (i=i0, c=ca; i<i1; i++, c++) {
		if (i->op == Oargv)
			continue;
		if (c->class & Cptr) {
			i->arg[0] = newtmp("abi", Kl, fn);
			stkblob(i->arg[0], c->type, fn, ilp);
			i->op = Oarg;
		}
		if (c->class & Cstk1)
			stk += 8;
		if (c->class & Cstk2)
			stk += 8;
	}
	stk += stk & 15;
	if (stk)
		emit(Osalloc, Kl, R, getcon(-stk, fn), R);

	if (!req(i1->arg[1], R)) {
		stkblob(i1->to, cr.type, fn, ilp);
		cty |= (cr.nfp << 2) | cr.ngp;
		if (cr.class & Cptr)
			/* spill & rega expect calls to be
			 * followed by copies from regs,
			 * so we emit a dummy
			 */
			emit(Ocopy, Kw, R, TMP(A0), R);
		else {
			sttmps(tmp, cr.nreg, &cr, i1->to, fn);
			for (j=0; j<cr.nreg; j++) {
				r = TMP(cr.reg[j]);
				emit(Ocopy, cr.cls[j], tmp[j], r, R);
			}
		}
	} else if (KBASE(i1->cls) == 0) {
		emit(Ocopy, i1->cls, i1->to, TMP(A0), R);
		cty |= 1;
	} else {
		emit(Ocopy, i1->cls, i1->to, TMP(FA0), R);
		cty |= 1 << 2;
	}

	emit(Ocall, 0, R, i1->arg[0], CALL(cty));

	if (cr.class & Cptr)
		/* struct return argument */
		emit(Ocopy, Kl, TMP(A0), i1->to, R);

	/* move arguments into registers */
	for (i=i0, c=ca; i<i1; i++, c++) {
		if (i->op == Oargv || c->class & Cstk1)
			continue;
		if (i->op == Oargc) {
			ldregs(c, i->arg[1], fn);
		} else if (c->class & Cfpint) {
			k = KWIDE(*c->cls) ? Kl : Kw;
			r = newtmp("abi", k, fn);
			emit(Ocopy, k, TMP(*c->reg), r, R);
			*c->reg = r.val;
		} else {
			emit(Ocopy, *c->cls, TMP(*c->reg), i->arg[0], R);
		}
	}

	for (i=i0, c=ca; i<i1; i++, c++) {
		if (c->class & Cfpint) {
			k = KWIDE(*c->cls) ? Kl : Kw;
			emit(Ocast, k, TMP(*c->reg), i->arg[0], R);
		}
		if (c->class & Cptr)
			blit0(i->arg[0], i->arg[1], c->type->size, fn);
	}

	if (!stk)
		return;

	/* populate the stack */
	off = 0;
	r = newtmp("abi", Kl, fn);
	for (i=i0, c=ca; i<i1; i++, c++) {
		if (i->op == Oargv || !(c->class & Cstk))
			continue;
		if (i->op == Oarg) {
			r1 = newtmp("abi", Kl, fn);
			emit(Ostorew+i->cls, Kw, R, i->arg[0], r1);
			if (i->cls == Kw) {
				/* TODO: we only need this sign
				 * extension for l temps passed
				 * as w arguments
				 * (see rv64/isel.c:fixarg)
				 */
				curi->op = Ostorel;
				curi->arg[0] = newtmp("abi", Kl, fn);
				emit(Oextsw, Kl, curi->arg[0], i->arg[0], R);
			}
			emit(Oadd, Kl, r1, r, getcon(off, fn));
			off += 8;
		}
		if (i->op == Oargc) {
			if (c->class & Cstk1) {
				blit(r, off, i->arg[1], 0, 8, fn);
				off += 8;
			}
			if (c->class & Cstk2) {
				blit(r, off, i->arg[1], 8, 8, fn);
				off += 8;
			}
		}
	}
	emit(Osalloc, Kl, r, getcon(stk, fn), R);
}

static Params
selpar(Fn *fn, Ins *i0, Ins *i1)
{
	Class *ca, *c, cr;
	Insl *il;
	Ins *i;
	int j, k, s, cty, nt;
	Ref r, tmp[17], *t;

	ca = alloc((i1-i0) * sizeof ca[0]);
	cr.class = 0;
	curi = &insb[NIns];

	if (fn->retty >= 0) {
		typclass(&cr, &typ[fn->retty], 1, gpreg, fpreg);
		if (cr.class & Cptr) {
			fn->retr = newtmp("abi", Kl, fn);
			emit(Ocopy, Kl, fn->retr, TMP(A0), R);
		}
	}

	cty = argsclass(i0, i1, ca, cr.class & Cptr);
	fn->reg = rv64_argregs(CALL(cty), 0);

	il = 0;
	t = tmp;
	for (i=i0, c=ca; i<i1; i++, c++) {
		if (c->class & Cfpint) {
			r = i->to;
			k = *c->cls;
			*c->cls = KWIDE(k) ? Kl : Kw;
			i->to = newtmp("abi", k, fn);
			emit(Ocast, k, r, i->to, R);
		}
		if (i->op == Oparc)
		if (!(c->class & Cptr))
		if (c->nreg != 0) {
			nt = c->nreg;
			if (c->class & Cstk2) {
				c->cls[1] = Kl;
				c->off[1] = 8;
				assert(nt == 1);
				nt = 2;
			}
			sttmps(t, nt, c, i->to, fn);
			stkblob(i->to, c->type, fn, &il);
			t += nt;
		}
	}
	for (; il; il=il->link)
		emiti(il->i);

	t = tmp;
	s = 2 + 8*fn->vararg;
	for (i=i0, c=ca; i<i1; i++, c++)
		if (i->op == Oparc && !(c->class & Cptr)) {
			if (c->nreg == 0) {
				fn->tmp[i->to.val].slot = -s;
				s += (c->class & Cstk2) ? 2 : 1;
				continue;
			}
			for (j=0; j<c->nreg; j++) {
				r = TMP(c->reg[j]);
				emit(Ocopy, c->cls[j], *t++, r, R);
			}
			if (c->class & Cstk2) {
				emit(Oload, Kl, *t, SLOT(-s), R);
				t++, s++;
			}
		} else if (c->class & Cstk1) {
			emit(Oload, *c->cls, i->to, SLOT(-s), R);
			s++;
		} else {
			emit(Ocopy, *c->cls, i->to, TMP(*c->reg), R);
		}

	return (Params){
		.stk = s,
		.ngp = (cty >> 4) & 15,
		.nfp = (cty >> 8) & 15,
	};
}

static void
selvaarg(Fn *fn, Ins *i)
{
	Ref loc, newloc;

	loc = newtmp("abi", Kl, fn);
	newloc = newtmp("abi", Kl, fn);
	emit(Ostorel, Kw, R, newloc, i->arg[0]);
	emit(Oadd, Kl, newloc, loc, getcon(8, fn));
	emit(Oload, i->cls, i->to, loc, R);
	emit(Oload, Kl, loc, i->arg[0], R);
}

static void
selvastart(Fn *fn, Params p, Ref ap)
{
	Ref rsave;
	int s;

	rsave = newtmp("abi", Kl, fn);
	emit(Ostorel, Kw, R, rsave, ap);
	s = p.stk > 2 + 8 * fn->vararg ? p.stk : 2 + p.ngp;
	emit(Oaddr, Kl, rsave, SLOT(-s), R);
}

void
rv64_abi(Fn *fn)
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
				selvaarg(fn, i);
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
