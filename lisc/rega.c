#include "lisc.h"


typedef struct RMap RMap;
struct RMap {
	int t[NReg];
	int r[NReg];
	Bits bt;
	Bits br;
	int n;
};

extern Ins insb[NIns], *curi;
static Sym *sym;   /* symbol table in use */
static Blk *elist; /* edge list created by edge() */
static int ne;     /* length of elist */

static int
rfind(RMap *m, int t)
{
	int i;

	for (i=0; i<m->n; i++)
		if (m->t[i] == t)
			return m->r[i];
	return -1;
}

static void
radd(RMap *m, int t, int r)
{
	assert(m->n <= NReg);
	assert(sym[t].type == STmp && "invalid allocation");
	assert(!BGET(m->bt, t) && "temp has mapping");
	assert(!BGET(m->br, r) && "reg already allocated");
	BSET(m->bt, t);
	BSET(m->br, r);
	m->t[m->n] = t;
	m->r[m->n] = r;
	m->n++;
}

static void
ralloc(RMap *m, int t)
{
	int r;

	assert(m->n <= NReg || "oops, too few regs");
	r = sym[t].hint;
	if (r == -1 || BGET(m->br, r))
		for (r=RAX; r<NReg; r++)
			if (!BGET(m->br, r))
				break;
	radd(m, t, r);
}

static int
rfree(RMap *m, int t)
{
	int i, r;

	if (!BGET(m->bt, t))
		return 0;
	for (i=0; m->t[i] != t; i++)
		assert(i+1 < NReg);
	r = m->r[i];
	BCLR(m->bt, t);
	BCLR(m->br, r);
	m->n--;
	memmove(&m->t[i], &m->t[i+1], (m->n-i) * sizeof(int));
	memmove(&m->r[i], &m->r[i+1], (m->n-i) * sizeof(int));
	return r;
}

static int
isreg(Ref r)
{
	return rtype(r) == RSym && sym[r.val].type == SReg;
}

static Ins *
pmgen(Blk *b, Ins *i)
{
	diag("not implemented");
	return 0;
}

/* register allocation
 * depends on rpo, cost, (and obviously spill)
 */
void
rega(Fn *fn)
{
	int n, t, u, r;
	Blk *b, *b1;
	Ins *i;
	RMap *end, *beg, cur;

	sym = fn->sym;
	/* 1. gross hinting setup */
	for (b=fn->start; b; b=b->link) {
		for (i=b->ins; i-b->ins < b->nins; i++) {
			if (i->op == OCopy
			&& rtype(i->arg[0]) == RSym
			&& !req(i->to, R)) {
				t = i->arg[0].val;
				u = i->to.val;
				if (sym[t].type == SReg)
					sym[u].hint = t;
				if (sym[u].type == SReg)
					sym[t].hint = u;
			}
		}
	}

	/* 2. assign registers backwards */
	end = alloc(fn->ntmp * sizeof end[0]);
	beg = alloc(fn->ntmp * sizeof beg[0]);
	for (n=fn->nblk-1; n>=0; n--) {
		b = fn->rpo[n];
		b1 = b->s1;
		cur.n = 0;
		cur.bt = (Bits){{0}};
		cur.br = (Bits){{0}};
		if (!b1 || b->s2->loop > b1->loop)
			b1 = b->s2;
		/* try to reuse the register
		 * assignment of the most frequent
		 * successor
		 */
		for (t=Tmp0; t<fn->ntmp; t++)
			if (BGET(b->out, t))
			if ((r = rfind(&beg[b1->id], t)) != -1)
				radd(&cur, t, r);
		for (t=Tmp0; t<fn->ntmp; t++)
			if (!BGET(cur.bt, t))
				ralloc(&cur, t);
		/* process instructions */
		if (rtype(b->jmp.arg) == RSym)
			ralloc(&cur, b->jmp.arg.val);
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			i--;
			if (i->op == OCopy /* par. moves are special */
			&& (isreg(i->arg[0]) || isreg(i->to))) {
				i = pmgen(b, i);
				continue;
			}
			if (!req(i->to, R))
				r = rfree(&cur, i->to.val);
			if (rtype(i->arg[0]) == RSym) {
				/* <arch>
				 *   on Intel, we attempt to
				 *   use the same register
				 *   for the return and the
				 *   first argument
				 */
				t = i->arg[0].val;
				if (sym[t].hint == -1)
					sym[t].hint = r;
				ralloc(&cur, t);
			}
			if (rtype(i->arg[1]) == RSym) {
				/* <arch>
				 *   on Intel, we have to
				 *   make sure we avoid the
				 *   situation
				 *   eax = sub ebx, eax
				 */
				if (!opdesc[i->op].commut && r!=-1)
					BSET(cur.br, r);
				t = i->arg[1].val;
				ralloc(&cur, t);
				if (!opdesc[i->op].commut && r!=-1)
					BCLR(cur.br, r);
			}
		}
	}

	/* 3. compose glue code */
	free(end);
	free(beg);
}






static Blk *
edge(Blk *b, Blk **ps, Ins *ins, int nins)
{
	Blk *b1, *s;
	Ins *ib;

	/* we could try to merge in blocks,
	 * but what the hell...
	 */
	s = *ps;
	b1 = blocka();
	b1->link = elist;
	elist = b1;
	ne++;
	sprintf(b1->name, "%s_%s", b->name, s->name);
	ib = alloc(nins * sizeof(Ins));
	memcpy(ib, ins, nins * sizeof(Ins));
	b1->ins = ib;
	b1->nins = nins;
	b1->jmp.type = JJmp;
	b1->s1 = s;
	return *ps = b1;
}
