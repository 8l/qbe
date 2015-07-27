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
static Sym *sym;       /* symbol table in use */
static struct {
	Ref src, dst;
} *pm;                 /* parallel move constructed */
static int cpm, npm;   /* capacity and size of pm */

static int
rfind(RMap *m, int t)
{
	int i;

	for (i=0; i<m->n; i++)
		if (m->t[i] == t)
			return m->r[i];
	return -1;
}

static Ref
rref(RMap *m, int t)
{
	int r, s;

	r = rfind(m, t);
	if (r == -1) {
		s = sym[t].spill;
		assert(s && "should have spilled");
		return SLOT(s);
	} else
		return SYM(r);
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

static int
ralloc(RMap *m, int t)
{
	int r;

	assert(m->n <= NReg || "oops, too few regs");
	if (BGET(m->bt, t)) {
		r = rfind(m, t);
		assert(r > 0);
		return r;
	}
	r = sym[t].hint;
	if (r == -1 || BGET(m->br, r))
		for (r=RAX; r<NReg; r++)
			if (!BGET(m->br, r))
				break;
	radd(m, t, r);
	if (sym[t].hint == -1)
		sym[t].hint = r;
	return r;
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

static void
mdump(RMap *m)
{
	int i;

	for (i=0; i<m->n; i++)
		fprintf(stderr, " (%s, %s)",
			sym[m->t[i]].name,
			sym[m->r[i]].name);
	fprintf(stderr, "\n");
}

static inline int
isreg(Ref r)
{
	return rtype(r) == RSym && sym[r.val].type == SReg;
}

static void
pmadd(Ref src, Ref dst)
{
	if (npm == cpm) {
		cpm = cpm * 2 + 16;
		pm = realloc(pm, cpm * sizeof pm[0]);
		if (!pm)
			diag("pmadd: out of memory");
	}
	pm[npm].src = src;
	pm[npm].dst = dst;
	npm++;
}

enum PMStat { ToMove, Moving, Moved };

static Ref
pmrec(enum PMStat *status, int i)
{
	Ref swp, swp1;
	int j;

	if (req(pm[i].src, pm[i].dst))
		return R;
	status[i] = Moving;
	swp = R;
	for (j=0; j<npm; j++) {
		if (req(pm[j].src, pm[i].dst))
			switch (status[j]) {
			case ToMove:
				swp1 = pmrec(status, j);
				assert(req(swp, R) || req(swp1, R));
				swp = swp1;
				break;
			case Moving:
				assert(req(swp, R));
				swp = pm[i].dst;
				break;
			case Moved:
				break;
			}
	}
	status[i] = Moved;
	if (req(swp, R)) {
		*curi++ = (Ins){OCopy, pm[i].dst, {pm[i].src, R}};
		return R;
	} else if (!req(swp, pm[i].src)) {
		*curi++ = (Ins){OSwap, R, {pm[i].src, pm[i].dst}};
		return swp;
	} else
		return R;

}

static void
pmgen()
{
	int i;
	enum PMStat *status;

	status = alloc(npm * sizeof status[0]);
	assert(!npm || status[npm-1] == ToMove);
	curi = insb;
	for (i=0; i<npm; i++)
		if (status[i] == ToMove)
			pmrec(status, i);
	free(status);
}

static Ins *
dopm(Blk *b, Ins *i)
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
	int n, t, u, r, x;
	Blk *b, *b1, *s, ***ps, *blist;
	Ins *i;
	RMap *end, *beg, cur;
	Phi *p;
	uint a;
	Ref src, dst;

	sym = fn->sym;
	/* 1. gross hinting setup */
	for (t=Tmp0; t<fn->ntmp; t++)
		sym[t].hint = -1;
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
	if (debug['R'])
		fprintf(stderr, "> Register mappings:\n");
	for (n=fn->nblk-1; n>=0; n--) {
		b = fn->rpo[n];
		cur.n = 0;
		cur.bt = (Bits){{0}};
		cur.br = (Bits){{0}};
		b1 = b->s1;
		if (b1 && b->s2 && b->s2->loop > b1->loop)
			b1 = b->s2;
		if (b1 && b->loop > b1->loop)
			b1 = 0;
		/* try to reuse the register
		 * assignment of the most frequent
		 * successor
		 */
		if (b1)
			for (t=Tmp0; t<fn->ntmp; t++)
				if (BGET(b->out, t))
				if ((r = rfind(&beg[b1->id], t)) != -1)
					radd(&cur, t, r);
		for (x=0; x<2; x++)
			for (t=Tmp0; t<fn->ntmp; t++)
				if (x==1 || sym[t].hint!=-1)
				if (BGET(b->out, t))
				if (!BGET(cur.bt, t))
					ralloc(&cur, t);
		/* process instructions */
		end[n] = cur;
		if (debug['R']) {
			fprintf(stderr, "\t%-10s end", b->name);
			mdump(&cur);
		}
		if (rtype(b->jmp.arg) == RSym)
			b->jmp.arg = SYM(ralloc(&cur, b->jmp.arg.val));
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			i--;
			if (i->op == OCopy /* par. moves are special */
			&& (isreg(i->arg[0]) || isreg(i->to))) {
				i = dopm(b, i);
				continue;
			}
			if (!req(i->to, R)) {
				r = rfree(&cur, i->to.val);
				if (!r) {
					*i = (Ins){ONop, R, {R, R}};
					continue;
				}
				i->to = SYM(r);
			}
			if (rtype(i->arg[0]) == RSym) {
				/* <arch>
				 *   on Intel, we attempt to
				 *   use the same register
				 *   for the return and the
				 *   first argument
				 */
				t = i->arg[0].val;
				if (sym[t].hint == -1 && r)
					sym[t].hint = r;
				i->arg[0] = SYM(ralloc(&cur, t));
			}
			if (rtype(i->arg[1]) == RSym) {
				/* <arch>
				 *   on Intel, we have to
				 *   make sure we avoid the
				 *   situation
				 *   eax = sub ebx, eax
				 */
				if (!opdesc[i->op].commut && r)
					BSET(cur.br, r);
				t = i->arg[1].val;
				i->arg[1] = SYM(ralloc(&cur, t));
				if (!opdesc[i->op].commut && r)
					BCLR(cur.br, r);
			}
		}
		if (debug['R']) {
			fprintf(stderr, "\t           beg");
			mdump(&cur);
		}
		b->in = cur.bt;
		for (p=b->phi; p; p=p->link)
			if (rtype(p->to) == RSym)
				BCLR(b->in, p->to.val);
		beg[n] = cur;
	}
	if (debug['R'])
		fprintf(stderr, "\n");

	/* 3. compose glue code */
	blist = 0;
	for (b=fn->start;; b=b->link) {
		ps = (Blk**[3]){&b->s1, &b->s2, (Blk*[1]){0}};
		for (; (s=**ps); ps++) {
			npm = 0;
			for (p=s->phi; p; p=p->link) {
				assert(rtype(p->to) == RSlot
					|| rtype(p->to) == RSym);
				dst = p->to;
				if (rtype(dst) == RSym) {
					r = rfind(&beg[s->id], dst.val);
					if (!r)
						continue;
					dst = SYM(r);
				}
				for (a=0; p->blk[a]!=b; a++)
					assert(a+1 < p->narg);
				src = p->arg[a];
				if (rtype(src) == RSym)
					src = rref(&end[b->id], src.val);
				pmadd(src, dst);
			}
			for (t=Tmp0; t<fn->ntmp; t++)
				if (BGET(s->in, t)) {
					src = rref(&end[b->id], t);
					dst = rref(&beg[s->id], t);
					pmadd(src, dst);
				}
			pmgen();
			/* todo, moving this out of
			 * here would make sense */
			n = curi-insb;
			if (!n)
				continue;
			b1 = blocka();
			b1->link = blist;
			blist = b1;
			fn->nblk++;
			sprintf(b1->name, "%s_%s", b->name, s->name);
			i = alloc(n * sizeof(Ins));
			memcpy(i, insb, n * sizeof(Ins));
			b1->ins = i;
			b1->nins = n;
			b1->jmp.type = JJmp;
			b1->s1 = s;
			**ps = b1;
		}
		if (!b->link) {
			b->link = blist;
			break;
		}
	}
	for (b=fn->start; b; b=b->link)
		while ((p=b->phi)) {
			b->phi = p->link;
			free(p);
		}

	free(end);
	free(beg);
}
