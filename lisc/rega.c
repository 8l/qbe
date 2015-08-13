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
static Tmp *tmp;       /* function temporaries */
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
reg(int r, int t)
{
	assert(r < Tmp0);
	switch (tmp[t].type) {
	default:
		diag("rega: invalid temporary");
	case TWord:
		return TMP(RWORD(r));
	case TLong:
		return TMP(r);
	}
}

static Ref
rref(RMap *m, int t)
{
	int r, s;

	r = rfind(m, t);
	if (r == -1) {
		s = tmp[t].spill;
		assert(s && "should have spilled");
		return SLOT(s);
	} else
		return reg(r, t);
}

static void
radd(RMap *m, int t, int r)
{
	assert(RAX <= r && r < RAX + NReg && "invalid register");
	assert(!BGET(m->bt, t) && "temp has mapping");
	assert(!BGET(m->br, r) && "reg already allocated");
	assert(m->n <= NReg && "too many mappings");
	BSET(m->bt, t);
	BSET(m->br, r);
	m->t[m->n] = t;
	m->r[m->n] = r;
	m->n++;
}

static Ref
ralloc(RMap *m, int t)
{
	static int x;
	int n, r;

	if (t < Tmp0) {
		BSET(m->br, t);
		return TMP(t);
	}
	if (BGET(m->bt, t)) {
		r = rfind(m, t);
		assert(r != -1);
	} else {
		r = tmp[t].hint;
		if (r == -1 || BGET(m->br, r))
			for (n=0;; x=(x+1)%NReg, n++) {
				if (n > NReg)
					diag("rega: no more regs");
				r = RAX + x;
				if (!BGET(m->br, r))
					break;
			}
		radd(m, t, r);
		if (tmp[t].hint == -1)
			tmp[t].hint = r;
	}
	return reg(r, t);
}

static int
rfree(RMap *m, int t)
{
	int i, r;

	if (t < Tmp0) {
		t = RBASE(t);
		assert(BGET(m->br, t));
		BCLR(m->br, t);
		return t;
	}
	if (!BGET(m->bt, t))
		return -1;
	for (i=0; m->t[i] != t; i++)
		assert(i+1 < m->n);
	r = m->r[i];
	BCLR(m->bt, t);
	BCLR(m->br, r);
	m->n--;
	memmove(&m->t[i], &m->t[i+1], (m->n-i) * sizeof m->t[0]);
	memmove(&m->r[i], &m->r[i+1], (m->n-i) * sizeof m->r[0]);
	return r;
}

static void
mdump(RMap *m)
{
	int i;

	for (i=0; i<m->n; i++)
		fprintf(stderr, " (%s, R%d)",
			tmp[m->t[i]].name,
			m->r[i]);
	fprintf(stderr, "\n");
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

static int
isreg(Ref r)
{
	return rtype(r) == RTmp && r.val < Tmp0;
}

static Ins *
dopm(Blk *b, Ins *i, RMap *m)
{
	int n, r, t, nins;
	Ref rt;
	Ins *i1, *ib, *ip, *ir;

	npm = 0;
	i1 = i+1;
	if (isreg(i->to))
		for (;; i--) {
			r = RBASE(i->to.val);
			rt = i->arg[0];
			assert(rtype(rt) == RTmp);
			assert(BGET(m->br, r));
			/* todo, assert that r is not mapped */
			BCLR(m->br, r);
			rt = ralloc(m, rt.val);
			pmadd(rt, i->to);
			if (i==b->ins
			|| (i-1)->op!=OCopy
			|| isreg((i-1)->to))
				break;
		}
	else if (isreg(i->arg[0]))
		for (;; i--) {
			r = RBASE(i->arg[0].val);
			if (req(i->to, R)) {
				if (BGET(m->br, r)) {
					for (n=0; m->r[n] != r; n++)
						assert(n+1 < m->n);
					t = m->t[n];
					rfree(m, t);
					BSET(m->br, r);
					rt = ralloc(m, t);
					pmadd(rt, i->arg[0]);
				}
			} else if (BGET(m->bt, i->to.val)) {
				rt = reg(rfree(m, i->to.val), i->to.val);
				pmadd(i->arg[0], rt);
			}
			BSET(m->br, r);
			if (i==b->ins
			|| (i-1)->op!=OCopy
			|| isreg((i-1)->arg[0]))
				break;
		}
	else
		assert(!"no parallel move starting here");
	pmgen();
	nins = curi-insb;
	ib = alloc((b->nins + nins - (i1-i)) * sizeof(Ins));
	memcpy(ip = ib, b->ins, (i - b->ins) * sizeof(Ins));
	ip += i - b->ins;
	memcpy(ir = ip, insb, nins * sizeof(Ins));
	ip += nins;
	memcpy(ip, i1, (&b->ins[b->nins] - i1) * sizeof(Ins));
	b->nins += nins - (i1-i);
	free(b->ins);
	b->ins = ib;
	return ir;
}

/* register allocation
 * depends on rpo, cost, (and obviously spill)
 */
void
rega(Fn *fn)
{
	int n, t, r, x;
	Blk *b, *b1, *s, ***ps, *blist;
	Ins *i;
	RMap *end, *beg, cur;
	Phi *p;
	uint a;
	Ref src, dst;

	tmp = fn->tmp;
	end = alloc(fn->nblk * sizeof end[0]);
	beg = alloc(fn->nblk * sizeof beg[0]);

	/* 1. gross hinting setup */
	for (t=Tmp0; t<fn->ntmp; t++)
		tmp[t].hint = -1;
	for (b=fn->start; b; b=b->link)
		for (i=b->ins; i-b->ins < b->nins; i++) {
			if (i->op != OCopy)
				continue;
			if (rtype(i->arg[0]) == RTmp && isreg(i->to))
				tmp[i->arg[0].val].hint = RBASE(i->to.val);
			if (rtype(i->to) == RTmp && isreg(i->arg[0]))
				tmp[i->to.val].hint = RBASE(i->arg[0].val);
		}

	/* 2. assign registers backwards */
	if (debug['R'])
		fprintf(stderr, "> Register mappings:\n");
	for (n=fn->nblk-1; n>=0; n--) {
		b = fn->rpo[n];
		cur.n = 0;
		cur.bt = (Bits){{0}};
		cur.br = (Bits){{0}};
		b1 = b;
		if (b->s1 && b1->loop <= b->s1->loop)
			b1 = b->s1;
		if (b->s2 && b1->loop <= b->s2->loop)
			b1 = b->s1;
		/* try to reuse the register
		 * assignment of the most frequent
		 * successor
		 */
		if (b1 != b)
			for (t=Tmp0; t<fn->ntmp; t++)
				if (BGET(b->out, t))
				if ((r = rfind(&beg[b1->id], t)) != -1)
					radd(&cur, t, r);
		for (x=0; x<2; x++)
			for (t=Tmp0; t<fn->ntmp; t++)
				if (x==1 || tmp[t].hint!=-1)
				if (BGET(b->out, t))
				if (!BGET(cur.bt, t))
					ralloc(&cur, t);
		/* process instructions */
		end[n] = cur;
		if (rtype(b->jmp.arg) == RTmp)
			b->jmp.arg = ralloc(&cur, b->jmp.arg.val);
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			i--;
			if (i->op == OCopy /* par. moves are special */
			&& (isreg(i->arg[0]) || isreg(i->to))) {
				i = dopm(b, i, &cur);
				continue;
			}
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				r = rfree(&cur, i->to.val);
				if (r == -1) {
					*i = (Ins){ONop, R, {R, R}};
					continue;
				}
				if (i->to.val >= Tmp0)
					i->to = reg(r, i->to.val);
			}
			if (rtype(i->arg[0]) == RTmp) {
				/* <arch>
				 *   on Intel, we attempt to
				 *   use the same register
				 *   for the return and the
				 *   first argument
				 */
				t = i->arg[0].val;
				if (tmp[t].hint == -1 && r)
					tmp[t].hint = r;
				i->arg[0] = ralloc(&cur, t);
			}
			if (rtype(i->arg[1]) == RTmp) {
				t = i->arg[1].val;
				i->arg[1] = ralloc(&cur, t);
			}
		}
		b->in = cur.bt;
		for (p=b->phi; p; p=p->link)
			if (rtype(p->to) == RTmp)
				BCLR(b->in, p->to.val);
		beg[n] = cur;
		if (debug['R']) {
			fprintf(stderr, "\t%-10s beg", b->name);
			mdump(&beg[n]);
			fprintf(stderr, "\t           end");
			mdump(&end[n]);
		}
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
				dst = p->to;
				assert(rtype(dst)==RSlot|| rtype(dst)==RTmp);
				if (rtype(dst) == RTmp) {
					r = rfind(&beg[s->id], dst.val);
					if (r == -1)
						continue;
					dst = reg(r, dst.val);
				}
				for (a=0; p->blk[a]!=b; a++)
					assert(a+1 < p->narg);
				src = p->arg[a];
				if (rtype(src) == RTmp)
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
