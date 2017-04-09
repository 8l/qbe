#include "all.h"

#ifdef TEST_PMOV
	#undef assert
	#define assert(x) assert_test(#x, x)
#endif

typedef struct RMap RMap;

struct RMap {
	int t[Tmp0];
	int r[Tmp0];
	BSet b[1];
	int n;
};

static bits regu;      /* registers used */
static Tmp *tmp;       /* function temporaries */
static Mem *mem;       /* function mem references */
static struct {
	Ref src, dst;
	int cls;
} *pm;                 /* parallel move constructed */
static int cpm, npm;   /* capacity and size of pm */

static int *
hint(int t)
{
	return &tmp[phicls(t, tmp)].hint.r;
}

static void
sethint(int t, int r)
{
	bits m;

	m = tmp[phicls(t, tmp)].hint.m;
	if (*hint(t) == -1)
	if (!(BIT(r) & m))
		*hint(t) = r;
}

static void
rcopy(RMap *ma, RMap *mb)
{
	memcpy(ma->t, mb->t, sizeof ma->t);
	memcpy(ma->r, mb->r, sizeof ma->r);
	bscopy(ma->b, mb->b);
	ma->n = mb->n;
}

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
		s = tmp[t].slot;
		assert(s != -1 && "should have spilled");
		return SLOT(s);
	} else
		return TMP(r);
}

static void
radd(RMap *m, int t, int r)
{
	assert((t >= Tmp0 || t == r) && "invalid temporary");
	assert(((T.gpr0 <= r && r < T.gpr0 + T.ngpr)
		|| (T.fpr0 <= r && r < T.fpr0 + T.nfpr))
		&& "invalid register");
	assert(!bshas(m->b, t) && "temporary has mapping");
	assert(!bshas(m->b, r) && "register already allocated");
	assert(m->n <= T.ngpr+T.nfpr && "too many mappings");
	bsset(m->b, t);
	bsset(m->b, r);
	m->t[m->n] = t;
	m->r[m->n] = r;
	m->n++;
	regu |= BIT(r);
}

static Ref
ralloc(RMap *m, int t)
{
	bits regs;
	int r, r0, r1;

	if (t < Tmp0) {
		assert(bshas(m->b, t));
		return TMP(t);
	}
	if (bshas(m->b, t)) {
		r = rfind(m, t);
		assert(r != -1);
		return TMP(r);
	}
	r = *hint(t);
	if (r == -1 || bshas(m->b, r)) {
		regs = tmp[phicls(t, tmp)].hint.m;
		regs |= m->b->t[0];
		if (KBASE(tmp[t].cls) == 0) {
			r0 = T.gpr0;
			r1 = r0 + T.ngpr;
		} else {
			r0 = T.fpr0;
			r1 = r0 + T.nfpr;
		}
		for (r=r0; r<r1; r++)
			if (!(regs & BIT(r)))
				goto Found;
		for (r=r0; r<r1; r++)
			if (!bshas(m->b, r))
				goto Found;
		die("no more regs");
	}
Found:
	radd(m, t, r);
	sethint(t, r);
	return TMP(r);
}

static int
rfree(RMap *m, int t)
{
	int i, r;

	assert(t >= Tmp0 || !(BIT(t) & T.rglob));
	if (!bshas(m->b, t))
		return -1;
	for (i=0; m->t[i] != t; i++)
		assert(i+1 < m->n);
	r = m->r[i];
	bsclr(m->b, t);
	bsclr(m->b, r);
	m->n--;
	memmove(&m->t[i], &m->t[i+1], (m->n-i) * sizeof m->t[0]);
	memmove(&m->r[i], &m->r[i+1], (m->n-i) * sizeof m->r[0]);
	assert(t >= Tmp0 || t == r);
	return r;
}

static void
mdump(RMap *m)
{
	int i;

	for (i=0; i<m->n; i++)
		if (m->t[i] >= Tmp0)
			fprintf(stderr, " (%s, R%d)",
				tmp[m->t[i]].name,
				m->r[i]);
	fprintf(stderr, "\n");
}

static void
pmadd(Ref src, Ref dst, int k)
{
	if (npm == cpm) {
		cpm = cpm * 2 + 16;
		pm = realloc(pm, cpm * sizeof pm[0]);
		if (!pm)
			die("pmadd, out of memory");
	}
	pm[npm].src = src;
	pm[npm].dst = dst;
	pm[npm].cls = k;
	npm++;
}

enum PMStat { ToMove, Moving, Moved };

static Ref
pmrec(enum PMStat *status, int i, int *k)
{
	Ref swp, swp1;
	int j, k1;

	/* note, this routine might emit
	 * too many large instructions:
	 *
	 *                  , x -- x
	 *      x -- x -- x        |
	 *                  ` x -- x
	 *
	 * if only the first move is wide
	 * the whole cycle will be wide,
	 * this is safe but not necessary
	 */

	if (req(pm[i].src, pm[i].dst))
		return R;
	status[i] = Moving;
	assert(KBASE(*k) == KBASE(pm[i].cls));
	assert((Kw|1) == Kl && (Ks|1) == Kd);
	*k |= KWIDE(pm[i].cls); /* see above */
	swp = R;
	for (j=0; j<npm; j++) {
		if (req(pm[j].src, pm[i].dst))
			switch (status[j]) {
			case ToMove:
				k1 = *k;
				swp1 = pmrec(status, j, &k1);
				if (!req(swp1, R)) {
					assert(req(swp, R));
					swp = swp1;
					*k = k1;
				}
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
		*curi++ = (Ins){Ocopy, pm[i].dst, {pm[i].src}, pm[i].cls};
		return R;
	} else if (!req(swp, pm[i].src)) {
		*curi++ = (Ins){Oswap, R, {pm[i].src, pm[i].dst}, *k};
		return swp;
	} else
		return R;

}

static void
pmgen()
{
	int i, k;
	enum PMStat *status;

	status = alloc(npm * sizeof status[0]);
	assert(!npm || status[npm-1] == ToMove);
	curi = insb;
	for (i=0; i<npm; i++)
		if (status[i] == ToMove) {
			k = pm[i].cls;
			pmrec(status, i, &k);
		}
}

static void
move(int r, Ref to, RMap *m)
{
	int n, t, r1;

	r1 = req(to, R) ? -1 : rfree(m, to.val);
	if (bshas(m->b, r) && r1 != r) {
		/* r is used and not by to */
		for (n=0; m->r[n] != r; n++)
			assert(n+1 < m->n);
		t = m->t[n];
		rfree(m, t);
		bsset(m->b, r);
		ralloc(m, t);
		bsclr(m->b, r);
	}
	t = req(to, R) ? r : to.val;
	radd(m, t, r);
}

static int
regcpy(Ins *i)
{
	return i->op == Ocopy && isreg(i->arg[0]);
}

static Ins *
dopm(Blk *b, Ins *i, RMap *m)
{
	RMap m0;
	int n, r, r1, t, s;
	Ins *i0, *i1, *ip, *ir;
	bits def;

	m0 = *m;
	i1 = ++i;
	do {
		i--;
		move(i->arg[0].val, i->to, m);
	} while (i != b->ins && regcpy(i-1));
	assert(m0.n <= m->n);
	if (i != b->ins && (i-1)->op == Ocall) {
		def = T.retregs((i-1)->arg[1], 0) | T.rglob;
		for (r=0; T.rsave[r]>=0; r++)
			if (!(BIT(T.rsave[r]) & def))
				move(T.rsave[r], R, m);
	}
	for (npm=0, n=0; n<m->n; n++) {
		t = m->t[n];
		s = tmp[t].slot;
		r1 = m->r[n];
		r = rfind(&m0, t);
		if (r != -1)
			pmadd(TMP(r1), TMP(r), tmp[t].cls);
		else if (s != -1)
			pmadd(TMP(r1), SLOT(s), tmp[t].cls);
	}
	for (ip=i; ip<i1; ip++) {
		if (!req(ip->to, R))
			rfree(m, ip->to.val);
		r = ip->arg[0].val;
		if (rfind(m, r) == -1)
			radd(m, r, r);
	}
	pmgen();
#ifdef TEST_PMOV
	return 0;
#endif
	n = b->nins - (i1 - i) + (curi - insb);
	i0 = alloc(n * sizeof(Ins));
	ip = icpy(ip = i0, b->ins, i - b->ins);
	ip = icpy(ir = ip, insb, curi - insb);
	ip = icpy(ip, i1, &b->ins[b->nins] - i1);
	b->nins = n;
	b->ins = i0;
	return ir;
}

static int
prio(Ref r1, Ref r2)
{
	/* trivial heuristic to begin with,
	 * later we can use the distance to
	 * the definition instruction
	 */
	(void) r2;
	return *hint(r1.val) != -1;
}

static void
insert(Ref *r, Ref **rs, int p)
{
	int i;

	rs[i = p] = r;
	while (i-- > 0 && prio(*r, *rs[i])) {
		rs[i+1] = rs[i];
		rs[i] = r;
	}
}

static void
doblk(Blk *b, RMap *cur)
{
	int x, r, nr;
	bits rs;
	Ins *i;
	Mem *m;
	Ref *ra[4];

	for (r=0; bsiter(b->out, &r) && r<Tmp0; r++)
		radd(cur, r, r);
	if (rtype(b->jmp.arg) == RTmp)
		b->jmp.arg = ralloc(cur, b->jmp.arg.val);
	for (i=&b->ins[b->nins]; i!=b->ins;) {
		switch ((--i)->op) {
		case Ocall:
			rs = T.argregs(i->arg[1], 0) | T.rglob;
			for (r=0; T.rsave[r]>=0; r++)
				if (!(BIT(T.rsave[r]) & rs))
					rfree(cur, T.rsave[r]);
			break;
		case Ocopy:
			if (isreg(i->arg[0])) {
				i = dopm(b, i, cur);
				continue;
			}
			if (isreg(i->to))
			if (rtype(i->arg[0]) == RTmp)
				sethint(i->arg[0].val, i->to.val);
			/* fall through */
		default:
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				r = i->to.val;
				if (r >= Tmp0 || !(BIT(r) & T.rglob))
					r = rfree(cur, r);
				if (r == -1) {
					assert(!isreg(i->to));
					*i = (Ins){.op = Onop};
					continue;
				}
				i->to = TMP(r);
			}
			break;
		}
		for (x=0, nr=0; x<2; x++)
			switch (rtype(i->arg[x])) {
			case RMem:
				m = &mem[i->arg[x].val];
				if (rtype(m->base) == RTmp)
					insert(&m->base, ra, nr++);
				if (rtype(m->index) == RTmp)
					insert(&m->index, ra, nr++);
				break;
			case RTmp:
				insert(&i->arg[x], ra, nr++);
				break;
			}
		for (r=0; r<nr; r++)
			*ra[r] = ralloc(cur, ra[r]->val);
	}
}

/* register allocation
 * depends on rpo, phi, cost, (and obviously spill)
 */
void
rega(Fn *fn)
{
	int j, t, r, r1, x, rl[Tmp0];
	Blk *b, *b1, *s, ***ps, *blist;
	RMap *end, *beg, cur, old;
	Ins *i;
	Phi *p;
	uint u, n;
	Ref src, dst;

	/* 1. setup */
	regu = 0;
	tmp = fn->tmp;
	mem = fn->mem;
	end = alloc(fn->nblk * sizeof end[0]);
	beg = alloc(fn->nblk * sizeof beg[0]);
	for (n=0; n<fn->nblk; n++) {
		bsinit(end[n].b, fn->ntmp);
		bsinit(beg[n].b, fn->ntmp);
	}
	bsinit(cur.b, fn->ntmp);
	bsinit(old.b, fn->ntmp);

	for (t=0; t<fn->ntmp; t++)
		*hint(t) = t < Tmp0 ? t : -1;
	for (b=fn->start, i=b->ins; i-b->ins < b->nins; i++)
		if (i->op != Ocopy || !isreg(i->arg[0]))
			break;
		else {
			assert(rtype(i->to) == RTmp);
			sethint(i->to.val, i->arg[0].val);
		}

	/* 2. assign registers following post-order */
	for (n=fn->nblk-1; n!=-1u; n--) {
		b = fn->rpo[n];
		cur.n = 0;
		bszero(cur.b);
		for (x=0; x<2; x++)
			for (t=Tmp0; bsiter(b->out, &t); t++)
				if (x || (r=*hint(t)) != -1)
				if (x || !bshas(cur.b, r))
					ralloc(&cur, t);
		rcopy(&end[n], &cur);
		doblk(b, &cur);
		bscopy(b->in, cur.b);
		for (p=b->phi; p; p=p->link)
			if (rtype(p->to) == RTmp) {
				bsclr(b->in, p->to.val);
				/* heuristic 0:
				 * if the phi destination has an
				 * argument from a frequent block
				 * that was already allocated to
				 * 'r', use 'r' as the new hint
				 */
				memset(rl, 0, sizeof rl);
				for (u=0; u<p->narg; u++) {
					t = p->arg[u].val;
					b1 = p->blk[u];
					if (rtype(p->arg[u]) == RTmp)
					if ((r=rfind(&end[b1->id], t)) != -1)
						rl[r] += b1->loop;
				}
				for (x=0, j=0; j<Tmp0; j++)
					if (rl[j] > rl[x])
						x = j;
				if (rl[x] >= b->loop)
					*hint(p->to.val) = x;
			}
		if (b->npred > 1) {
			/* heuristic 1:
			 * attempt to satisfy hints
			 * when it's simple and we have
			 * multiple predecessors
			 */
			rcopy(&old, &cur);
			curi = &insb[NIns];
			for (j=0; j<old.n; j++) {
				t = old.t[j];
				r = *hint(t);
				r1 = rfind(&cur, t);
				if (r != -1 && r != r1)
				if (!bshas(cur.b, r)) {
					rfree(&cur, t);
					radd(&cur, t, r);
					x = tmp[t].cls;
					emit(Ocopy, x, TMP(r1), TMP(r), R);
				}
			}
			if ((j = &insb[NIns] - curi)) {
				b->nins += j;
				i = alloc(b->nins * sizeof(Ins));
				icpy(icpy(i, curi, j), b->ins, b->nins-j);
				b->ins = i;
			}
		}
		rcopy(&beg[n], &cur);
	}
	if (debug['R'])  {
		fprintf(stderr, "\n> Register mappings:\n");
		for (n=0; n<fn->nblk; n++) {
			b = fn->rpo[n];
			fprintf(stderr, "\t%-10s beg", b->name);
			mdump(&beg[n]);
			fprintf(stderr, "\t           end");
			mdump(&end[n]);
		}
		fprintf(stderr, "\n");
	}

	/* 3. compose glue code */
	blist = 0;
	for (b=fn->start;; b=b->link) {
		ps = (Blk**[3]){&b->s1, &b->s2, (Blk*[1]){0}};
		for (; (s=**ps); ps++) {
			npm = 0;
			for (p=s->phi; p; p=p->link) {
				dst = p->to;
				assert(rtype(dst)==RSlot || rtype(dst)==RTmp);
				if (rtype(dst) == RTmp) {
					r = rfind(&beg[s->id], dst.val);
					if (r == -1)
						continue;
					dst = TMP(r);
				}
				for (u=0; p->blk[u]!=b; u++)
					assert(u+1 < p->narg);
				src = p->arg[u];
				if (rtype(src) == RTmp)
					src = rref(&end[b->id], src.val);
				pmadd(src, dst, p->cls);
			}
			for (t=Tmp0; bsiter(s->in, &t); t++) {
				src = rref(&end[b->id], t);
				dst = rref(&beg[s->id], t);
				pmadd(src, dst, tmp[t].cls);
			}
			pmgen();
			if (curi == insb)
				continue;
			b1 = blknew();
			b1->loop = (b->loop+s->loop) / 2;
			b1->link = blist;
			blist = b1;
			fn->nblk++;
			sprintf(b1->name, "%s_%s", b->name, s->name);
			b1->nins = curi - insb;
			idup(&b1->ins, insb, b1->nins);
			b1->jmp.type = Jjmp;
			b1->s1 = s;
			**ps = b1;
		}
		if (!b->link) {
			b->link = blist;
			break;
		}
	}
	for (b=fn->start; b; b=b->link)
		b->phi = 0;
	fn->reg = regu;

	if (debug['R']) {
		fprintf(stderr, "\n> After register allocation:\n");
		printfn(fn, stderr);
	}
}
