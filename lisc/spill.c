#include "lisc.h"

static void
loopmark(Blk *hd, Blk *b, Phi *p)
{
	int k, head;
	uint n, a;

	head = hd->id;
	if (b->id < head)
		return;
	for (; p; p=p->link)
		for (a=0; a<p->narg; a++)
			if (p->blk[a] == b)
			if (rtype(p->arg[a]) == RTmp)
				bsset(hd->gen, p->arg[a].val);
	if (b->visit == head)
		return;
	b->visit = head;
	b->loop *= 10;
	/* aggregate looping information at
	 * loop headers */
	bsunion(hd->gen, b->gen);
	for (k=0; k<2; k++)
		if (b->nlive[k] > hd->nlive[k])
			hd->nlive[k] = b->nlive[k];
	for (n=0; n<b->npred; n++)
		loopmark(hd, b->pred[n], b->phi);
}

static void
tmpuse(Ref r, int use, int loop, Fn *fn)
{
	Mem *m;
	Tmp *t;

	if (rtype(r) == RAMem) {
		m = &fn->mem[r.val & AMask];
		tmpuse(m->base, 1, loop, fn);
		tmpuse(m->index, 1, loop, fn);
	}
	else if (rtype(r) == RTmp && r.val >= Tmp0) {
		t = &fn->tmp[r.val];
		t->nuse += use;
		t->ndef += !use;
		t->cost += loop;
	}
}

/* evaluate spill costs of temporaries,
 * this also fills usage information
 * requires rpo, preds
 */
void
fillcost(Fn *fn)
{
	int n, hd;
	uint a;
	Blk *b;
	Ins *i;
	Tmp *t;
	Phi *p;

	for (b=fn->start; b; b=b->link) {
		b->loop = 1;
		b->visit = -1;
	}
	if (debug['S'])
		fprintf(stderr, "\n> Loop information:\n");
	for (n=0; n<fn->nblk; n++) {
		b = fn->rpo[n];
		hd = 0;
		for (a=0; a<b->npred; a++)
			if (b->pred[a]->id >= n) {
				loopmark(b, b->pred[a], b->phi);
				hd = 1;
			}
		if (hd && debug['S']) {
			fprintf(stderr, "\t%-10s", b->name);
			fprintf(stderr, " (% 3d ", b->nlive[0]);
			fprintf(stderr, "% 3d) ", b->nlive[1]);
			dumpts(b->gen, fn->tmp, stderr);
		}
	}
	for (t=fn->tmp; t-fn->tmp < fn->ntmp; t++) {
		t->cost = t-fn->tmp < Tmp0 ? 1e6 : 0;
		t->nuse = 0;
		t->ndef = 0;
	}
	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link) {
			/* todo, the cost computation
			 * for p->to is not great... */
			tmpuse(p->to, 0, 0, fn);
			for (a=0; a<p->narg; a++) {
				n = p->blk[a]->loop;
				assert(b->npred==p->narg &&
					"wrong cfg");
				n /= b->npred;
				tmpuse(p->arg[a], 1, n, fn);
			}
		}
		n = b->loop;
		for (i=b->ins; i-b->ins < b->nins; i++) {
			tmpuse(i->to, 0, n, fn);
			tmpuse(i->arg[0], 1, n, fn);
			tmpuse(i->arg[1], 1, n, fn);
		}
		tmpuse(b->jmp.arg, 1, n, fn);
	}
	if (debug['S']) {
		fprintf(stderr, "\n> Spill costs:\n");
		for (n=Tmp0; n<fn->ntmp; n++)
			fprintf(stderr, "\t%-10s %d\n",
				fn->tmp[n].name,
				fn->tmp[n].cost);
		fprintf(stderr, "\n");
	}
}

static BSet *fst; /* temps to prioritize in registers (for tcmp1) */
static Tmp *tmp;  /* current temporaries (for tcmpX) */
static int ntmp;  /* current # of temps (for limit) */
static int locs;  /* stack size used by locals */
static int slot4; /* next slot of 4 bytes */
static int slot8; /* ditto, 8 bytes */
static BSet mask[2][1]; /* class masks */

static int
tcmp0(const void *pa, const void *pb)
{
	return tmp[*(int *)pb].cost - tmp[*(int *)pa].cost;
}

static int
tcmp1(const void *pa, const void *pb)
{
	int c;

	c = bshas(fst, *(int *)pb) - bshas(fst, *(int *)pa);
	return c ? c : tcmp0(pa, pb);
}

static Ref
slot(int t)
{
	int s;

	if (t < Tmp0)
		diag("spill: cannot spill register");
	s = tmp[t].slot;
	if (s == -1) {
		assert(NAlign == 3);
		/* nice logic to pack stack slots
		 * on demand, there can be only
		 * one hole and slot4 points to it
		 *
		 * invariant: slot4 <= slot8
		 */
		if (KWIDE(tmp[t].cls)) {
			s = slot8;
			if (slot4 == slot8)
				slot4 += 2;
			slot8 += 2;
		} else {
			s = slot4;
			if (slot4 == slot8) {
				slot8 += 2;
				slot4 += 1;
			} else
				slot4 = slot8;
		}
		s += locs;
		tmp[t].slot = s;
	}
	return SLOT(s);
}

static void
limit(BSet *b, int k, BSet *f)
{
	static int *tarr, maxt;
	int i, t, nt;

	nt = bscount(b);
	if (nt <= k)
		return;
	if (nt > maxt) {
		free(tarr);
		tarr = emalloc(nt * sizeof tarr[0]);
		maxt = nt;
	}
	i = 0;
	for (t=0; t<ntmp; t++)
		if (bshas(b, t)) {
			bsclr(b, t);
			tarr[i++] = t;
		}
	assert(i == nt);
	if (!f)
		qsort(tarr, nt, sizeof tarr[0], tcmp0);
	else {
		fst = f;
		qsort(tarr, nt, sizeof tarr[0], tcmp1);
	}
	for (i=0; i<k && i<nt; i++)
		bsset(b, tarr[i]);
	for (; i<nt; i++)
		slot(tarr[i]);
}

static void
limit2(BSet *b, int k1, int k2, BSet *fst)
{
	BSet u[1], t[1];
	int k;

	bsinit(u, ntmp); /* todo, free those */
	bsinit(t, ntmp);
	bscopy(t, b);
	bszero(b);
	k1 = NIReg - k1;
	k2 = NFReg - k2;
	for (k=0; k<2; k++) {
		bscopy(u, t);
		bsinter(u, mask[k]);
		limit(u, k == 0 ? k1 : k2, fst);
		bsunion(b, u);
	}
}

static void
sethint(BSet *u, ulong r)
{
	uint t;

	for (t=Tmp0; bsiter(u, &t); t++)
		tmp[phicls(t, tmp)].hint.m |= r;
}

static void
reloads(BSet *u, BSet *v)
{
	uint t;

	for (t=Tmp0; bsiter(u, &t); t++)
		if (!bshas(v, t))
			emit(OLoad, tmp[t].cls, TMP(t), slot(t), R);
}

static void
store(Ref r, int s)
{
	static int kstore[] = {
		[Kw] = OStorew, [Kl] = OStorel,
		[Ks] = OStores, [Kd] = OStored,
	};

	if (s != -1)
		emit(kstore[tmp[r.val].cls], 0, R, r, SLOT(s));
}

static int
regcpy(Ins *i)
{
	return i->op == OCopy && isreg(i->arg[0]);
}

static Ins *
dopm(Blk *b, Ins *i, BSet *v)
{
	int n, t;
	BSet u[1];
	Ins *i1;
	ulong r;

	bsinit(u, ntmp); /* fixme, free those */
	/* consecutive copies from
	 * registers need to be handled
	 * as one large instruction
	 *
	 * fixme: there is an assumption
	 * that calls are always followed
	 * by copy instructions here, this
	 * might not be true if previous
	 * passes change
	 */
	i1 = ++i;
	do {
		i--;
		t = i->to.val;
		if (!req(i->to, R))
		if (BGET(*v, t)) {
			BCLR(*v, t);
			store(i->to, tmp[t].slot);
		}
		bsset(v, i->arg[0].val);
	} while (i != b->ins && regcpy(i-1));
	bscopy(u, v);
	if (i != b->ins && (i-1)->op == OCall) {
		v->t[0] &= ~calldef(*(i-1), 0);
		limit2(v, NISave, NFSave, 0);
		for (r=0, n=0; n<NRSave; n++)
			r |= BIT(rsave[n]);
		v->t[0] |= calluse(*(i-1), 0);
	} else {
		limit2(v, 0, 0, 0);
		r = v->t[0];
	}
	sethint(v, r);
	reloads(u, v);
	do
		emiti(*--i1);
	while (i1 != i);
	return i;
}

/* spill code insertion
 * requires spill costs, rpo, liveness
 *
 * Note: this will replace liveness
 * information (in, out) with temporaries
 * that must be in registers at block
 * borders
 *
 * Be careful with:
 * - OCopy instructions to ensure register
 *   constraints
 */
void
spill(Fn *fn)
{
	Blk *b, *s1, *s2, *hd, **bp;
	int j, n, l, t, k, lvarg[2];
	BSet u[1], v[1], w[1];
	Ins *i;
	Phi *p;
	Mem *m;
	ulong r;

	tmp = fn->tmp;
	ntmp = fn->ntmp;

	bsinit(u, ntmp); /* todo, free those */
	bsinit(v, ntmp);
	bsinit(w, ntmp);
	bsinit(mask[0], ntmp);
	bsinit(mask[1], ntmp);

	locs = fn->slot;
	slot4 = 0;
	slot8 = 0;
	for (t=0; t<ntmp; t++) {
		k = 0;
		if (t >= XMM0 && t < XMM0 + NFReg)
			k = 1;
		else if (t >= Tmp0)
			k = KBASE(tmp[t].cls);
		bsset(mask[k], t);
	}

	for (bp=&fn->rpo[fn->nblk]; bp!=fn->rpo;) {
		b = *--bp;
		/* invariant: all bocks with bigger rpo got
		 * their in,out updated. */

		/* 1. find temporaries in registers at
		 * the end of the block (put them in v) */
		curi = 0;
		s1 = b->s1;
		s2 = b->s2;
		hd = 0;
		if (s1 && s1->id <= n)
			hd = s1;
		if (s2 && s2->id <= n)
		if (!hd || s2->id >= hd->id)
			hd = s2;
		bszero(v);
		if (hd) {
			/* back-edge */
			for (k=0; k<2; k++) {
				n = k == 0 ? NIReg : NFReg;
				bscopy(u, b->out);
				bsinter(u, mask[k]);
				bscopy(w, u);
				bsinter(u, hd->gen);
				bsdiff(w, hd->gen);
				if ((int)bscount(u) < n) { /* fixme */
					j = bscount(w);   /* live through */
					l = hd->nlive[k];
					limit(w, n - (l - j), 0);
					bsunion(u, w);
				} else
					limit(u, n, 0);
				bsunion(v, u);
			}
		} else if (s1) {
			liveon(v, b, s1);
			if (s2) {
				bszero(u);
				liveon(u, b, s2);
				bscopy(w, u);
				bsinter(w, v);
				bsunion(v, u);
			}
			limit2(v, 0, 0, w);
		}
		bscopy(b->out, v);

		/* 2. process the block instructions */
		curi = &insb[NIns];
		r = 0;
		for (i=&b->ins[b->nins]; i!=b->ins;) {
			i--;
			if (regcpy(i)) {
				i = dopm(b, i, v);
				continue;
			}
			bszero(w);
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				t = i->to.val;
				if (bshas(v, t))
					bsclr(v, t);
				else {
					/* make sure we have a reg
					 * for the result */
					bsset(v, t);
					bsset(w, t);
				}
			}
			j = opdesc[i->op].nmem;
			for (n=0; n<2; n++)
				if (rtype(i->arg[n]) == RAMem)
					j--;
			for (n=0; n<2; n++)
				switch (rtype(i->arg[n])) {
				case RAMem:
					t = i->arg[n].val;
					m = &fn->mem[t & AMask];
					if (rtype(m->base) == RTmp) {
						bsset(v, m->base.val);
						bsset(w, m->base.val);
					}
					if (rtype(m->index) == RTmp) {
						bsset(v, m->index.val);
						bsset(w, m->index.val);
					}
					break;
				case RTmp:
					t = i->arg[n].val;
					lvarg[n] = bshas(v, t);
					bsset(v, t);
					if (j-- <= 0)
						bsset(w, t);
					break;
				}
			bscopy(u, v);
			limit2(v, 0, 0, w);
			for (n=0; n<2; n++)
				if (rtype(i->arg[n]) == RTmp) {
					t = i->arg[n].val;
					if (!bshas(v, t)) {
						/* do not reload if the
						 * the temporary was dead
						 */
						if (!lvarg[n])
							bsclr(u, t);
						i->arg[n] = slot(t);
					}
				}
			reloads(u, v);
			if (!req(i->to, R)) {
				t = i->to.val;
				store(i->to, tmp[t].slot);
				bsclr(v, t);
			}
			emiti(*i);
			r = v->t[0] & (BIT(Tmp0)-1);
			if (r)
				sethint(v, r);
		}
		assert(!r || b==fn->start);

		for (p=b->phi; p; p=p->link) {
			assert(rtype(p->to) == RTmp);
			t = p->to.val;
			if (bshas(v, t)) {
				bsclr(v, t);
				store(p->to, tmp[t].slot);
			} else if (bshas(b->in, t))
				/* only if the phi is live */
				p->to = slot(p->to.val);
		}
		bscopy(b->in, v);
		b->nins = &insb[NIns] - curi;
		idup(&b->ins, curi, b->nins);
	}

	/* align the locals to a 16 byte boundary */
	assert(NAlign == 3);
	slot8 += slot8 & 3;
	fn->slot += slot8;

	if (debug['S']) {
		fprintf(stderr, "\n> Block information:\n");
		for (b=fn->start; b; b=b->link) {
			printf("\t%-10s (% 5d) ", b->name, b->loop);
			dumpts(b->out, fn->tmp, stdout);
		}
		fprintf(stderr, "\n> After spilling:\n");
		printfn(fn, stderr);
	}
}
