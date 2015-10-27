#include "lisc.h"

static void
addpred(Blk *bp, Blk *bc)
{
	uint i;

	if (!bc->pred) {
		bc->pred = alloc(bc->npred * sizeof bc->pred[0]);
		for (i=0; i<bc->npred; i++)
			bc->pred[i] = 0;
	}
	for (i=0; bc->pred[i]; i++)
		;
	bc->pred[i] = bp;
}

/* fill predecessors information in blocks
 */
void
fillpreds(Fn *f)
{
	Blk *b;

	for (b=f->start; b; b=b->link) {
		b->npred = 0;
		b->pred = 0;
	}
	for (b=f->start; b; b=b->link) {
		if (b->s1)
			b->s1->npred++;
		if (b->s2)
			b->s2->npred++;
	}
	for (b=f->start; b; b=b->link) {
		if (b->s1)
			addpred(b, b->s1);
		if (b->s2)
			addpred(b, b->s2);
	}
}

static int
rporec(Blk *b, int x)
{
	Blk *s1, *s2;

	if (!b || b->id >= 0)
		return x;
	b->id = 1;
	s1 = b->s1;
	s2 = b->s2;
	if (s1 && s2 && s1->loop > s2->loop) {
		s1 = b->s2;
		s2 = b->s1;
	}
	x = rporec(s1, x);
	x = rporec(s2, x);
	b->id = x;
	assert(x >= 0);
	return x - 1;
}

/* fill the rpo information in blocks
 */
void
fillrpo(Fn *f)
{
	int n;
	Blk *b, **p;

	for (b=f->start; b; b=b->link)
		b->id = -1;
	n = 1 + rporec(f->start, f->nblk-1);
	f->nblk -= n;
	f->rpo = alloc(f->nblk * sizeof f->rpo[0]);
	for (p=&f->start; *p;) {
		b = *p;
		if (b->id == -1) {
			*p = b->link;
			/* todo, free block */
		} else {
			b->id -= n;
			f->rpo[b->id] = b;
			p=&(*p)->link;
		}
	}
}

/* gets the representant for the phi class of t
 */
int
phirepr(Tmp *tmp, int t)
{
	int tp;

	tp = tmp[t].phi;
	if (tp == 0)
		tp = t;
	else if (tp != t) {
		tp = phirepr(tmp, tp);
		tmp[t].phi = tp;
	}
	return tp;
}

/* fill union find data for phi classes
 */
void
fillphi(Fn *fn)
{
	Blk *b;
	Phi *p;
	uint a;
	int t, ta;
	Tmp *tmp;

	tmp = fn->tmp;
	for (t=Tmp0; t<fn->ntmp; t++)
		tmp[t].phi = 0;
	for (b=fn->start; b; b=b->link)
		for (p=b->phi; p; p=p->link) {
			t = p->to.val;
			if (tmp[t].phi == 0)
				tmp[t].phi = t;
			for (a=0; a<p->narg; a++) {
				if (rtype(p->arg[a]) != RTmp)
					continue;
				ta = p->arg[a].val;
				ta = phirepr(tmp, ta);
				tmp[ta].phi = t;
			}
		}
}

static Ref *top, *bot;
static Ref topdef(Blk *, Fn *, int);

static Ref
botdef(Blk *b, Fn *f, int w)
{
	Ref r;

	if (!req(bot[b->id], R))
		return bot[b->id];
	r = topdef(b, f, w);
	bot[b->id] = r;
	return r;
}

static Ref
topdef(Blk *b, Fn *f, int w)
{
	uint i;
	int t1;
	Ref r;
	Phi *p;

	if (!req(top[b->id], R))
		return top[b->id];
	assert(b->npred && "invalid ssa program detected");
	if (b->npred == 1) {
		r = botdef(b->pred[0], f, w);
		top[b->id] = r;
		return r;
	}
	/* add a phi node */
	t1 = f->ntmp++;
	r = TMP(t1);
	top[b->id] = r;
	p = alloc(sizeof *p);
	p->link = b->phi;
	b->phi = p;
	p->to = r;
	p->wide = w;
	for (i=0; i<b->npred; i++) {
		p->arg[i] = botdef(b->pred[i], f, w);
		p->blk[i] = b->pred[i];
	}
	p->narg = i;
	return r;
}

/* restore ssa form for a temporary t
 * predecessors must be available
 */
void
ssafix(Fn *f, int t)
{
	uint n;
	int t0, t1, w;
	Ref rt;
	Blk *b;
	Phi *p;
	Ins *i;

	w = 0;
	top = alloc(f->nblk * sizeof top[0]);
	bot = alloc(f->nblk * sizeof bot[0]);
	rt = TMP(t);
	t0 = f->ntmp;
	for (b=f->start; b; b=b->link) {
		t1 = 0;
		/* rename defs and some in-blocks uses */
		for (p=b->phi; p; p=p->link)
			if (req(p->to, rt)) {
				t1 = t0++;
				p->to = TMP(t1);
				w |= p->wide;
			}
		for (i=b->ins; i-b->ins < b->nins; i++) {
			if (t1) {
				if (req(i->arg[0], rt))
					i->arg[0] = TMP(t1);
				if (req(i->arg[1], rt))
					i->arg[1] = TMP(t1);
			}
			if (req(i->to, rt)) {
				w |= i->wide;
				t1 = t0++;
				i->to = TMP(t1);
			}
		}
		if (t1 && req(b->jmp.arg, rt))
			b->jmp.arg = TMP(t1);
		top[b->id] = R;
		bot[b->id] = t1 ? TMP(t1) : R;
	}
	for (b=f->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link)
			for (n=0; n<p->narg; n++)
				if (req(p->arg[n], rt))
					p->arg[n] = botdef(p->blk[n], f, w);
		for (i=b->ins; i-b->ins < b->nins; i++) {
			if (req(i->arg[0], rt))
				i->arg[0] = topdef(b, f, w);
			if (req(i->arg[1], rt))
				i->arg[1] = topdef(b, f, w);
		}
		if (req(b->jmp.arg, rt))
			b->jmp.arg = topdef(b, f, w);
	}
	/* add new temporaries */
	for (t1=f->ntmp; t1<t0; t1++)
		newtmp(f->tmp[t].name, f);
}
