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

/* for dominators computation, read
 * "A Simple, Fast Dominance Algorithm"
 * by K. Cooper, T. Harvey, and K. Kennedy.
 */

static Blk *
inter(Blk *b1, Blk *b2)
{
	Blk *bt;

	if (b1 == 0)
		return b2;
	while (b1 != b2) {
		if (b1->id > b2->id) {
			bt = b1;
			b1 = b2;
			b2 = bt;
		}
		while (b1->id < b2->id)
			b1 = b1->idom;
	}
	return b1;
}

static void
filldom(Fn *fn)
{
	Blk *b, *d;
	int ch, n;
	uint p;

	for (b=fn->start; b; b=b->link) {
		b->idom = 0;
		b->dom = 0;
		b->dlink = 0;
	}
	do {
		ch = 0;
		for (n=1; n<fn->nblk; n++) {
			b = fn->rpo[n];
			d = 0;
			for (p=0; p<b->npred; p++)
				if (b->pred[p]->idom)
					d = inter(d, b->pred[p]);
			if (d != b->idom) {
				ch++;
				b->idom = d;
			}
		}
	} while (ch);
	for (b=fn->start; b; b=b->link)
		if ((d=b->idom)) {
			assert(d != b);
			b->dlink = d->dom;
			d->dom = b;
		}
}

static int
sdom(Blk *b1, Blk *b2)
{
	if (b1 == b2)
		return 0;
	while (b2->id > b1->id)
		b2 = b2->idom;
	return b1 == b2;
}

static void
addfron(Blk *a, Blk *b)
{
	int n;

	for (n=0; n<a->nfron; n++)
		if (a->fron[n] == b)
			return;
	if (!a->nfron)
		a->fron = vnew(++a->nfron, sizeof a->fron[0]);
	else
		vgrow(&a->fron, ++a->nfron);
	a->fron[a->nfron-1] = b;
}

static void
fillfron(Fn *fn)
{
	Blk *a, *b;

	for (b=fn->start; b; b=b->link) {
		if (b->s1)
			for (a=b; !sdom(a, b->s1); a=a->link)
				addfron(a, b->s1);
		if (b->s2)
			for (a=b; !sdom(a, b->s2); a=a->link)
				addfron(a, b->s2);
	}
}

static void
phiins(Fn *fn)
{
	Bits u;
	Blk *b;
	Ins *i;
	Phi *p;
	int t, n, w;
	uint a;

	for (t=Tmp0; t<fn->ntmp; t++) {
		u = (Bits){{0}};
		w = -1;
		for (b=fn->start; b; b=b->link) {
			b->visit = 0;
			for (i=b->ins; i-b->ins < b->nins; i++)
				if (req(i->to, TMP(t))) {
					BSET(u, b->id);
					if (w == -1)
						w = i->wide;
					if (w != i->wide)
						/* uh, oh, warn */
						;
				}
		}
		for (;;) {
		NextBlk:
			for (n=0; !BGET(u, n); n++)
				if (n == fn->nblk)
					goto NextVar;
			BCLR(u, n);
			b = fn->rpo[n];
			if (b->visit)
				goto NextBlk;
			b->visit = 1;
			for (p=b->phi; p; p=p->link)
				for (a=0; a<p->narg; a++)
					if (req(p->arg[a], TMP(t)))
						goto NextBlk;
			p = alloc(sizeof *p);
			p->wide = w;
			p->to = TMP(t);
			p->link = b->phi;
			b->phi = p->link;
			for (n=0; n<b->nfron; n++)
				if (b->fron[n]->visit == 0)
					BSET(u, b->fron[n]->id);
		}
	NextVar:;
	}
}

void
ssa(Fn *fn)
{
	filldom(fn);
	fillfron(fn);
}
