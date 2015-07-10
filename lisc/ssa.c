#include "lisc.h"

static void
addpred(Blk *bp, Blk *bc)
{
	int i;

	if (!bc->preds) {
		bc->preds = alloc(bc->npreds * sizeof(Blk*));
		for (i=0; i<bc->npreds; i++)
			bc->preds[i] = 0;
	}
	for (i=0; bc->preds[i]; i++)
		;
	bc->preds[i] = bp;
}

void
fillpreds(Fn *f)
{
	Blk *b;

	for (b=f->start; b; b=b->link) {
		b->npreds = 0;
		free(b->preds);
		b->preds = 0;
	}
	for (b=f->start; b; b=b->link) {
		if (b->s1)
			b->s1->npreds++;
		if (b->s2)
			b->s2->npreds++;
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
	if (b->rpo >= 0)
		return x;
	if (b->s1)
		x = rporec(b->s1, x);
	if (b->s2)
		x = rporec(b->s2, x);
	b->rpo = x;
	return x - 1;
}

void
fillrpo(Fn *f)
{
	int n;
	Blk *b, **p;

	for (b=f->start; b; b=b->link)
		b->rpo = -1;
	n = rporec(f->start, f->nblk-1);
	f->rpo = alloc(n * sizeof(Blk*));
	for (p=&f->start; *p;) {
		b = *p;
		if (b->rpo == -1) {
			*p = b->link;
			/* todo, free block */
		} else {
			b->rpo -= n;
			f->rpo[b->rpo] = b;
			p=&(*p)->link;
		}
	}
}

void
ssafix(Fn *f, Ref v)
{
	(void)f;
	(void)v;
	return;
}
