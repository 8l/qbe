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
