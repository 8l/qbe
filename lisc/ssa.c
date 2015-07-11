#include "lisc.h"

static void
addpred(Blk *bp, Blk *bc)
{
	int i;

	if (!bc->preds) {
		bc->preds = alloc(bc->npreds * sizeof bc->preds[0]);
		for (i=0; i<bc->npreds; i++)
			bc->preds[i] = 0;
	}
	for (i=0; bc->preds[i]; i++)
		;
	bc->preds[i] = bp;
}

/* fill predecessors information in blocks
 */
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
	if (b->id >= 0)
		return x;
	if (b->s1)
		x = rporec(b->s1, x);
	if (b->s2)
		x = rporec(b->s2, x);
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
	free(f->rpo);
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

static Ref topdef(Blk *, Fn *, Ref *, Ref *, Phi *);

static Ref
botdef(Blk *b, Fn *f, Ref *top, Ref *bot, Phi *fix)
{
	Ref r;

	if (bot[b->id] != R)
		return bot[b->id];
	r = topdef(b, f, top, bot, fix);
	bot[b->id] = r;
	return r;
}

static Ref
topdef(Blk *b, Fn *f, Ref *top, Ref *bot, Phi *fix)
{
	int i, t1;
	Ref r;
	Phi *p;

	if (top[b->id] != R)
		return top[b->id];
	assert(b->npreds && "invalid ssa program detected");
	if (b->npreds == 1) {
		r = botdef(b->preds[0], f, top, bot, fix);
		top[b->id] = r;
		return r;
	}
	/* add a phi node */
	t1 = f->ntmp++;
	r = SYM(t1);
	top[b->id] = r;
	b->np++;
	p = &fix[b->id];
	p->to = r;
	for (i=0; i<b->npreds; i++)
		p->args[i] = botdef(b->preds[i], f, top, bot, fix);
	p->na = i;
	return r;
}

/* restore ssa form for a temporary t
 * predecessors must be available
 */
void
ssafix(Fn *f, int t)
{
	int i, t1;
	Ref rt, *top, *bot;
	Blk *b;
	Phi *phi, *fix;
	Ins *ins;

	top = alloc(f->nblk * sizeof top[0]);
	bot = alloc(f->nblk * sizeof bot[0]);
	fix = alloc(f->nblk * sizeof fix[0]);
	rt = SYM(t);
	for (b=f->start; b; b=b->link) {
		t1 = 0;
		/* rename defs and some in-blocks uses */
		for (phi=b->ps; phi-b->ps < b->np; phi++) {
			if (t1)
				for (i=0; i<phi->na; i++)
					if (phi->args[i] == rt)
						phi->args[i] = SYM(t1);
			if (phi->to == rt) {
				t1 = f->ntmp++;
				phi->to = SYM(t1);
			}
		}
		for (ins=b->is; ins-b->is < b->ni; ins++) {
			if (t1) {
				if (ins->l == rt)
					ins->l = SYM(t1);
				if (ins->r == rt)
					ins->r = SYM(t1);
			}
			if (ins->to == rt) {
				t1 = f->ntmp++;
				ins->to = SYM(t1);
			}
		}
		top[b->id] = R;
		bot[b->id] = t1 ? SYM(t1) : R;
		fix[b->id].to = R;
	}
	for (b=f->start; b; b=b->link) {
		for (phi=b->ps; phi-b->ps < b->np; phi++)
			for (i=0; i<phi->na; i++) {
				if (phi->args[i] != rt)
					continue;
				// use botdef of the parent block
				// corresponding to the phi branch!
				phi->args[i] = botdef(b, f, top, bot, fix);
			}
		for (ins=b->is; ins-b->is < b->ni; ins++) {
			if (ins->l == rt)
				ins->l = topdef(b, f, top, bot, fix);
			if (ins->r == rt)
				ins->r = topdef(b, f, top, bot, fix);
		}
	}

	// fixup phis

	free(fix);
	free(top);
	free(bot);
}
