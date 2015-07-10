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
	if (b->rpo >= 0)
		return x;
	if (b->s1)
		x = rporec(b->s1, x);
	if (b->s2)
		x = rporec(b->s2, x);
	b->rpo = x;
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
		b->rpo = -1;
	n = 1 + rporec(f->start, f->nblk-1);
	f->nblk -= n;
	free(f->rpo);
	f->rpo = alloc(f->nblk * sizeof f->rpo[0]);
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

static Ref topdef(int, Blk *, Fn *, Ref *, Ref *);

static Ref
botdef(int t, Blk *b, Fn *f, Ref *top, Ref *bot)
{
	Ref r;

	if (bot[b->rpo] != R)
		return bot[b->rpo];
	r = topdef(t, b, f, top, bot);
	bot[b->rpo] = r;
	return r;
}

static Ref
topdef(int t, Blk *b, Fn *f, Ref *top, Ref *bot)
{
	int i, t1;
	Ref r;
	Phi *p;

	if (top[b->rpo] != R)
		return top[b->rpo];
	if (b->npreds == 1) {
		r = botdef(t, b->preds[0], f, top, bot);
		top[b->rpo] = r;
		return r;
	}
	/* add a phi node */
	t1 = f->ntmp++;
	r = SYM(t1);
	bot[b->rpo] = r;
	b->np++;
	b->ps = realloc(b->ps, b->np * sizeof b->ps[0]);   // nope, we iterate on that
	assert(b->ps); /* todo, move this elsewhere */
	p = &b->ps[b->np-1];
	p->to = r;
	for (i=0; i<b->npreds; i++)
		p->args[i] = botdef(t, b->preds[i], f, top, bot);
	p->na = i;
	return r;
}

/* restore ssa form for a temporary t
 * predecessors and rpo must be available
 */
void
ssafix(Fn *f, int t)
{
	int i, t1;
	Ref rt, *top, *bot;
	Blk *b;
	Phi *phi;
	Ins *ins;

	top = alloc(f->nblk * sizeof top[0]);
	bot = alloc(f->nblk * sizeof bot[0]);
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
		top[b->rpo] = R;
		bot[b->rpo] = t1 ? SYM(t1) : R;
	}
	for (b=f->start; b; b=b->link) {
		for (phi=b->ps; phi-b->ps < b->np; phi++)
			for (i=0; i<phi->na; i++) {
				if (phi->args[i] != rt)
					continue;
				phi->args[i] = topdef(t, b, f, top, bot);
			}
		for (ins=b->is; ins-b->is < b->ni; ins++) {
			if (ins->l == rt)
				ins->l = topdef(t, b, f, top, bot);
			if (ins->r == rt)
				ins->r = topdef(t, b, f, top, bot);
		}
	}
	free(top);
	free(bot);
}
