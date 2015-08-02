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
		free(b->pred);
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
	if (b->id >= 0)
		return x;
	b->id = 1;
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

static Ref *top, *bot;
static Ref topdef(Blk *, Fn *);

static Ref
botdef(Blk *b, Fn *f)
{
	Ref r;

	if (!req(bot[b->id], R))
		return bot[b->id];
	r = topdef(b, f);
	bot[b->id] = r;
	return r;
}

static Ref
topdef(Blk *b, Fn *f)
{
	uint i;
	int s1;
	Ref r;
	Phi *p;

	if (!req(top[b->id], R))
		return top[b->id];
	assert(b->npred && "invalid ssa program detected");
	if (b->npred == 1) {
		r = botdef(b->pred[0], f);
		top[b->id] = r;
		return r;
	}
	/* add a phi node */
	s1 = f->nsym++;
	r = SYM(s1);
	top[b->id] = r;
	p = alloc(sizeof *p);
	p->link = b->phi;
	b->phi = p;
	p->to = r;
	for (i=0; i<b->npred; i++) {
		p->arg[i] = botdef(b->pred[i], f);
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
	int s0, s1;
	Ref rt;
	Blk *b;
	Phi *p;
	Ins *i;

	top = alloc(f->nblk * sizeof top[0]);
	bot = alloc(f->nblk * sizeof bot[0]);
	rt = SYM(t);
	s0 = f->nsym;
	for (b=f->start; b; b=b->link) {
		s1 = 0;
		/* rename defs and some in-blocks uses */
		for (p=b->phi; p; p=p->link)
			if (req(p->to, rt)) {
				s1 = f->nsym++;
				p->to = SYM(s1);
			}
		for (i=b->ins; i-b->ins < b->nins; i++) {
			if (s1) {
				if (req(i->arg[0], rt))
					i->arg[0] = SYM(s1);
				if (req(i->arg[1], rt))
					i->arg[1] = SYM(s1);
			}
			if (req(i->to, rt)) {
				s1 = f->nsym++;
				i->to = SYM(s1);
			}
		}
		if (s1 && req(b->jmp.arg, rt))
			b->jmp.arg = SYM(s1);
		top[b->id] = R;
		bot[b->id] = s1 ? SYM(s1) : R;
	}
	for (b=f->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link)
			for (n=0; n<p->narg; n++)
				if (req(p->arg[n], rt))
					p->arg[n] = botdef(p->blk[n], f);
		for (i=b->ins; i-b->ins < b->nins; i++) {
			if (req(i->arg[0], rt))
				i->arg[0] = topdef(b, f);
			if (req(i->arg[1], rt))
				i->arg[1] = topdef(b, f);
		}
		if (req(b->jmp.arg, rt))
			b->jmp.arg = topdef(b, f);
	}
	/* add new symbols */
	f->sym = realloc(f->sym, f->nsym * sizeof f->sym[0]);
	if (!f->sym)
		diag("ssafix: out of memory");
	for (s1=s0; s0<f->nsym; s0++) {
		f->sym[s0] = f->sym[t];
		snprintf(f->sym[s0].name, NString, "%s%d",
			f->sym[t].name, s0-s1);
	}
	free(top);
	free(bot);
}
