#include "lisc.h"
#include <stdarg.h>

static void
adduse(Tmp *tmp, int ty, Blk *b, ...)
{
	Use *u;
	int n;
	va_list ap;

	va_start(ap, b);
	n = tmp->nuse;
	vgrow(&tmp->use, ++tmp->nuse);
	u = &tmp->use[n];
	u->type = ty;
	u->bid = b->id;
	switch (ty) {
	default:
		diag("ssa: adduse defaulted");
	case UPhi:
		u->u.phi = va_arg(ap, Phi *);
		break;
	case UIns:
		u->u.ins = va_arg(ap, Ins *);
		break;
	case UJmp:
		break;
	}
	va_end(ap);
}

/* fill usage and phi information
 */
void
filluse(Fn *fn)
{
	Blk *b;
	Phi *p;
	Ins *i;
	int m, t;
	uint a;
	Tmp *tmp;

	/* todo, is this the correct file? */
	tmp = fn->tmp;
	for (t=0; t<fn->ntmp; t++) {
		tmp[t].ndef = 0;
		tmp[t].nuse = 0;
		tmp[t].phi = 0;
		if (tmp[t].use == 0)
			tmp[t].use = vnew(0, sizeof(Use));
	}
	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link) {
			assert(rtype(p->to) == RTmp);
			tmp[p->to.val].ndef++;
			tmp[p->to.val].phi = p->to.val;
			for (a=0; a<p->narg; a++)
				if (rtype(p->arg[a]) == RTmp) {
					t = p->arg[a].val;
					adduse(&tmp[t], UPhi, b, p);
					if (!tmp[t].phi)
						tmp[t].phi = p->to.val;
				}
		}
		for (i=b->ins; i-b->ins < b->nins; i++) {
			if (!req(i->to, R)) {
				assert(rtype(i->to) == RTmp);
				tmp[i->to.val].ndef++;
			}
			for (m=0; m<2; m++)
				if (rtype(i->arg[m]) == RTmp) {
					t = i->arg[m].val;
					adduse(&tmp[t], UIns, b, i);
				}
		}
		if (rtype(b->jmp.arg) == RTmp)
			adduse(&tmp[b->jmp.arg.val], UJmp, b);
	}
}

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
		if (b1->id < b2->id) {
			bt = b1;
			b1 = b2;
			b2 = bt;
		}
		while (b1->id > b2->id) {
			b1 = b1->idom;
			assert(b1);
		}
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
				if (b->pred[p]->idom
				||  b->pred[p] == fn->start)
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
	assert(b1 && b2);
	if (b1 == b2)
		return 0;
	while (b2->id > b1->id)
		b2 = b2->idom;
	return b1 == b2;
}

static int
dom(Blk *b1, Blk *b2)
{
	return b1 == b2 || sdom(b1, b2);
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
			for (a=b; !sdom(a, b->s1); a=a->idom)
				addfron(a, b->s1);
		if (b->s2)
			for (a=b; !sdom(a, b->s2); a=a->idom)
				addfron(a, b->s2);
	}
}

static Ref
index(int t, Fn *fn)
{
	return newtmp(fn->tmp[t].name, fn);
}

static void
phiins(Fn *fn)
{
	Bits u, defs;
	Blk *a, *b, **blist, **be, **bp;
	Ins *i;
	Phi *p;
	Ref r;
	int t, n, w, nt;

	blist = emalloc(fn->nblk * sizeof blist[0]);
	be = &blist[fn->nblk];
	nt = fn->ntmp;
	for (t=Tmp0; t<nt; t++) {
		fn->tmp[t].visit = 0;
		if (fn->tmp[t].phi != 0)
			continue;
		BZERO(u);
		w = -1;
		bp = be;
		for (b=fn->start; b; b=b->link) {
			b->visit = 0;
			r = R;
			for (i=b->ins; i-b->ins < b->nins; i++) {
				if (!req(r, R)) {
					if (req(i->arg[0], TMP(t)))
						i->arg[0] = r;
					if (req(i->arg[1], TMP(t)))
						i->arg[1] = r;
				}
				if (req(i->to, TMP(t))) {
					if (!BGET(b->out, t)) {
						if (fn->tmp[t].ndef == 1)
							r = TMP(t);
						else
							r = index(t, fn);
						i->to = r;
					} else {
						if (!BGET(u, b->id)) {
							BSET(u, b->id);
							*--bp = b;
						}
						if (w == -1)
							w = i->wide;
						if (w != i->wide)
							/* uh, oh, warn */
							;
					}
				}
			}
			if (!req(r, R) && req(b->jmp.arg, TMP(t)))
				b->jmp.arg = r;
		}
		defs = u;
		while (bp != be) {
			fn->tmp[t].visit = t;
			b = *bp++;
			BCLR(u, b->id);
			for (n=0; n<b->nfron; n++) {
				a = b->fron[n];
				if (a->visit++ == 0)
				if (BGET(a->in, t)) {
					p = alloc(sizeof *p);
					p->wide = w;
					p->to = TMP(t);
					p->link = a->phi;
					a->phi = p;
					if (!BGET(defs, a->id))
					if (!BGET(u, a->id)) {
						BSET(u, a->id);
						*--bp = a;
					}
				}
			}
		}
	}
	free(blist);
}

typedef struct Name Name;
struct Name {
	Ref r;
	Blk *b;
	Name *up;
};

static Name *namel;

static Name *
nnew(Ref r, Blk *b, Name *up)
{
	Name *n;

	if (namel) {
		n = namel;
		namel = n->up;
	} else
		/* could use alloc, here
		 * but namel should be reset
		 */
		n = emalloc(sizeof *n);
	n->r = r;
	n->b = b;
	n->up = up;
	return n;
}

static void
nfree(Name *n)
{
	n->up = namel;
	namel = n;
}

static void
rendef(Ref *r, Blk *b, Name **stk, Fn *fn)
{
	Ref r1;
	int t;

	t = r->val;
	if (req(*r, R) || !fn->tmp[t].visit)
		return;
	r1 = index(t, fn);
	fn->tmp[r1.val].visit = t;
	stk[t] = nnew(r1, b, stk[t]);
	*r = r1;
}

static Ref
getstk(int t, Blk *b, Name **stk)
{
	Name *n, *n1;

	n = stk[t];
	while (n && !dom(n->b, b)) {
		n1 = n;
		n = n->up;
		nfree(n1);
	}
	stk[t] = n;
	if (!n) {
		/* uh, oh, warn */
		return CON_Z;
	} else
		return n->r;
}

static void
renblk(Blk *b, Name **stk, Fn *fn)
{
	Phi *p;
	Ins *i;
	Blk *s, **ps, *succ[3];
	int t, m;

	for (p=b->phi; p; p=p->link)
		rendef(&p->to, b, stk, fn);
	for (i=b->ins; i-b->ins < b->nins; i++) {
		for (m=0; m<2; m++) {
			t = i->arg[m].val;
			if (rtype(i->arg[m]) == RTmp)
			if (fn->tmp[t].visit)
				i->arg[m] = getstk(t, b, stk);
		}
		rendef(&i->to, b, stk, fn);
	}
	t = b->jmp.arg.val;
	if (rtype(b->jmp.arg) == RTmp)
	if (fn->tmp[t].visit)
		b->jmp.arg = getstk(t, b, stk);
	succ[0] = b->s1;
	succ[1] = b->s2;
	succ[2] = 0;
	for (ps=succ; (s=*ps); ps++)
		for (p=s->phi; p; p=p->link) {
			t = p->to.val;
			if ((t=fn->tmp[t].visit)) {
				m = p->narg++;
				p->arg[m] = getstk(t, b, stk);
				p->blk[m] = b;
			}
		}
	for (s=b->dom; s; s=s->dlink)
		renblk(s, stk, fn);
}

/* require ndef */
void
ssa(Fn *fn)
{
	Name **stk, *n;
	int d, nt;
	Blk *b, *b1;

	nt = fn->ntmp;
	stk = emalloc(nt * sizeof stk[0]);
	d = debug['L'];
	debug['L'] = 0;
	filldom(fn);
	if (debug['N']) {
		fprintf(stderr, "\n> Dominators:\n");
		for (b1=fn->start; b1; b1=b1->link) {
			if (!b1->dom)
				continue;
			fprintf(stderr, "%10s:", b1->name);
			for (b=b1->dom; b; b=b->dlink)
				fprintf(stderr, " %s", b->name);
			fprintf(stderr, "\n");
		}
	}
	fillfron(fn);
	filllive(fn);
	phiins(fn);
	renblk(fn->start, stk, fn);
	while (nt--)
		while ((n=stk[nt])) {
			stk[nt] = n->up;
			nfree(n);
		}
	debug['L'] = d;
	free(stk);
	if (debug['N']) {
		fprintf(stderr, "\n> After SSA construction:\n");
		printfn(fn, stderr);
	}
}
