#include "all.h"

enum {
	Bot = -2, /* lattice bottom */
	Top = -1, /* lattice top */
};

typedef struct Edge Edge;

struct Edge {
	int dest;
	int dead;
	Edge *work;
};

int evalop(int, int, int, int);

static int *val;
static Edge *flowrk, (*edge)[2];
static Use **usewrk;
static uint nuse;

static int
czero(Con *c)
{
	return c->type == CBits && c->bits.i == 0;
}

static int
latval(Ref r)
{
	switch (rtype(r)) {
	case RTmp:
		return val[r.val];
	case RCon:
		return r.val;
	case RType:
		return Bot;
	default:
		die("unreachable");
	}
}

static int
latmerge(int l, int r)
{
	if (l == Bot || r == Bot)
		return Bot;
	if (l == Top)
		return r;
	if (r == Top)
		return l;
	if (l == r)
		return l;
	return Bot;
}

static void
update(int t, int v, Fn *fn)
{
	Tmp *tmp;
	uint u;

	if (val[t] != v) {
		tmp = &fn->tmp[t];
		for (u=0; u<tmp->nuse; u++) {
			vgrow(usewrk, ++nuse);
			usewrk[nuse-1] = &tmp->use[u];
		}
	}
}

static void
visitphi(Phi *p, int n, Fn *fn)
{
	int v, dead;
	uint a;

	v = Top;
	for (a=0; a<p->narg; a++) {
		if (edge[n][0].dest == p->blk[a]->id)
			dead = edge[n][0].dead;
		else
			dead = edge[n][1].dead;
		if (!dead)
			v = latmerge(v, latval(p->arg[a]));
	}
	assert(v != Top);
	update(p->to.val, v, fn);
}

static void
visitins(Ins *i, Fn *fn)
{
	int v, l, r;

	if (rtype(i->to) != RTmp)
		return;
	l = latval(i->arg[0]);
	r = latval(i->arg[1]);
	v = evalop(i->op, i->cls, l, r);
	assert(v != Top);
	update(i->to.val, v, fn);
}

static void
visitjmp(Blk *b, int n, Fn *fn)
{
	int l;

	switch (b->jmp.type) {
	case JJnz:
		l = latval(b->jmp.arg);
		if (l == Bot) {
			edge[n][1].work = flowrk;
			edge[n][0].work = &edge[n][1];
			flowrk = &edge[n][0];
		}
		else if (czero(&fn->con[l])) {
			assert(edge[n][0].dead);
			edge[n][1].work = flowrk;
			flowrk = &edge[n][1];
		}
		else {
			assert(edge[n][1].dead);
			edge[n][0].work = flowrk;
			flowrk = &edge[n][0];
		}
		break;
	case JJmp:
		edge[n][0].work = flowrk;
		flowrk = &edge[n][0];
		break;
	default:
		if (isret(b->jmp.type))
			break;
		die("unreachable");
	}
}

static void
initedge(Edge *e, Blk *s)
{
	if (s)
		e->dest = s->id;
	else
		e->dest = -1;
	e->dead = 1;
	e->work = 0;
}

/* require rpo, use, pred */
void
fold(Fn *fn)
{
	Edge *e;
	Use *u;
	Blk *b;
	Phi *p;
	Ins *i;
	int n;

	val = emalloc(fn->ntmp * sizeof val[0]);
	edge = emalloc(fn->nblk * sizeof edge[0]);
	usewrk = vnew(0, sizeof usewrk[0]);

	for (n=0; n<fn->ntmp; n++)
		val[n] = Bot;
	for (n=0; n<fn->nblk; n++) {
		b = fn->rpo[n];
		b->visit = 0;
		initedge(&edge[n][0], b->s1);
		initedge(&edge[n][1], b->s2);
	}
	assert(fn->start->id == 0);
	edge[0][0].work = &edge[0][1];
	flowrk = &edge[0][0];
	nuse = 0;

	/* 1. find out constants and dead cfg edges */
	for (;;) {
		e = flowrk;
		if (e) {
			flowrk = e->work;
			e->work = 0;
			if (e->dest == -1 || !e->dead)
				continue;
			e->dead = 0;
			n = e->dest;
			b = fn->rpo[n];
			for (p=b->phi; p; p=p->link)
				visitphi(p, n, fn);
			if (b->visit == 0) {
				for (i=b->ins; i-b->ins < b->nins; i++)
					visitins(i, fn);
				visitjmp(b, n, fn);
			}
			b->visit++;
			assert(b->jmp.type != JJmp
				|| edge[n][0].dead != 0
				|| flowrk == &edge[n][0]);
		}
		else if (nuse) {
			u = usewrk[--nuse];
			if (u->type == UPhi) {
				visitphi(u->u.phi, u->bid, fn);
				continue;
			}
			if (b->visit == 0)
				continue;
			n = u->bid;
			switch (u->type) {
			case UIns:
				visitins(u->u.ins, fn);
				break;
			case UJmp:
				visitjmp(fn->rpo[n], n, fn);
				break;
			default:
				die("unreachable");
			}
		}
		else
			break;
	}

	/* 2. trim dead code, replace constants */

	free(val);
	free(edge);
}
