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

static int *val;
static Edge *flowrk, (*edge)[2];
static Use **usewrk;
static uint nuse;

static int
czero(Con *c, int w)
{
	if (c->type != CBits)
		return 0;
	if (w)
		return c->bits.i == 0;
	else
		return (uint32_t)c->bits.i == 0;
}

static int
latval(Ref r)
{
	switch (rtype(r)) {
	case RTmp:
		return val[r.val];
	case RCon:
		return r.val;
	default:
		die("unreachable");
	}
}

static int
latmerge(int v, int m)
{
	return m == Top ? v : (v == Top || v == m) ? m : Bot;
}

static void
update(int t, int m, Fn *fn)
{
	Tmp *tmp;
	uint u;

	m = latmerge(val[t], m);
	if (m != val[t]) {
		tmp = &fn->tmp[t];
		for (u=0; u<tmp->nuse; u++) {
			vgrow(&usewrk, ++nuse);
			usewrk[nuse-1] = &tmp->use[u];
		}
		val[t] = m;
	}
}

static int
deadedge(int s, int d)
{
	Edge *e;

	e = edge[s];
	if (e[0].dest == d && !e[0].dead)
		return 0;
	if (e[1].dest == d && !e[1].dead)
		return 0;
	return 1;
}

static void
visitphi(Phi *p, int n, Fn *fn)
{
	int v;
	uint a;

	v = Top;
	for (a=0; a<p->narg; a++)
		if (!deadedge(p->blk[a]->id, n))
			v = latmerge(v, latval(p->arg[a]));
	update(p->to.val, v, fn);
}

static int opfold(int, int, Con *, Con *, Fn *);

static void
visitins(Ins *i, Fn *fn)
{
	int v, l, r;

	if (rtype(i->to) != RTmp)
		return;
	if (optab[i->op].canfold) {
		l = latval(i->arg[0]);
		if (!req(i->arg[1], R))
			r = latval(i->arg[1]);
		else
			r = CON_Z.val;
		if (l == Bot || r == Bot)
			v = Bot;
		else if (l == Top || r == Top)
			v = Top;
		else
			v = opfold(i->op, i->cls, &fn->con[l], &fn->con[r], fn);
	} else
		v = Bot;
	/* fprintf(stderr, "\nvisiting %s (%p)", optab[i->op].name, (void *)i); */
	update(i->to.val, v, fn);
}

static void
visitjmp(Blk *b, int n, Fn *fn)
{
	int l;

	switch (b->jmp.type) {
	case Jjnz:
		l = latval(b->jmp.arg);
		assert(l != Top && "ssa invariant broken");
		if (l == Bot) {
			edge[n][1].work = flowrk;
			edge[n][0].work = &edge[n][1];
			flowrk = &edge[n][0];
		}
		else if (czero(&fn->con[l], 0)) {
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
	case Jjmp:
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

static int
renref(Ref *r)
{
	int l;

	if (rtype(*r) == RTmp)
		if ((l=val[r->val]) != Bot) {
			assert(l != Top && "ssa invariant broken");
			*r = CON(l);
			return 1;
		}
	return 0;
}

/* require rpo, use, pred */
void
fold(Fn *fn)
{
	Edge *e, start;
	Use *u;
	Blk *b, **pb;
	Phi *p, **pp;
	Ins *i;
	int t, d;
	uint n, a;

	val = emalloc(fn->ntmp * sizeof val[0]);
	edge = emalloc(fn->nblk * sizeof edge[0]);
	usewrk = vnew(0, sizeof usewrk[0], Pheap);

	for (t=0; t<fn->ntmp; t++)
		val[t] = Top;
	for (n=0; n<fn->nblk; n++) {
		b = fn->rpo[n];
		b->visit = 0;
		initedge(&edge[n][0], b->s1);
		initedge(&edge[n][1], b->s2);
	}
	initedge(&start, fn->start);
	flowrk = &start;
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
				for (i=b->ins; i<&b->ins[b->nins]; i++)
					visitins(i, fn);
				visitjmp(b, n, fn);
			}
			b->visit++;
			assert(b->jmp.type != Jjmp
				|| !edge[n][0].dead
				|| flowrk == &edge[n][0]);
		}
		else if (nuse) {
			u = usewrk[--nuse];
			n = u->bid;
			b = fn->rpo[n];
			if (b->visit == 0)
				continue;
			switch (u->type) {
			case UPhi:
				visitphi(u->u.phi, u->bid, fn);
				break;
			case UIns:
				visitins(u->u.ins, fn);
				break;
			case UJmp:
				visitjmp(b, n, fn);
				break;
			default:
				die("unreachable");
			}
		}
		else
			break;
	}

	if (debug['F']) {
		fprintf(stderr, "\n> SCCP findings:");
		for (t=Tmp0; t<fn->ntmp; t++) {
			if (val[t] == Bot)
				continue;
			fprintf(stderr, "\n%10s: ", fn->tmp[t].name);
			if (val[t] == Top)
				fprintf(stderr, "Top");
			else
				printref(CON(val[t]), fn, stderr);
		}
		fprintf(stderr, "\n dead code: ");
	}

	/* 2. trim dead code, replace constants */
	d = 0;
	for (pb=&fn->start; (b=*pb);) {
		if (b->visit == 0) {
			d = 1;
			if (debug['F'])
				fprintf(stderr, "%s ", b->name);
			edgedel(b, &b->s1);
			edgedel(b, &b->s2);
			*pb = b->link;
			continue;
		}
		for (pp=&b->phi; (p=*pp);)
			if (val[p->to.val] != Bot)
				*pp = p->link;
			else {
				for (a=0; a<p->narg; a++)
					if (!deadedge(p->blk[a]->id, b->id))
						renref(&p->arg[a]);
				pp = &p->link;
			}
		for (i=b->ins; i<&b->ins[b->nins]; i++)
			if (renref(&i->to))
				*i = (Ins){.op = Onop};
			else
				for (n=0; n<2; n++)
					renref(&i->arg[n]);
		renref(&b->jmp.arg);
		if (b->jmp.type == Jjnz && rtype(b->jmp.arg) == RCon) {
				if (czero(&fn->con[b->jmp.arg.val], 0)) {
					edgedel(b, &b->s1);
					b->s1 = b->s2;
					b->s2 = 0;
				} else
					edgedel(b, &b->s2);
				b->jmp.type = Jjmp;
				b->jmp.arg = R;
		}
		pb = &b->link;
	}

	if (debug['F']) {
		if (!d)
			fprintf(stderr, "(none)");
		fprintf(stderr, "\n\n> After constant folding:\n");
		printfn(fn, stderr);
	}

	free(val);
	free(edge);
	vfree(usewrk);
}

/* boring folding code */

static int
foldint(Con *res, int op, int w, Con *cl, Con *cr)
{
	union {
		int64_t s;
		uint64_t u;
		float fs;
		double fd;
	} l, r;
	uint64_t x;
	uint32_t lab;
	int typ;

	typ = CBits;
	lab = 0;
	l.s = cl->bits.i;
	r.s = cr->bits.i;
	if (op == Oadd) {
		if (cl->type == CAddr) {
			if (cr->type == CAddr)
				err("undefined addition (addr + addr)");
			lab = cl->label;
			typ = CAddr;
		}
		else if (cr->type == CAddr) {
			lab = cr->label;
			typ = CAddr;
		}
	}
	else if (op == Osub) {
		if (cl->type == CAddr) {
			if (cr->type != CAddr) {
				lab = cl->label;
				typ = CAddr;
			} else if (cl->label != cr->label)
				err("undefined substraction (addr1 - addr2)");
		}
		else if (cr->type == CAddr)
			err("undefined substraction (num - addr)");
	}
	else if (cl->type == CAddr || cr->type == CAddr) {
		if (Ocmpl <= op && op <= Ocmpl1)
			return 1;
		err("invalid address operand for '%s'", optab[op].name);
	}
	switch (op) {
	case Oadd:  x = l.u + r.u; break;
	case Osub:  x = l.u - r.u; break;
	case Odiv:  x = w ? l.s / r.s : (int32_t)l.s / (int32_t)r.s; break;
	case Orem:  x = w ? l.s % r.s : (int32_t)l.s % (int32_t)r.s; break;
	case Oudiv: x = l.u / r.u; break;
	case Ourem: x = l.u % r.u; break;
	case Omul:  x = l.u * r.u; break;
	case Oand:  x = l.u & r.u; break;
	case Oor:   x = l.u | r.u; break;
	case Oxor:  x = l.u ^ r.u; break;
	case Osar:  x = (w ? l.s : (int32_t)l.s) >> (r.u & 63); break;
	case Oshr:  x = l.u >> (r.u & 63); break;
	case Oshl:  x = l.u << (r.u & 63); break;
	case Oextsb: x = (int8_t)l.u;   break;
	case Oextub: x = (uint8_t)l.u;  break;
	case Oextsh: x = (int16_t)l.u;  break;
	case Oextuh: x = (uint16_t)l.u; break;
	case Oextsw: x = (int32_t)l.u;  break;
	case Oextuw: x = (uint32_t)l.u; break;
	case Ostosi: x = w ? (int64_t)cl->bits.s : (int32_t)cl->bits.s; break;
	case Odtosi: x = w ? (int64_t)cl->bits.d : (int32_t)cl->bits.d; break;
	case Ocast:
		x = l.u;
		if (cl->type == CAddr) {
			lab = cl->label;
			typ = CAddr;
		}
		break;
	default:
		if (Ocmpw <= op && op <= Ocmpl1) {
			if (op <= Ocmpw1) {
				l.u = (int32_t)l.u;
				r.u = (int32_t)r.u;
			} else
				op -= Ocmpl - Ocmpw;
			switch (op - Ocmpw) {
			case Ciule: x = l.u <= r.u; break;
			case Ciult: x = l.u < r.u;  break;
			case Cisle: x = l.s <= r.s; break;
			case Cislt: x = l.s < r.s;  break;
			case Cisgt: x = l.s > r.s;  break;
			case Cisge: x = l.s >= r.s; break;
			case Ciugt: x = l.u > r.u;  break;
			case Ciuge: x = l.u >= r.u; break;
			case Cieq:  x = l.u == r.u; break;
			case Cine:  x = l.u != r.u; break;
			default: die("unreachable");
			}
		}
		else if (Ocmps <= op && op <= Ocmps1) {
			switch (op - Ocmps) {
			case Cfle: x = l.fs <= r.fs; break;
			case Cflt: x = l.fs < r.fs;  break;
			case Cfgt: x = l.fs > r.fs;  break;
			case Cfge: x = l.fs >= r.fs; break;
			case Cfne: x = l.fs != r.fs; break;
			case Cfeq: x = l.fs == r.fs; break;
			case Cfo: x = l.fs < r.fs || l.fs >= r.fs; break;
			case Cfuo: x = !(l.fs < r.fs || l.fs >= r.fs); break;
			default: die("unreachable");
			}
		}
		else if (Ocmpd <= op && op <= Ocmpd1) {
			switch (op - Ocmpd) {
			case Cfle: x = l.fd <= r.fd; break;
			case Cflt: x = l.fd < r.fd;  break;
			case Cfgt: x = l.fd > r.fd;  break;
			case Cfge: x = l.fd >= r.fd; break;
			case Cfne: x = l.fd != r.fd; break;
			case Cfeq: x = l.fd == r.fd; break;
			case Cfo: x = l.fd < r.fd || l.fd >= r.fd; break;
			case Cfuo: x = !(l.fd < r.fd || l.fd >= r.fd); break;
			default: die("unreachable");
			}
		}
		else
			die("unreachable");
	}
	*res = (Con){.type=typ, .label=lab, .bits={.i=x}};
	return 0;
}

static void
foldflt(Con *res, int op, int w, Con *cl, Con *cr)
{
	float xs, ls, rs;
	double xd, ld, rd;

	if (cl->type != CBits || cr->type != CBits)
		err("invalid address operand for '%s'", optab[op].name);
	if (w)  {
		ld = cl->bits.d;
		rd = cr->bits.d;
		switch (op) {
		case Oadd: xd = ld + rd; break;
		case Osub: xd = ld - rd; break;
		case Odiv: xd = ld / rd; break;
		case Omul: xd = ld * rd; break;
		case Oswtof: xd = (int32_t)cl->bits.i; break;
		case Osltof: xd = (int64_t)cl->bits.i; break;
		case Oexts: xd = cl->bits.s; break;
		case Ocast: xd = ld; break;
		default: die("unreachable");
		}
		*res = (Con){CBits, .bits={.d=xd}, .flt=2};
	} else {
		ls = cl->bits.s;
		rs = cr->bits.s;
		switch (op) {
		case Oadd: xs = ls + rs; break;
		case Osub: xs = ls - rs; break;
		case Odiv: xs = ls / rs; break;
		case Omul: xs = ls * rs; break;
		case Oswtof: xs = (int32_t)cl->bits.i; break;
		case Osltof: xs = (int64_t)cl->bits.i; break;
		case Otruncd: xs = cl->bits.d; break;
		case Ocast: xs = ls; break;
		default: die("unreachable");
		}
		*res = (Con){CBits, .bits={.s=xs}, .flt=1};
	}
}

static int
opfold(int op, int cls, Con *cl, Con *cr, Fn *fn)
{
	int nc;
	Con c;

	if ((op == Odiv || op == Oudiv
	|| op == Orem || op == Ourem) && czero(cr, KWIDE(cls)))
		return Bot;
	if (cls == Kw || cls == Kl) {
		if (foldint(&c, op, cls == Kl, cl, cr))
			return Bot;
	} else
		foldflt(&c, op, cls == Kd, cl, cr);
	if (c.type == CBits)
		nc = getcon(c.bits.i, fn).val;
	else {
		nc = fn->ncon;
		vgrow(&fn->con, ++fn->ncon);
	}
	assert(!(cls == Ks || cls == Kd) || c.flt);
	fn->con[nc] = c;
	return nc;
}
