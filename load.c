#include "all.h"

#define MASK(w) (BIT(8*(w)-1)*2-1) /* must work when w==8 */

typedef struct Loc Loc;
typedef struct Slice Slice;
typedef struct Insert Insert;


struct Loc {
	enum {
		LRoot,   /* right above the original load */
		LLoad,   /* inserting a load is allowed */
		LNoLoad, /* only scalar operations allowed */
	} type;
	uint off;
	Blk *blk;
};

struct Slice {
	Ref ref;
	short sz;
	short cls; /* load class */
};

struct Insert {
	uint isphi:1;
	uint num:31;
	uint bid;
	uint off;
	union {
		Ins ins;
		struct {
			Slice m;
			Phi *p;
		} phi;
	} new;
};

static Fn *curf;
static uint inum;    /* current insertion number */
static Insert *ilog; /* global insertion log */
static uint nlog;    /* number of entries in the log */

int
loadsz(Ins *l)
{
	switch (l->op) {
	case Oloadsb: case Oloadub: return 1;
	case Oloadsh: case Oloaduh: return 2;
	case Oloadsw: case Oloaduw: return 4;
	case Oload: return KWIDE(l->cls) ? 8 : 4;
	}
	die("unreachable");
}

int
storesz(Ins *s)
{
	switch (s->op) {
	case Ostoreb: return 1;
	case Ostoreh: return 2;
	case Ostorew: case Ostores: return 4;
	case Ostorel: case Ostored: return 8;
	}
	die("unreachable");
}

static Ref
iins(int cls, int op, Ref a0, Ref a1, Loc *l)
{
	Insert *ist;

	vgrow(&ilog, ++nlog);
	ist = &ilog[nlog-1];
	ist->isphi = 0;
	ist->num = inum++;
	ist->bid = l->blk->id;
	ist->off = l->off;
	ist->new.ins = (Ins){op, cls, R, {a0, a1}};
	return ist->new.ins.to = newtmp("ld", cls, curf);
}

static void
cast(Ref *r, int cls, Loc *l)
{
	int cls0;

	if (rtype(*r) == RCon)
		return;
	assert(rtype(*r) == RTmp);
	cls0 = curf->tmp[r->val].cls;
	if (cls0 == cls || (cls == Kw && cls0 == Kl))
		return;
	if (KWIDE(cls0) < KWIDE(cls)) {
		if (cls0 == Ks)
			*r = iins(Kw, Ocast, *r, R, l);
		*r = iins(Kl, Oextuw, *r, R, l);
		if (cls == Kd)
			*r = iins(Kd, Ocast, *r, R, l);
	} else {
		if (cls0 == Kd && cls != Kl)
			*r = iins(Kl, Ocast, *r, R, l);
		if (cls0 != Kd || cls != Kw)
			*r = iins(cls, Ocast, *r, R, l);
	}
}

static inline void
mask(int cls, Ref *r, bits msk, Loc *l)
{
	cast(r, cls, l);
	*r = iins(cls, Oand, *r, getcon(msk, curf), l);
}

static Ref
load(Slice sl, bits msk, Loc *l)
{
	Alias *a;
	Ref r, r1;
	int ld, cls, all;
	Con c;

	ld = (int[]){
		[1] = Oloadub,
		[2] = Oloaduh,
		[4] = Oloaduw,
		[8] = Oload
	}[sl.sz];
	all = msk == MASK(sl.sz);
	if (all)
		cls = sl.cls;
	else
		cls = sl.sz > 4 ? Kl : Kw;
	r = sl.ref;
	/* sl.ref might not be live here,
	 * but its alias base ref will be
	 * (see killsl() below) */
	if (rtype(r) == RTmp) {
		a = &curf->tmp[r.val].alias;
		switch (a->type) {
		default:
			die("unreachable");
		case ALoc:
		case AEsc:
		case AUnk:
			r = a->base;
			if (!a->offset)
				break;
			r1 = getcon(a->offset, curf);
			r = iins(Kl, Oadd, r, r1, l);
			break;
		case ACon:
		case ASym:
			c.type = CAddr;
			c.label = a->label;
			c.bits.i = a->offset;
			c.local = 0;
			r = newcon(&c, curf);
			break;
		}
	}
	r = iins(cls, ld, r, R, l);
	if (!all)
		mask(cls, &r, msk, l);
	return r;
}

static int
killsl(Ref r, Slice sl)
{
	Alias *a;

	if (rtype(sl.ref) != RTmp)
		return 0;
	a = &curf->tmp[sl.ref.val].alias;
	switch (a->type) {
	default:   die("unreachable");
	case ALoc:
	case AEsc:
	case AUnk: return req(a->base, r);
	case ACon:
	case ASym: return 0;
	}
}

/* returns a ref containing the contents of the slice
 * passed as argument, all the bits set to 0 in the
 * mask argument are zeroed in the result;
 * the returned ref has an integer class when the
 * mask does not cover all the bits of the slice,
 * otherwise, it has class sl.cls
 * the procedure returns R when it fails */
static Ref
def(Slice sl, bits msk, Blk *b, Ins *i, Loc *il)
{
	Blk *bp;
	bits msk1, msks;
	int off, cls, cls1, op, sz, ld;
	uint np, oldl, oldt;
	Ref r, r1;
	Phi *p;
	Insert *ist;
	Loc l;

	/* invariants:
	 * -1- b dominates il->blk; so we can use
	 *     temporaries of b in il->blk
	 * -2- if il->type != LNoLoad, then il->blk
	 *     postdominates the original load; so it
	 *     is safe to load in il->blk
	 * -3- if il->type != LNoLoad, then b
	 *     postdominates il->blk (and by 2, the
	 *     original load)
	 */
	assert(dom(b, il->blk));
	oldl = nlog;
	oldt = curf->ntmp;
	if (0) {
	Load:
		curf->ntmp = oldt;
		nlog = oldl;
		if (il->type != LLoad)
			return R;
		return load(sl, msk, il);
	}

	if (!i)
		i = &b->ins[b->nins];
	cls = sl.sz > 4 ? Kl : Kw;
	msks = MASK(sl.sz);

	while (i > b->ins) {
		--i;
		if (killsl(i->to, sl)
		|| (i->op == Ocall && escapes(sl.ref, curf)))
			goto Load;
		ld = isload(i->op);
		if (ld) {
			sz = loadsz(i);
			r1 = i->arg[0];
			r = i->to;
		} else if (isstore(i->op)) {
			sz = storesz(i);
			r1 = i->arg[1];
			r = i->arg[0];
		} else
			continue;
		switch (alias(sl.ref, sl.sz, r1, sz, &off, curf)) {
		case MustAlias:
			if (off < 0) {
				off = -off;
				msk1 = (MASK(sz) << 8*off) & msks;
				op = Oshl;
			} else {
				msk1 = (MASK(sz) >> 8*off) & msks;
				op = Oshr;
			}
			if ((msk1 & msk) == 0)
				break;
			if (off) {
				cls1 = cls;
				if (op == Oshr && off + sl.sz > 4)
					cls1 = Kl;
				cast(&r, cls1, il);
				r1 = getcon(8*off, curf);
				r = iins(cls1, op, r, r1, il);
			}
			if ((msk1 & msk) != msk1 || off + sz < sl.sz)
				mask(cls, &r, msk1 & msk, il);
			if ((msk & ~msk1) != 0) {
				r1 = def(sl, msk & ~msk1, b, i, il);
				if (req(r1, R))
					goto Load;
				r = iins(cls, Oor, r, r1, il);
			}
			if (msk == msks)
				cast(&r, sl.cls, il);
			return r;
		case MayAlias:
			if (ld)
				break;
			else
				goto Load;
		case NoAlias:
			break;
		default:
			die("unreachable");
		}
	}

	for (ist=ilog; ist<&ilog[nlog]; ++ist)
		if (ist->isphi && ist->bid == b->id)
		if (req(ist->new.phi.m.ref, sl.ref))
		if (ist->new.phi.m.sz == sl.sz) {
			r = ist->new.phi.p->to;
			if (msk != msks)
				mask(cls, &r, msk, il);
			else
				cast(&r, sl.cls, il);
			return r;
		}

	for (p=b->phi; p; p=p->link)
		if (killsl(p->to, sl))
			/* scanning predecessors in that
			 * case would be unsafe */
			goto Load;

	if (b->npred == 0)
		goto Load;
	if (b->npred == 1) {
		bp = b->pred[0];
		assert(bp->loop >= il->blk->loop);
		l = *il;
		if (bp->s2)
			l.type = LNoLoad;
		r1 = def(sl, msk, bp, 0, &l);
		if (req(r1, R))
			goto Load;
		return r1;
	}

	r = newtmp("ld", sl.cls, curf);
	p = alloc(sizeof *p);
	vgrow(&ilog, ++nlog);
	ist = &ilog[nlog-1];
	ist->isphi = 1;
	ist->bid = b->id;
	ist->new.phi.m = sl;
	ist->new.phi.p = p;
	p->to = r;
	p->cls = sl.cls;
	p->narg = b->npred;
	p->arg = vnew(p->narg, sizeof p->arg[0], Pfn);
	p->blk = vnew(p->narg, sizeof p->blk[0], Pfn);
	for (np=0; np<b->npred; ++np) {
		bp = b->pred[np];
		if (!bp->s2
		&& il->type != LNoLoad
		&& bp->loop < il->blk->loop)
			l.type = LLoad;
		else
			l.type = LNoLoad;
		l.blk = bp;
		l.off = bp->nins;
		r1 = def(sl, msks, bp, 0, &l);
		if (req(r1, R))
			goto Load;
		p->arg[np] = r1;
		p->blk[np] = bp;
	}
	if (msk != msks)
		mask(cls, &r, msk, il);
	return r;
}

static int
icmp(const void *pa, const void *pb)
{
	Insert *a, *b;
	int c;

	a = (Insert *)pa;
	b = (Insert *)pb;
	if ((c = a->bid - b->bid))
		return c;
	if (a->isphi && b->isphi)
		return 0;
	if (a->isphi)
		return -1;
	if (b->isphi)
		return +1;
	if ((c = a->off - b->off))
		return c;
	return a->num - b->num;
}

/* require rpo ssa alias */
void
loadopt(Fn *fn)
{
	Ins *i, *ib;
	Blk *b;
	int sz;
	uint n, ni, ext, nt;
	Insert *ist;
	Slice sl;
	Loc l;

	curf = fn;
	ilog = vnew(0, sizeof ilog[0], Pheap);
	nlog = 0;
	inum = 0;
	for (b=fn->start; b; b=b->link)
		for (i=b->ins; i<&b->ins[b->nins]; ++i) {
			if (!isload(i->op))
				continue;
			sz = loadsz(i);
			sl = (Slice){i->arg[0], sz, i->cls};
			l = (Loc){LRoot, i-b->ins, b};
			i->arg[1] = def(sl, MASK(sz), b, i, &l);
		}
	qsort(ilog, nlog, sizeof ilog[0], icmp);
	vgrow(&ilog, nlog+1);
	ilog[nlog].bid = fn->nblk; /* add a sentinel */
	ib = vnew(0, sizeof(Ins), Pheap);
	for (ist=ilog, n=0; n<fn->nblk; ++n) {
		b = fn->rpo[n];
		for (; ist->bid == n && ist->isphi; ++ist) {
			ist->new.phi.p->link = b->phi;
			b->phi = ist->new.phi.p;
		}
		ni = 0;
		nt = 0;
		for (;;) {
			if (ist->bid == n && ist->off == ni)
				i = &ist++->new.ins;
			else {
				if (ni == b->nins)
					break;
				i = &b->ins[ni++];
				if (isload(i->op)
				&& !req(i->arg[1], R)) {
					ext = Oextsb + i->op - Oloadsb;
					switch (i->op) {
					default:
						die("unreachable");
					case Oloadsb:
					case Oloadub:
					case Oloadsh:
					case Oloaduh:
						i->op = ext;
						break;
					case Oloadsw:
					case Oloaduw:
						if (i->cls == Kl) {
							i->op = ext;
							break;
						}
						/* fall through */
					case Oload:
						i->op = Ocopy;
						break;
					}
					i->arg[0] = i->arg[1];
					i->arg[1] = R;
				}
			}
			vgrow(&ib, ++nt);
			ib[nt-1] = *i;
		}
		b->nins = nt;
		idup(&b->ins, ib, nt);
	}
	vfree(ib);
	vfree(ilog);
	if (debug['M']) {
		fprintf(stderr, "\n> After load elimination:\n");
		printfn(fn, stderr);
	}
}
