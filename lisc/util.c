#include "lisc.h"

typedef struct Bitset Bitset;
typedef struct Vec Vec;

struct Vec {
	ulong mag;
	size_t esz;
	ulong cap;
	union {
		long long ll;
		long double ld;
		void *ptr;
	} align[];
};

enum {
	VMin = 2,
	VMag = 0xcabba9e,
	NPtr = 256,
};

Typ typ[NTyp];
Ins insb[NIns], *curi;

static void *ptr[NPtr];
static void **pool = ptr;
static int nptr = 1;

void
diag(char *s)
{
	fputs(s, stderr);
	fputc('\n', stderr);
	abort();
}

void *
emalloc(size_t n)
{
	void *p;

	p = calloc(1, n);
	if (!p)
		diag("emalloc: out of memory");
	return p;
}

void *
alloc(size_t n)
{
	void **pp;

	if (n == 0)
		return 0;
	if (nptr >= NPtr) {
		pp = emalloc(NPtr * sizeof(void *));
		pp[0] = pool;
		pool = pp;
		nptr = 1;
	}
	return pool[nptr++] = emalloc(n);
}

void
freeall()
{
	void **pp;

	for (;;) {
		for (pp = &pool[1]; pp < &pool[nptr]; pp++)
			free(*pp);
		pp = pool[0];
		if (!pp)
			break;
		free(pool);
		pool = pp;
		nptr = NPtr;
	}
	nptr = 1;
}

Blk *
bnew()
{
	static Blk z;
	Blk *b;

	b = alloc(sizeof *b);
	*b = z;
	return b;
}

void
emit(int op, int k, Ref to, Ref arg0, Ref arg1)
{
	if (curi == insb)
		diag("emit: too many instructions");
	*--curi = (Ins){
		.op = op, .cls = k,
		.to = to, .arg = {arg0, arg1}
	};
}

void
emiti(Ins i)
{
	emit(i.op, i.cls, i.to, i.arg[0], i.arg[1]);
}

void
idup(Ins **pd, Ins *s, ulong n)
{
	*pd = alloc(n * sizeof(Ins));
	memcpy(*pd, s, n * sizeof(Ins));
}

Ins *
icpy(Ins *d, Ins *s, ulong n)
{
	memcpy(d, s, n * sizeof(Ins));
	return d + n;
}

void *
vnew(ulong len, size_t esz)
{
	ulong cap;
	Vec *v;

	for (cap=VMin; cap<len; cap*=2)
		;
	v = alloc(cap * esz + sizeof(Vec));
	v->mag = VMag;
	v->cap = cap;
	v->esz = esz;
	return v + 1;
}

void
vgrow(void *vp, ulong len)
{
	Vec *v;
	void *v1;

	v = *(Vec **)vp - 1;
	assert(v+1 && v->mag == VMag);
	if (v->cap >= len)
		return;
	v1 = vnew(len, v->esz);
	memcpy(v1, v+1, v->cap * v->esz);
	*(Vec **)vp = v1;
}

int
phicls(int t, Tmp *tmp /*, int c*/)
{
	if (tmp[t].phi)
		return tmp[t].phi;
	return t;
#if 0
	int t1;

	t1 = tmp[t].phi;
	if (!t1)
		t1 = t;
	if (t != t1) {
		t1 = phitmp(t1, tmp, c);
		if (c)
			tmp[t].phi = t1;
	}
	return t1;
#endif
}

Ref
newtmp(char *prfx, Fn *fn)
{
	static int n;
	int t;

	t = fn->ntmp++;
	vgrow(&fn->tmp, fn->ntmp);
	sprintf(fn->tmp[t].name, "%s%d", prfx, ++n);
	fn->tmp[t].slot = -1;
	fn->tmp[t].nuse = +1;
	fn->tmp[t].ndef = +1;
	return TMP(t);
}

Ref
getcon(int64_t val, Fn *fn)
{
	int c;

	for (c=0; c<fn->ncon; c++)
		if (fn->con[c].type == CBits && fn->con[c].bits.i == val)
			return CON(c);
	fn->ncon++;
	vgrow(&fn->con, fn->ncon);
	fn->con[c] = (Con){.type = CBits, .bits.i = val};
	return CON(c);
}

void
addcon(Con *c0, Con *c1)
{
	if (c0->type == CUndef)
		*c0 = *c1;
	else {
		if (c1->type == CAddr) {
			if (c0->type == CAddr)
				diag("addcon: adding two addresses");
			c0->type = CAddr;
			strcpy(c0->label, c1->label);
		}
		c0->bits.i += c1->bits.i;
	}
}

void
bsinit(BSet *bs, uint n)
{
	n = (n + NBit-1) / NBit;
	bs->nt = n;
	bs->t = alloc(n * sizeof bs->t[0]);
}

uint
bscount(BSet *bs)
{
	uint i, j, n;

	n = 0;
	for (i=0; i<bs->nt; i++)
		for (j=0; j<NBit; j++)
			if (bs->t[i] & BIT(j))
				n++;
	return n;
}

static inline uint
bsmax(BSet *bs)
{
	return bs->nt * NBit;
}

int
bshas(BSet *bs, uint elt)
{
	assert(elt < bsmax(bs));
	return (bs->t[elt/NBit] & BIT(elt%NBit)) != 0;
}

void
bsset(BSet *bs, uint elt)
{
	assert(elt < bsmax(bs));
	bs->t[elt/NBit] |= BIT(elt%NBit);
}

void
bsclr(BSet *bs, uint elt)
{
	assert(elt < bsmax(bs));
	bs->t[elt/NBit] &= ~BIT(elt%NBit);
}

#define BSOP(f, op)                           \
	void                                  \
	f(BSet *a, BSet *b)                   \
	{                                     \
		uint i;                       \
		                              \
		assert(a->nt == b->nt);       \
		for (i=0; i<a->nt; i++)       \
			a->t[i] op b->t[i];   \
	}

BSOP(bscopy, =)
BSOP(bsunion, |=)
BSOP(bsinter, &=)
BSOP(bsdiff, &= ~)

int
bsequal(BSet *a, BSet *b)
{
	uint i;

	assert(a->nt == b->nt);
	for (i=0; i<a->nt; i++)
		if (a->t[i] != b->t[i])
			return 0;
	return 1;
}

void
bszero(BSet *bs)
{
	memset(bs->t, 0, bs->nt * sizeof bs->t[0]);
}

/* iterates on a bitset, use as follows
 *
 * 	for (i=0; bsiter(set, &i); i++)
 * 		use(i);
 *
 */
int
bsiter(BSet *bs, uint *elt)
{
	uint i;

	for (i=*elt;; i++) {
		while (i < bsmax(bs) && !bs->t[i/NBit])
			i = (i + NBit) & -NBit;
		if (i >= bsmax(bs))
			return 0;
		if (bshas(bs, i)) {
			*elt = i;
			return 1;
		}
	}
}

void
dumpts(BSet *bs, Tmp *tmp, FILE *f)
{
	uint t;

	fprintf(f, "[");
	for (t=Tmp0; bsiter(bs, &t); t++)
		fprintf(f, " %s", tmp[t].name);
	fprintf(f, " ]\n");
}
