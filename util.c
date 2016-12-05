#include "all.h"
#include <stdarg.h>

typedef struct Bitset Bitset;
typedef struct Vec Vec;

struct Vec {
	ulong mag;
	void *(*alloc)();
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
die_(char *file, char *s, ...)
{
	va_list ap;

	fprintf(stderr, "%s: dying: ", file);
	va_start(ap, s);
	vfprintf(stderr, s, ap);
	va_end(ap);
	fputc('\n', stderr);
	abort();
}

void *
emalloc(size_t n)
{
	void *p;

	p = calloc(1, n);
	if (!p)
		die("emalloc, out of memory");
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

void
emit(int op, int k, Ref to, Ref arg0, Ref arg1)
{
	if (curi == insb)
		die("emit, too many instructions");
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
vnew(ulong len, size_t esz, void *alloc(size_t))
{
	ulong cap;
	Vec *v;

	for (cap=VMin; cap<len; cap*=2)
		;
	v = alloc(cap * esz + sizeof(Vec));
	v->mag = VMag;
	v->cap = cap;
	v->esz = esz;
	v->alloc = alloc;
	return v + 1;
}

void
vfree(void *p)
{
	Vec *v;

	v = (Vec *)p - 1;
	assert(v->mag == VMag);
	if (v->alloc == emalloc) {
		v->mag = 0;
		free(v);
	}
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
	v1 = vnew(len, v->esz, v->alloc);
	memcpy(v1, v+1, v->cap * v->esz);
	vfree(v+1);
	*(Vec **)vp = v1;
}

int
clsmerge(short *pk, short k)
{
	short k1;

	k1 = *pk;
	if (k1 == Kx) {
		*pk = k;
		return 0;
	}
	if ((k1 == Kw && k == Kl) || (k1 == Kl && k == Kw)) {
		*pk = Kw;
		return 0;
	}
	return k1 != k;
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
newtmp(char *prfx, int k,  Fn *fn)
{
	static int n;
	int t;

	t = fn->ntmp++;
	vgrow(&fn->tmp, fn->ntmp);
	memset(&fn->tmp[t], 0, sizeof(Tmp));
	if (prfx)
		sprintf(fn->tmp[t].name, "%s.%d", prfx, ++n);
	fn->tmp[t].cls = k;
	fn->tmp[t].slot = -1;
	fn->tmp[t].nuse = +1;
	fn->tmp[t].ndef = +1;
	return TMP(t);
}

void
chuse(Ref r, int du, Fn *fn)
{
	if (rtype(r) == RTmp)
		fn->tmp[r.val].nuse += du;
}

Ref
getcon(int64_t val, Fn *fn)
{
	int c;

	for (c=0; c<fn->ncon; c++)
		if (fn->con[c].type == CBits && fn->con[c].bits.i == val)
			return CON(c);
	vgrow(&fn->con, ++fn->ncon);
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
			assert(c0->type != CAddr && "adding two addresses");
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

MAKESURE(NBit_is_64, NBit == 64);
inline static uint
popcnt(bits b)
{
	b = (b & 0x5555555555555555) + ((b>>1) & 0x5555555555555555);
	b = (b & 0x3333333333333333) + ((b>>2) & 0x3333333333333333);
	b = (b & 0x0f0f0f0f0f0f0f0f) + ((b>>4) & 0x0f0f0f0f0f0f0f0f);
	b += (b>>8);
	b += (b>>16);
	b += (b>>32);
	return b & 0xff;
}

uint
bscount(BSet *bs)
{
	uint i, n;

	n = 0;
	for (i=0; i<bs->nt; i++)
		n += popcnt(bs->t[i]);
	return n;
}

static inline uint
bsmax(BSet *bs)
{
	return bs->nt * NBit;
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
bsiter(BSet *bs, int *elt)
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
	int t;

	fprintf(f, "[");
	for (t=Tmp0; bsiter(bs, &t); t++)
		fprintf(f, " %s", tmp[t].name);
	fprintf(f, " ]\n");
}
