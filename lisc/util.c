#include "lisc.h"

Typ typ[NTyp];
int ntyp;
Ins insb[NIns], *curi;

void
diag(char *s)
{
	fputs(s, stderr);
	fputc('\n', stderr);
	abort();
}

void *
alloc(size_t n)
{
	void *p;

	if (n == 0)
		return 0;
	p = calloc(1, n);
	if (!p)
		abort();
	return p;
}

Blk *
blocka()
{
	static Blk z;
	Blk *b;

	b = alloc(sizeof *b);
	*b = z;
	return b;
}

void
emit(int op, int w, Ref to, Ref arg0, Ref arg1)
{
	if (curi == insb)
		diag("emit: too many instructions");
	*--curi = (Ins){op, w, to, {arg0, arg1}};
}

void
emiti(Ins i)
{
	emit(i.op, i.wide, i.to, i.arg[0], i.arg[1]);
}

int
bcnt(Bits *b)
{
	int z, i, j;
	ulong tmp;

	i = 0;
	for (z=0; z<BITS; z++) {
		tmp = b->t[z];
		for (j=0; j<64; j++) {
			i += 1 & tmp;
			tmp >>= 1;
		}
	}
	return i;
}
