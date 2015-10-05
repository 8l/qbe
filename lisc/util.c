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
	const uint64_t m1 = 0x5555555555555555;
	const uint64_t m2 = 0x3333333333333333;
	const uint64_t m3 = 0x0f0f0f0f0f0f0f0f;
	const uint64_t m4 = 0x00ff00ff00ff00ff;
	const uint64_t m5 = 0x0000ffff0000ffff;
	const uint64_t m6 = 0x00000000ffffffff;
	uint64_t tmp;
	int z, i;

	i = 0;
	for (z=0; z<BITS; z++) {
		tmp = b->t[z];
		if (!tmp)
			continue;
		tmp = (tmp&m1) + (tmp>> 1&m1);
		tmp = (tmp&m2) + (tmp>> 2&m2);
		tmp = (tmp&m3) + (tmp>> 4&m3);
		tmp = (tmp&m4) + (tmp>> 8&m4);
		tmp = (tmp&m5) + (tmp>>16&m5);
		tmp = (tmp&m6) + (tmp>>32&m6);
		i += tmp;
	}
	return i;
}
