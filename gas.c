#include "all.h"


char *gasloc, *gassym;

void
gasemitdat(Dat *d, FILE *f)
{
	static int align;
	static char *dtoa[] = {
		[DAlign] = ".align",
		[DB] = "\t.byte",
		[DH] = "\t.short",
		[DW] = "\t.int",
		[DL] = "\t.quad"
	};

	switch (d->type) {
	case DStart:
		align = 0;
		fprintf(f, ".data\n");
		break;
	case DEnd:
		break;
	case DName:
		if (!align)
			fprintf(f, ".align 8\n");
		if (d->export)
			fprintf(f, ".globl %s%s\n", gassym, d->u.str);
		fprintf(f, "%s%s:\n", gassym, d->u.str);
		break;
	case DZ:
		fprintf(f, "\t.fill %"PRId64",1,0\n", d->u.num);
		break;
	default:
		if (d->type == DAlign)
			align = 1;

		if (d->isstr) {
			if (d->type != DB)
				err("strings only supported for 'b' currently");
			fprintf(f, "\t.ascii \"%s\"\n", d->u.str);
		}
		else if (d->isref) {
			fprintf(f, "%s %s%+"PRId64"\n",
				dtoa[d->type], d->u.ref.nam,
				d->u.ref.off);
		}
		else {
			fprintf(f, "%s %"PRId64"\n",
				dtoa[d->type], d->u.num);
		}
		break;
	}
}

typedef struct FBits FBits;

struct FBits {
	union {
		int64_t n;
		float f;
		double d;
	} bits;
	int wide;
	FBits *link;
};

static FBits *stash;

int
gasstashfp(int64_t n, int w)
{
	FBits **pb, *b;
	int i;

	/* does a dumb de-dup of fp constants
	 * this should be the linker's job */
	for (pb=&stash, i=0; (b=*pb); pb=&b->link, i++)
		if (n == b->bits.n && w == b->wide)
			return i;
	b = emalloc(sizeof *b);
	b->bits.n = n;
	b->wide = w;
	b->link = 0;
	*pb = b;
	return i;
}

void
gasemitfin(FILE *f)
{
	FBits *b;
	int i;

	if (!stash)
		return;
	fprintf(f, "/* floating point constants */\n");
	fprintf(f, ".data\n.align 8\n");
	for (b=stash, i=0; b; b=b->link, i++)
		if (b->wide)
			fprintf(f,
				"%sfp%d:\n"
				"\t.quad %"PRId64
				" /* %f */\n",
				gasloc, i, b->bits.n,
				b->bits.d
			);
	for (b=stash, i=0; b; b=b->link, i++)
		if (!b->wide)
			fprintf(f,
				"%sfp%d:\n"
				"\t.long %"PRId64
				" /* %lf */\n",
				gasloc, i, b->bits.n & 0xffffffff,
				b->bits.f
			);
	while ((b=stash)) {
		stash = b->link;
		free(b);
	}
}
