#include "all.h"


char *gasloc, *gassym;

void
gasemitdat(Dat *d, FILE *f)
{
	static int align;
	static char *dtoa[] = {
		[DAlign] = ".balign",
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
			fprintf(f, ".balign 8\n");
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
			fprintf(f, "\t.ascii %s\n", d->u.str);
		}
		else if (d->isref) {
			fprintf(f, "%s %s%s%+"PRId64"\n",
				dtoa[d->type], gassym, d->u.ref.nam,
				d->u.ref.off);
		}
		else {
			fprintf(f, "%s %"PRId64"\n",
				dtoa[d->type], d->u.num);
		}
		break;
	}
}

typedef struct Asmbits Asmbits;

struct Asmbits {
	char bits[16];
	int size;
	Asmbits *link;
};

static Asmbits *stash;

int
gasstash(void *bits, int size)
{
	Asmbits **pb, *b;
	int i;

	assert(size == 4 || size == 8 || size == 16);
	for (pb=&stash, i=0; (b=*pb); pb=&b->link, i++)
		if (size <= b->size)
		if (memcmp(bits, b->bits, size) == 0)
			return i;
	b = emalloc(sizeof *b);
	memcpy(b->bits, bits, size);
	b->size = size;
	b->link = 0;
	*pb = b;
	return i;
}

void
gasemitfin(FILE *f)
{
	Asmbits *b;
	char *p;
	int sz, i;
	double d;

	if (!stash)
		return;
	fprintf(f, "/* floating point constants */\n.data\n");
	for (sz=16; sz>=4; sz/=2)
		for (b=stash, i=0; b; b=b->link, i++) {
			if (b->size == sz) {
				fprintf(f,
					".balign %d\n"
					"%sfp%d:",
					sz, gasloc, i
				);
				for (p=b->bits; p<&b->bits[sz]; p+=4)
					fprintf(f, "\n\t.int %"PRId32,
						*(int32_t *)p);
				if (sz <= 8) {
					if (sz == 4)
						d = *(float *)b->bits;
					else
						d = *(double *)b->bits;
					fprintf(f, " /* %f */\n", d);
				} else
					fprintf(f, "\n");
			}
		}
	while ((b=stash)) {
		stash = b->link;
		free(b);
	}
}
