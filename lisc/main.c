#include "lisc.h"
#include <ctype.h>

char debug['Z'+1] = {
	['P'] = 0, /* parsing */
	['A'] = 0, /* abi lowering */
	['I'] = 0, /* instruction selection */
	['L'] = 0, /* liveness */
	['M'] = 0, /* memory optimization */
	['N'] = 0, /* ssa construction */
	['C'] = 0, /* copy elimination */
	['S'] = 0, /* spilling */
	['R'] = 0, /* reg. allocation */
};

static int dbg;

void
dumpts(Bits *b, Tmp *tmp, FILE *f)
{
	int t;

	fprintf(f, "[");
	for (t=Tmp0; t<BITS*NBit; t++)
		if (BGET(*b, t))
			fprintf(f, " %s", tmp[t].name);
	fprintf(f, " ]\n");
}

static void
data(Dat *d)
{
#if 0
	if (dbg)
		return;
	if (d->type == DEnd) {
		puts("/* end data */\n");
		freeall();
	}
	emitdat(d, stdout);
#endif
}

static void
func(Fn *fn)
{
	int n;

	if (dbg)
		fprintf(stderr, "**** Function %s ****", fn->name);
	if (debug['P']) {
		fprintf(stderr, "\n> After parsing:\n");
		printfn(fn, stderr);
	}
	fillrpo(fn);
	fillpreds(fn);
	filluse(fn);
#if 0
	memopt(fn);
	ssa(fn);
	filluse(fn);
	copy(fn);
	filluse(fn);
	isel(fn);
	filllive(fn);
	fillcost(fn);
	spill(fn);
	rega(fn);
	fillrpo(fn);
	assert(fn->rpo[0] == fn->start);
	for (n=0;; n++)
		if (n == fn->nblk-1) {
			fn->rpo[n]->link = 0;
			break;
		} else
			fn->rpo[n]->link = fn->rpo[n+1];
	if (!dbg) {
		emitfn(fn, stdout);
		printf("/* end function %s */\n\n", fn->name);
	} else
#endif
		fprintf(stderr, "\n");
	freeall();
}

int
main(int ac, char *av[])
{
	char *o, *f;
	FILE *inf;

	if (ac > 1 && strncmp(av[1], "-d", 2) == 0) {
		if (av[1][2] == 0) {
			if (ac <= 2)
				goto Usage;
			o = av[2];
			f = av[3];
		} else {
			o = &av[1][2];
			f = av[2];
		}
		for (; *o; o++)
			if (isalpha(*o)) {
				debug[toupper(*o)] = 1;
				dbg = 1;
			}
	} else
		f = av[1];

	if (!f || strcmp(f, "-") == 0)
		inf = stdin;
	else {
		inf = fopen(f, "r");
		if (!inf) {
			fprintf(stderr, "cannot open '%s'\n", f);
			goto Usage;
		}
	}

	parse(inf, data, func);
	fclose(inf);
	exit(0);

Usage:
	fprintf(stderr, "usage: %s [-d PCILSR] {file.ssa, -}\n", av[0]);
	exit(1);
}
