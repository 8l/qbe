#include "all.h"
#include "config.h"
#include <ctype.h>
#include <getopt.h>

char debug['Z'+1] = {
	['P'] = 0, /* parsing */
	['A'] = 0, /* abi lowering */
	['I'] = 0, /* instruction selection */
	['L'] = 0, /* liveness */
	['M'] = 0, /* memory optimization */
	['N'] = 0, /* ssa construction */
	['C'] = 0, /* copy elimination */
	['F'] = 0, /* constant folding */
	['S'] = 0, /* spilling */
	['R'] = 0, /* reg. allocation */
};

static FILE *outf;
static int dbg;

static void
data(Dat *d)
{
	if (dbg)
		return;
	if (d->type == DEnd) {
		fputs("/* end data */\n\n", outf);
		freeall();
	}
	emitdat(d, outf);
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
	/* memopt(fn); */
	ssa(fn);
	filluse(fn);
	ssacheck(fn);
	fillalias(fn);
	loadopt(fn);
	filluse(fn);
	ssacheck(fn);
	copy(fn);
	filluse(fn);
	fold(fn);
	abi(fn);
	filluse(fn);
	isel(fn);
	fillrpo(fn);
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
		emitfn(fn, outf);
		fprintf(outf, "/* end function %s */\n\n", fn->name);
	} else
		fprintf(stderr, "\n");
	freeall();
}

int
main(int ac, char *av[])
{
	FILE *inf;
	char *f;
	int c, asm;

	asm = Defaultasm;
	outf = stdout;
	while ((c = getopt(ac, av, "hd:o:G:")) != -1)
		switch (c) {
		case 'd':
			for (; *optarg; optarg++)
				if (isalpha(*optarg)) {
					debug[toupper(*optarg)] = 1;
					dbg = 1;
				}
			break;
		case 'o':
			if (strcmp(optarg, "-") != 0)
				outf = fopen(optarg, "w");
			break;
		case 'G':
			if (strcmp(optarg, "e") == 0)
				asm = Gaself;
			else if (strcmp(optarg, "m") == 0)
				asm = Gasmacho;
			else {
				fprintf(stderr, "unknown gas flavor '%s'\n", optarg);
				exit(1);
			}
			break;
		case 'h':
		default:
			fprintf(stderr, "%s [OPTIONS] {file.ssa, -}\n", av[0]);
			fprintf(stderr, "\t%-10s prints this help\n", "-h");
			fprintf(stderr, "\t%-10s output to file\n", "-o file");
			fprintf(stderr, "\t%-10s generate gas (e) or osx (m) asm\n", "-G {e,m}");
			fprintf(stderr, "\t%-10s dump debug information\n", "-d <flags>");
			exit(c != 'h');
		}

	switch (asm) {
	case Gaself:
		locprefix = ".L";
		symprefix = "";
		break;
	case Gasmacho:
		locprefix = "L";
		symprefix = "_";
		break;
	}

	do {
		f = av[optind];
		if (!f || strcmp(f, "-") == 0) {
			inf = stdin;
			f = "-";
		} else {
			inf = fopen(f, "r");
			if (!inf) {
				fprintf(stderr, "cannot open '%s'\n", f);
				exit(1);
			}
		}
		parse(inf, f, data, func);
	} while (++optind < ac);

	if (!dbg)
		emitfin(outf);

	exit(0);
}
