#include "lisc.h"


char debug['Z'+1] = {
	['S'] = 0, /* spiller */
};

void
dumpss(Bits *b, Sym *s, FILE *f)
{
	int t;

	fprintf(f, "[");
	for (t=0; t<BITS*NBit; t++)
		if (BGET(*b, t))
			fprintf(f, " %s", s[t].name);
	fprintf(f, " ]\n");
}

int
main(int ac, char *av[])
{
	int opt, pr;
	Fn *fn;

	fn = parsefn(stdin);

	pr = 1;
	opt = 0;
	if (ac > 1 && av[1][0] == '-')
		opt = av[1][1];

	switch (opt) {
	case 'f': {
		int tx, ntmp;

		fprintf(stderr, "[Testing SSA Reconstruction:");
		fillpreds(fn);
		for (ntmp=fn->ntmp, tx=Tmp0; tx<ntmp; tx++) {
			fprintf(stderr, " %s", fn->sym[tx].name);
			ssafix(fn, tx);
		}
		fprintf(stderr, "]\n");
		break;
	}
	case 'r': {
		int n;

		fprintf(stderr, "[Testing RPO]\n");
	RPODump:
		fillrpo(fn);
		assert(fn->rpo[0] == fn->start);
		for (n=0;; n++)
			if (n == fn->nblk-1) {
				fn->rpo[n]->link = 0;
				break;
			} else
				fn->rpo[n]->link = fn->rpo[n+1];
		break;
	}
	case 'l': {
		Blk *b;

		fprintf(stderr, "[Testing Liveness]\n");
		fillrpo(fn);
		filllive(fn);
		for (b=fn->start; b; b=b->link) {
			printf("> Block %s\n", b->name);
			printf("\t in:   ");
			dumpss(&b->in, fn->sym, stdout);
			printf("\tout:   ");
			dumpss(&b->out, fn->sym, stdout);
			printf("\tnlive: %d\n", b->nlive);
		}
		pr = 0;
		break;
	}
	case 'i': {
		fprintf(stderr, "[Testing Instruction Selection]\n");
		isel(fn);
		break;
	}
	case 's': {
		Blk *b;

		fprintf(stderr, "[Testing Spilling]\n");
		debug['S'] = 1;
		isel(fn);
		fillrpo(fn);
		fillpreds(fn);
		filllive(fn);
		fillcost(fn);
		spill(fn);
		printf("> Block information:\n");
		for (b=fn->start; b; b=b->link) {
			printf("\t%-10s (% 5d) ",
				b->name, b->loop);
			dumpss(&b->out, fn->sym, stdout);
		}
		printf("\n");
		break;
	}
	case 'a': {
		fprintf(stderr, "[Testing Register Allocation]\n");
		debug['R'] = 1;
		isel(fn);
		fillrpo(fn);
		fillpreds(fn);
		filllive(fn);
		fillcost(fn);
		spill(fn);
		rega(fn);
		goto RPODump;
		break;
	}
	case 'e': {
		int n;

		fprintf(stderr, "[Testing Code Emission]\n");
		fillrpo(fn);
		fillpreds(fn);
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
		emitfn(fn, stdout);
		pr = 0;
		break;
	}
	default:
		break;
	}

	if (pr)
		printfn(fn, stdout);
	return 0;
}
