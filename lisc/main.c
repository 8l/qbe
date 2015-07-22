#include "lisc.h"


char debug['Z'+1] = {
	['S'] = 1, /* spiller */
};

void
dumpss(Bits *b, Sym *s, FILE *f)
{
	int t;

	fprintf(f, "[");
	for (t=Tmp0; t<BITS*NBit; t++)
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
	case 's': {
		int t;
		Blk *b;

		fprintf(stderr, "[Testing Spilling]\n");
		fillrpo(fn);
		fillpreds(fn);
		filllive(fn);
		fillcost(fn);
		printf("> Spill costs:\n");
		for (t=Tmp0; t<fn->ntmp; t++)
			printf("\t%-10s %d\n",
				fn->sym[t].name,
				fn->sym[t].cost);
		spill(fn);
		printf("\n> Block information:\n");
		for (b=fn->start; b; b=b->link) {
			printf("\t%-10s (% 5d) ",
				b->name, b->loop);
			dumpss(&b->out, fn->sym, stdout);
		}
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
