#include "lisc.h"


static void
dumprset(Bits *b, Fn *fn)
{
	int t;

	for (t=Tmp0; t<fn->ntmp; t++)
		if (BGET(*b, t))
			printf(" %s", fn->sym[t].name);
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
			printf("\t in:   [");
			dumprset(&b->in, fn);
			printf(" ]\n");
			printf("\tout:   [");
			dumprset(&b->out, fn);
			printf(" ]\n");
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
		filllive(fn);
		fillcost(fn);
		fprintf(stderr, "> Spill costs:\n");
		for (t=Tmp0; t<fn->ntmp; t++)
			fprintf(stderr, "\t%s: %d\n",
				fn->sym[t].name,
				fn->sym[t].cost);
		spill(fn);
		fprintf(stderr, "\n> In registers at exits:\n");
		for (b=fn->start; b; b=b->link) {
			printf("\t%s: [", b->name);
			dumprset(&b->out, fn);
			printf(" ]\n");
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
