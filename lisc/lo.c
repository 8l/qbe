#include "lisc.h"

static void
rporec(int *rpo, int *cnt, Blk *bs, int b)
{
	if (rpo[b] >= 0)
		return;
	if (bs[b].suc1 >= 0)
		rporec(rpo, cnt, bs, bs[b].suc1);
	if (bs[b].suc0 >= 0)
		rporec(rpo, cnt, bs, bs[b].suc0);
	rpo[b] = --*cnt;
}

int
rposched(Blk *bs, int nb)
{
	static int rpo[MaxBlks];
	Blk t;
	int cnt, i, j;

	for (i=0; i<nb; i++)
		rpo[i] = -1;
	cnt = nb;
	rporec(rpo, &cnt, bs, 0);
	if (cnt) {
		for (i=0; i<nb; i++)
			rpo[i] -= cnt;
	}
	for (i=0; i<nb; i++) {
		if (bs[i].suc0 >= 0)
			bs[i].suc0 = rpo[bs[i].suc0];
		if (bs[i].suc1 >= 0)
			bs[i].suc1 = rpo[bs[i].suc1];
	}
/*
  A little messy, the idea is that we have an
  array permutation inside the rpo array, now we
  apply it to the bs array with a linear algorithm
  using swaps.
*/
	for (i=0; i<nb; i++)
		while (rpo[i] >= 0 && rpo[i] != i) {
			j = rpo[i];
			rpo[i] = rpo[j];
			rpo[j] = j;
			t = bs[i];
			bs[i] = bs[j];
			bs[j] = t;
		}
	return nb - cnt;
}


void
cfdump(FILE *f, char *pname, Blk *bs, int nb)
{
	Blk *b;
	int i;

	fprintf(f, "digraph %s {\n", pname);
	for (b=bs, i=0; i<nb; i++, b++) {
		if (b->suc0 >= 0)
			fprintf(f, "b%d -> b%d;\n", i, b->suc0);
		if (b->suc1 >= 0)
			fprintf(f, "b%d -> b%d;\n", i, b->suc1);
		fprintf(f, "b%d [shape=box]\n", i);
	}
	fprintf(f, "}\n");
}

#define LEN(a) sizeof a / sizeof a[0]

Blk rpocond[] = {
	{ .suc0 =  2, .suc1 =  3 },
	{ .suc0 = -1, .suc1 = -1 },
	{ .suc0 =  1, .suc1 = -1 },
	{ .suc0 = -1, .suc1 =  1 },
	{ .suc0 = 12, .suc1 = -1 }, /* dead */
};

int
main()
{
	Blk *bs;
	int nb;
	FILE *f;

	bs = rpocond;
	nb = LEN(rpocond);

	f = fopen("cf.dot", "w");
	cfdump(f, "bef", bs, nb);
	nb = rposched(bs, nb);
	cfdump(f, "aft", bs, nb);
	fclose(f);

	return 0;
}
