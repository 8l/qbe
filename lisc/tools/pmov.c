/*% cc -std=c99 -Wall -DTEST_PMOV -g -o # %
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void assert_test(char *, int), fail(void);

#include "../rega.c"

static RMap mbeg;
static Ins ins[NReg], *ip;

int
main()
{
	Blk dummyb;
	Ins *i1;
	unsigned long long tm, rm;
	RMap mend;
	int reg[NReg];
	int t, i, r, nr;

	tmp = (Tmp[Tmp0+NReg]){{0}};
	for (t=0; t<Tmp0+NReg; t++)
		if (t < Tmp0)
			tmp[t] = (Tmp){.type = TReg};
		else {
			tmp[t].type = TLong;
			tmp[t].hint = -1;
			sprintf(tmp[t].name, "tmp%d", t-Tmp0+1);
		}

	dummyb.ins = ins;
	strcpy(dummyb.name, "dummy");

	for (tm = 0; tm < 1ull << (2*NReg); tm++) {
		mbeg.n = 0;
		mbeg.b = (Bits){{0}};
		ip = ins;

		/* find what temporaries are in copy and
		 * wether or not they are in register
		 */
		for (t=0; t<NReg; t++)
			switch ((tm >> (2*t)) & 3) {
			case 0:
				/* not in copy, not in use */
				break;
			case 1:
				/* not in copy, in use */
				radd(&mbeg, Tmp0+t, t+1);
				break;
			case 2:
				/* in copy, not in reg */
				*ip++ = (Ins){OCopy, TMP(Tmp0+t), {R, R}};
				break;
			case 3:
				/* in copy, in reg */
				*ip++ = (Ins){OCopy, TMP(Tmp0+t), {R, R}};
				radd(&mbeg, Tmp0+t, t+1);
				break;
			}

		if (ip == ins)
			/* cancel is the parallel move
			 * is empty
			 */
			goto Nxt;

		/* find registers for temporaries
		 * in mbeg
		 */
		nr = ip - ins;
		dummyb.nins = nr;
		rm = (1ull << (nr+1)) - 1;
		for (i=0; i<nr; i++)
			reg[i] = i+1;

		for (;;) {
			/* set registers on copies
			 */
			for (i=0, i1=ins; i1<ip; i1++, i++)
				i1->arg[0] = TMP(reg[i]);
#if 0
			for (i=0; i<nr; i++)
				printf("%d ", reg[i]);
			printf("\n");
#endif

			/* compile the parallel move
			 */
			mend = mbeg;
			dopm(&dummyb, ip-1, &mend);

			// TODO
			/* check that mend contain mappings for
			 * source registers and does not map any
			 * assigned temporary
			 */

			// TODO
			/* execute the code generated and check
			 * that all assigned temporaries got their
			 * value
			 */

			/* find the next register assignment */
			i = nr - 1;
			for (;;) {
				r = reg[i];
				rm &= ~(1ull<<r);
				do
					r++;
				while (r <= NReg && (rm & (1ull<<r)));
				if (r == NReg+1) {
					if (i == 0)
						goto Nxt;
					i--;
				} else {
					rm |= (1ull<<r);
					reg[i++] = r;
					break;
				}
			}
			for (; i<nr; i++)
				for (r=1; r<=NReg; r++)
					if (!(rm & (1ull<<r))) {
						rm |= (1ull<<r);
						reg[i] = r;
						break;
					}
		}
	Nxt:	;
	}
	exit(0);
}


/* failure diagnostics */
static void
fail()
{
	Ins *i1;
	int i;

	printf("\nIn registers: ");
	for (i=0; i<mbeg.n; i++)
		printf("%s(r%d) ",
			tmp[mbeg.t[i]].name,
			mbeg.r[i]);
	printf("\n");
	printf("Parallel move:\n");
	for (i1=ins; i1<ip; i1++)
		printf("\t %s <- r%d\n",
			tmp[i1->to.val].name,
			i1->arg[0].val);
	exit(1);
}

static void
assert_test(char *s, int x)
{
	if (x)
		return;
	printf("!assertion failure: %s\n", s);
	fail();
}


/* symbols required by the linker */
char debug['Z'+1];
Ins insb[NIns], *curi;

void diag(char *s)
{ printf("!diag failure: %s\n", s); fail(); }

void *alloc(size_t n)
{ return malloc(n); }

Blk *blocka()
{ printf("!blocka called\n"); exit(1); }
