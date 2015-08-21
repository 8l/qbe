/*% cc -O3 -std=c99 -Wall -DTEST_PMOV -o # %
 *
 * This is a test framwork for the dopm() function
 * in rega.c, use it when you want to modify it or
 * all the parallel move functions.
 *
 * You might need to decrease NReg to see it
 * terminate, I used NReg == 7 at most.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void assert_test(char *, int), fail(void), iexec(int *);

#include "../rega.c"

static RMap mbeg;
static Ins ins[NReg], *ip;
static Blk dummyb = { .ins = ins };

int
main()
{
	Ins *i1;
	unsigned long long tm, rm, cnt;
	RMap mend;
	int reg[NReg], val[NReg+1];
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

	cnt = 0;
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
			/* cancel if the parallel move
			 * is empty
			 */
			goto Nxt;

		/* find registers for temporaries
		 * in mbeg
		 */
		nr = ip - ins;
		rm = (1ull << (nr+1)) - 1;
		for (i=0; i<nr; i++)
			reg[i] = i+1;

		for (;;) {
			/* set registers on copies
			 */
			for (i=0, i1=ins; i1<ip; i1++, i++)
				i1->arg[0] = TMP(reg[i]);

			/* compile the parallel move
			 */
			mend = mbeg;
			dopm(&dummyb, ip-1, &mend);
			cnt++;

			/* check that mend contain mappings for
			 * source registers and does not map any
			 * assigned temporary, then check that
			 * all temporaries in mend are mapped in
			 * mbeg and not used in the copy
			 */
			for (i1=ins; i1<ip; i1++) {
				r = i1->arg[0].val;
				assert(rfree(&mend, r) == r);
				t = i1->to.val;
				assert(!BGET(mend.b, t));
			}
			for (i=0; i<mend.n; i++) {
				t = mend.t[i];
				assert(BGET(mbeg.b, t));
				t -= Tmp0;
				assert(((tm >> (2*t)) & 3) == 1);
			}

			/* execute the code generated and check
			 * that all assigned temporaries got their
			 * value, and that all live variables's
			 * content got preserved
			 */
			 for (i=1; i<=NReg; i++)
			 	val[i] = i;
			 iexec(val);
			 for (i1=ins; i1<ip; i1++) {
			 	t = i1->to.val;
			 	r = rfind(&mbeg, t);
			 	if (r != -1)
			 		assert(val[r] == i1->arg[0].val);
			 }
			 for (i=0; i<mend.n; i++) {
			 	t = mend.t[i];
			 	r = mend.r[i];
			 	assert(val[t-Tmp0+1] == r);
			 }

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
	printf("%llu tests successful!\n", cnt);
	exit(0);
}


/* execute what pmgen() wrote (swap, copy) */

#define validr(r)           \
	rtype(r) == RTmp && \
	r.val > 0 &&        \
	r.val <= NReg

static void
iexec(int val[])
{
	Ins *i;
	int t;

	for (i=insb; i<curi; i++)
		switch (i->op) {
		default:
			assert(!"iexec: missing case\n");
			exit(1);
		case OSwap:
			assert(validr(i->arg[0]));
			assert(validr(i->arg[1]));
			t = val[i->arg[0].val];
			val[i->arg[0].val] = val[i->arg[1].val];
			val[i->arg[1].val] = t;
			break;
		case OCopy:
			assert(validr(i->to));
			assert(validr(i->arg[0]));
			val[i->to.val] = val[i->arg[0].val];
			break;
		}
}


/* failure diagnostics */

static int re;

static void
replay()
{
	RMap mend;

	re = 1;
	mend = mbeg;
	dopm(&dummyb, ip-1, &mend);
}

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
	replay();
	exit(1);
}

static void
assert_test(char *s, int x)
{
	if (x)
		return;
	if (re)
		exit(1);
	printf("!assertion failure: %s\n", s);
	fail();
}

void diag(char *s)
{
	if (re)
		exit(1);
	printf("!diag failure: %s\n", s);
	fail();
}


/* symbols required by the linker */
char debug['Z'+1];
Ins insb[NIns], *curi;

void *alloc(size_t n)
{ return calloc(n, 1); }
Blk *blocka()
{ printf("!blocka\n"); exit(1); }
