/*% clang -g -Wall -o # %
 *
 * This is a test program for the slota
 * routine in isel.c, it's a tricky beast
 * so when you modify it you can use this
 * test program to debug your changes.
 *
 * Please make sure it stays in sync.
 */
#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

#define VARL 1

enum { N = 3 };

static int
slota(int sz, int al, int *sa)
{
	int j, k, s, l, a, ret;

	a = 1 << al;
	l = sz;

	if (l > a) {
		/* for large slots, we just
		 * tack them on the next max
		 * alignment slot available
		 * todo, could sophisticate
		 */
		l = (l + a-1) & ~(a-1);
		s = sa[N-1] + l;
		ret = s;
		for (j=0, k=1; j<N; j++, k*=2) {
			l = (l + k-1) & ~(k-1);
			sa[j] = sa[N-1] + l;
		}
	} else {
		j = al;
		s = sa[j] + a;
		ret = s;
	Shift:
		if (j < N-1 && s < sa[j+1])
			/* ........-----------...
			 * ^       ^          ^
			 * sa[j]  sa[j]+a    sa[j+1]
			 *
			 * we have to skip to the
			 * next large whole
			 */
			s = sa[j+1];

		for (k=0; k<=j; k++)
			/* move all smaller holes
			 * that we contain with us
			 */
			if (sa[k] == sa[j])
				sa[k] = s;

		if (j < N-1 && s > sa[j+1]) {
			/* we were in a bigger hole,
			 * it needs to shift further
			 */
			s = sa[++j] + (a *= 2);
			goto Shift;
		}
	}
	return ret;
}

enum { S = 300 };

int
main(int ac, char *av[])
{
	int sa[N] = {0, 0, 2};
	char stk[S] = {0}, buf[4] = {0};
	unsigned seed;
	int i, a, l, s, itr;
	int ret;
	FILE *rnd;

	if (ac < 2) {
		rnd = fopen("/dev/urandom", "r");
		fread(buf, 4, 1, rnd);
		seed = *(unsigned *)buf;
		printf("seed: %u", seed);
		fclose(rnd);
	} else
		seed = atol(av[1]);
	srand(seed);

	for (itr=1;;itr++) {
		if ((itr-1) % 4 == 0)
			printf("\n");
		do
			a = rand() % 4;
		while (a >= N);
		if ((float)rand()/RAND_MAX < 0.1 && VARL) {
			l = rand() % (S/20);
			printf("[(%02d) %02d %d] ", itr, l, a);
		} else {
			l = 1 << a;
			printf("[(%02d) xx %d] ", itr, a);
		}
		s = slota(l, a, sa);
		if (s > S)
			break;
		if ((s+2) % (1 << a) != 0) {
			printf("... FAIL (%d align)\n", s);
			ret = 1;
			goto end;
		}
		for (i=0; i<l; i++) {
			s--;
			assert(s >= 0);
			if (stk[s]) {
				printf("... FAIL (%d)\n", s);
				ret = 1;
				goto end;
			}
			stk[s] = itr;
		}
	}

	for (s=0, i=0; i<S; i++)
		if (!stk[i])
			s++;
	printf("... OK (%d)\n", s);
	ret = 0;
end:
	printf("\n");
	for (i=0; i<S; i++)
		printf("%02d ", stk[i]);
	printf("\n\n");
	for (i=0; i<N; i++)
		printf("sa[%d] = %d\n", i, sa[i]);
	exit(ret);
}
