#include <stdio.h>
#include <time.h>

enum { NRounds = 150 };

extern long f(void);

int main()
{
	clock_t t0, tmin;
	long i, l;

	tmin = 10 * CLOCKS_PER_SEC;
	for (i=0; i<NRounds; i++) {
		t0 = clock();
		l = f();
		t0 = clock() - t0;
		if (t0 < tmin)
			tmin = t0;
	}
	printf("f() = %ld\n", l);
	printf("  %.4f secs\n", (double)t0/CLOCKS_PER_SEC);
	return 0;
}
