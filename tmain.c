#include <stdio.h>
#include <time.h>

extern long f(void);

int main()
{
	clock_t t0;
	long l;

	t0 = clock();
	l = f();
	t0 = clock() - t0;
	printf("f() = %ld\n", l);
	printf("  %.4f secs\n", (double)t0/CLOCKS_PER_SEC);
	return 0;
}
