#include <stdio.h>
#include <stdlib.h>

int
main(int ac, char *av[])
{
	double d;
	float f;

	if (ac < 2) {
	usage:
		fputs("usage: fptox NUMBER\n", stderr);
		return 1;
	}
	f = d = strtod(av[1], 0);
	printf("0x%08x 0x%016llx\n", *(unsigned *)&f, *(unsigned long long*)&d);
	return 0;
}
