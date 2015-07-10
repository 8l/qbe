#include <stdio.h>

int main()
{
	int a = 123456;
	int b = 32223;
	int t;

	do {
		t = a % b;
		a = b;
		b = t;
	} while (b);

	printf("%d\n", a);
	return 0;
}
