#include <stdio.h>
extern long f(void);

int main()
{
	printf("f() = %ld\n", f());
	return 0;
}
