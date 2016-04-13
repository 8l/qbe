void *malloc();

main()
{
	int n;
	int nv;
	int c;
	int cmax;
	int *mem;

	mem = malloc(sizeof(int) * 4000);

	cmax = 0;
	for (nv = 1; nv < 1000; nv++) {
		n = nv;
		c = 0;
		while (n != 1) {
			if (n < nv) {
				c = c + mem[n];
				break;
			}
			if (n & 1)
				n = 3*n + 1;
			else
				n = n / 2;
			c++;
		}
		mem[nv] = c;
		if (c > cmax)
			cmax = c;
	}
	printf("should print 178: %d\n", cmax);
}
