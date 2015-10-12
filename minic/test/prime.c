main() {
	int n;
	int t;
	int c;
	int p;

	c = 0;
	n = 2;
	while (n < 1000) {
		if (c % 10 == 0)
		if (c != 0)
			printf("\n");
		t = 2;
		p = 1;
		while (t*t <= n) {
			if (n % t == 0)
				p = 0;
			t = t + 2;
		}
		if (p) {
			printf("%4d ", n);
			c++;
		}
		n = n + 2;
	}
	printf("\n");
}
