long f() {
	long n, n0, s;
	
	s = 0;
	n = 1234567;
	for (;;) {
		n0 = n - 1;
		s = s + n;
		if (!n0) break;
		n = n0;
	}
	return s;
}
