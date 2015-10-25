int printf();
void *calloc();
int atoi();

int Q;
int N;
int **t;

print() {
	int x;
	int y;

	for (y=0; y<Q; y++) {
		for (x=0; x<Q; x++)
			if (t[x][y])
				printf(" Q");
			else
				printf(" .");
		printf("\n");
	}
	printf("\n");
}

chk(int x, int y) {
	int i;
	int r;

	for (r=i=0; i<Q; i++) {
		r = r + t[x][i];
		r = r + t[i][y];
		if (x+i < Q & y+i < Q)
			r = r + t[x+i][y+i];
		if (x+i < Q & y-i >= 0)
			r = r + t[x+i][y-i];
		if (x-i >= 0 & y+i < Q)
			r = r + t[x-i][y+i];
		if (x-i >= 0 & y-i >= 0)
			r = r + t[x-i][y-i];
	}
	return r;
}

go(int y) {
	int x;

	if (y == Q) {
		print();
		N++;
		return 0;
	}
	for (x=0; x<Q; x++)
		if (chk(x, y) == 0) {
			t[x][y]++;
			go(y+1);
			t[x][y]--;
		}
}

main(int ac, void **av) {
	int i;

	Q = 8;
	if (ac >= 2)
		Q = atoi(av[1]);
	t = calloc(Q, sizeof(int *));
	for (i=0; i<Q; i++)
		t[i] = calloc(Q, sizeof(int));
	go(0);
	printf("found %d solutions\n", N);
}
