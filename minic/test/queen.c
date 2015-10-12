#include <stdio.h>
#include <stdlib.h>

int N;
int *t;

print() {
	int x;
	int y;

	y = 0;
	while (y < 8) {
		x = 0;
		while (x < 8) {
			if (t[x + 8*y])
				printf(" Q");
			else
				printf(" .");
			x++;
		}
		printf("\n");
		y++;
	}
	printf("\n");
}

chk(int x, int y) {
	int i;
	int r;

	r = 0;
	i = 0;
	while (i < 8) {
		r = r + t[x + 8*i];
		r = r + t[i + 8*y];
		if (x+i < 8 & y+i < 8)
			r = r + t[x+i + 8*(y+i)];
		if (x+i < 8 & y-i >= 0)
			r = r + t[x+i + 8*(y-i)];
		if (x-i >= 0 & y+i < 8)
			r = r + t[x-i + 8*(y+i)];
		if (x-i >= 0 & y-i >= 0)
			r = r + t[x-i + 8*(y-i)];
		if (r)
			return 1;
		i++;
	}
	return 0;
}

go(int n, int x, int y) {
	if (n == 8) {
		print();
		N++;
		return 0;
	}
	while (y < 8) {
		while (x < 8) {
			if (chk(x, y) == 0) {
				t[x + 8*y]++;
				go(n+1, x, y);
				t[x + 8*y]--;
			}
			x++;
		}
		x = 0;
		y++;
	}
}

main() {
	t = calloc(64, sizeof(int));
	go(0, 0, 0);
	printf("found %d solutions\n", N);
}
