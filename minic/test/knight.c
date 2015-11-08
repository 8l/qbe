#include <stdlib.h>
#include <stdio.h>

void *calloc();

int N;
int **b;

board()
{
	int x;
	int y;

	for (y=0; y<8; y++) {
		for (x=0; x<8; x++)
			printf(" %02d", b[x][y]);
		printf("\n");
	}
	printf("\n");
	return 0;
}

chk(int x, int y)
{
	if (x < 0 || x > 7 || y < 0 || y > 7)
		return 0;
	return b[x][y] == 0;
}

go(int k, int x, int y)
{
	int i;
	int j;

	b[x][y] = k;
	if (k == 64) {
		if (x != 2 && y != 0 && abs(x-2) + abs(y) == 3) {
			board();
			N++;
			if (N == 10)
				exit(0);
		}
	} else
		for (i=-2; i<=2; i++)
			for (j=-2; j<=2; j++) 
				if (abs(i) + abs(j) == 3 && chk(x+i, y+j)) 
					go(k+1, x+i, y+j);
	b[x][y] = 0;
	return 0;
}

main()
{
	int i;

	b = calloc(8, sizeof (int *));
	for (i=0; i<8; i++)
		b[i] = calloc(8, sizeof (int));
	go(1, 2, 0);
}
