/*% c99 -O3 -Wall -o # %
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>

typedef unsigned int uint;

char *tok[] = {

	"add", "sub", "div", "rem", "udiv", "urem", "mul",
	"and", "or", "xor", "sar", "shr", "shl", "stored",
	"stores", "storel", "storew", "storeh", "storeb",
	"load", "loadsw", "loaduw", "loadsh", "loaduh",
	"loadsb", "loadub", "extsw", "extuw", "extsh",
	"extuh", "extsb", "extub", "exts", "truncd",
	"stosi", "dtosi", "swtof", "sltof", "cast", "copy",
	"alloc4", "alloc8", "alloc16", "culew", "cultw",
	"cslew", "csltw", "csgtw", "csgew", "cugtw",
	"cugew", "ceqw", "cnew", "culel", "cultl", "cslel",
	"csltl", "csgtl", "csgel", "cugtl", "cugel",
	"ceql", "cnel", "cles", "clts", "cgts", "cges",
	"cnes", "ceqs", "cos", "cuos", "cled", "cltd",
	"cgtd", "cged", "cned", "ceqd", "cod", "cuod",

	"call", "phi", "jmp", "jnz", "ret", "export",
	"function", "type", "data", "align", "l", "w",
	"h", "b", "d", "s", "z", "loadw", "loadl", "loads",
	"loadd", "alloc1", "alloc2",

};
enum {
	Ntok = sizeof tok / sizeof tok[0]
};

uint th[Ntok];

uint
hash(char *s)
{
	uint h;

	h = 0;
	for (; *s; ++s)
		h = *s + 5*h;
	return h;
}

int
main()
{
	char *bmap;
	uint h;
	int i, j;
	int M, K;

	bmap = malloc(1u << 31);

	for (i=0; i<Ntok; ++i) {
		h = hash(tok[i]);
		for (j=0; j<i; ++j)
			if (th[j] == h) {
				printf("error: hash()\n");
				printf("\t%s\n", tok[i]);
				printf("\t%s\n", tok[j]);
				exit(1);
			}
		th[i] = h;
	}

	for (i=0; 1<<i < Ntok; ++i);
	M = 32 - i;

	for (;; --M) {
		printf("trying M=%d...\n", M);
		for (K = 1; K<UINT_MAX-2; K+=2) {
			memset(bmap, 0, 1 << (32 - M));
			for (i=0; i<Ntok; ++i) {
				h = (th[i]*K) >> M;
				if (bmap[h])
					break;
				bmap[h] = 1;
			}
			if (i==Ntok) {
				printf("found K=%d for M=%d\n", K, M);
				exit(0);
			}
		}
	}
}
