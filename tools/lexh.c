/*% c99 -O3 -Wall -o # %
 */
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <stdint.h>

char *tok[] = {

	"add", "sub", "neg", "div", "rem", "udiv", "urem", "mul",
	"and", "or", "xor", "sar", "shr", "shl", "stored",
	"stores", "storel", "storew", "storeh", "storeb",
	"load", "loadsw", "loaduw", "loadsh", "loaduh",
	"loadsb", "loadub", "extsw", "extuw", "extsh",
	"extuh", "extsb", "extub", "exts", "truncd",
	"stosi", "dtosi", "stoui", "dtoui", "uwtof",
	"ultof", "swtof", "sltof", "cast", "copy",
	"alloc4", "alloc8", "alloc16", "culew", "cultw",
	"cslew", "csltw", "csgtw", "csgew", "cugtw",
	"cugew", "ceqw", "cnew", "culel", "cultl", "cslel",
	"csltl", "csgtl", "csgel", "cugtl", "cugel",
	"ceql", "cnel", "cles", "clts", "cgts", "cges",
	"cnes", "ceqs", "cos", "cuos", "cled", "cltd",
	"cgtd", "cged", "cned", "ceqd", "cod", "cuod",
	"vaarg", "vastart", "...", "env",

	"call", "phi", "jmp", "jnz", "ret", "export",
	"function", "type", "data", "section", "align",
	"l", "w", "h", "b", "d", "s", "z", "loadw", "loadl",
	"loads", "loadd", "alloc1", "alloc2",

};
enum {
	Ntok = sizeof tok / sizeof tok[0]
};

uint32_t th[Ntok];

uint32_t
hash(char *s)
{
	uint32_t h;

	h = 0;
	for (; *s; ++s)
		h = *s + 17*h;
	return h;
}

int
main()
{
	char *bmap;
	uint32_t h, M, K;
	int i, j;

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
		K = 1;
		do {
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
			K += 2;
		} while (K != 1);
	}
}
