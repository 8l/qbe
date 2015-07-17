#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned int uint;
typedef unsigned char uchar;
typedef unsigned long long ullong;

enum {
	NReg    = 32,
	Tmp0    = NReg+1,

	NString = 32,
	NPred   = 15,
	NBlk    = 128,
	NIns    = 256,

	BITS    = 4,
	NBit    = 8 * sizeof(ullong),
};

typedef struct Bits Bits;
typedef struct Ref Ref;
typedef struct OpDesc OpDesc;
typedef struct Ins Ins;
typedef struct Phi Phi;
typedef struct Blk Blk;
typedef struct Sym Sym;
typedef struct Fn Fn;

struct Bits {
	ullong t[BITS];
};

#define BGET(b, n) (1&((b).t[n/NBit]>>(n%NBit)))
#define BSET(b, n) ((b).t[n/NBit] |= (ullong)1<<(n%NBit))
#define BCLR(b, n) ((b).t[n/NBit] &= ~((ullong)1<<(n%NBit)))

struct Ref {
	uint16_t type:1;
	uint16_t val:15;
};

enum {
	RSym = 0,
	RConst = 1,
	NRef = (1<<15) - 1
};

#define R        (Ref){0, 0}
#define SYM(x)   (Ref){RSym, x}
#define CONST(x) (Ref){RConst, x}

static inline int req(Ref a, Ref b)
{
	return a.type == b.type && a.val == b.val;
}
static inline int rtype(Ref r)
{
	return req(r, R) ? -1 : r.type;
}

enum {
	OXXX = 0,
	OAdd,
	OSub,
	ODiv,
	OMod,
	OCopy,

	/* reserved instructions */
	OX86Div,
	OLast
};

enum {
	JXXX,
	JRet,
	JJmp,
	JJez,
};

struct OpDesc {
	int arity;
	int commut:1;
	char *name;
};

struct Ins {
	short op;
	Ref to;
	Ref arg[2];
};

struct Phi {
	Ref to;
	Ref arg[NPred];
	Blk *blk[NPred];
	uint narg;
	Phi *link;
};

struct Blk {
	Phi *phi;
	Ins *ins;
	uint nins;
	struct {
		short type;
		Ref arg;
	} jmp;
	Blk *s1;
	Blk *s2;
	Blk *link;

	Blk **pred;
	uint npred;
	Bits in, out;
	char name[NString];
	int id;
};

struct Sym {
	enum {
		SUndef,
		SReg,
		STmp,
	} type;
	char name[NString];
	int ndef, nuse;
};

struct Fn {
	Blk *start;
	Sym *sym;
	int ntmp;
	int nblk;
	Blk **rpo;
};


/* parse.c */
extern OpDesc opdesc[];
void *alloc(size_t);
Fn *parsefn(FILE *);
void printfn(Fn *, FILE *);

/* ssa.c */
void fillpreds(Fn *);
void fillrpo(Fn *);
void ssafix(Fn *, int);

/* live.c */
void filllive(Fn *);
