#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;

enum {
	NReg    = 32,
	Tmp0    = NReg+1,
	NString = 32,
	NPred   = 15,
	NBlk    = 128,
	NIns    = 256,
};

typedef struct OpDesc OpDesc;
typedef struct Ins Ins;
typedef struct Phi Phi;
typedef struct Blk Blk;
typedef struct Sym Sym;
typedef struct Fn Fn;
typedef struct Ref Ref;

struct Ref {
	ushort type:1;
	ushort val:15;
};

static inline int
req(Ref a, Ref b)
{
	return a.type == b.type && a.val == b.val;
}

#define R (Ref){0, 0} // Invalid reference

enum {
	RSym = 0,
	RConst = 1,
	NRef = ((ushort)-1)>>1,
};

#define SYM(x)   (Ref){ RSym, x }
#define CONST(x) (Ref){ RConst, x }

enum {
	OXXX,
	OAdd,
	OSub,
	ODiv,
	OMod,
	OCopy,

	/* reserved instructions */
	OX86Div,
	OLast
};

struct OpDesc {
	int arity;
	int commut:1;
	char *name;
};

enum {
	JXXX,
	JRet,
	JJmp,
	JJez,
};

struct Ins {
	short op;
	Ref to;
	Ref l;
	Ref r;
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
	Blk *blk;
	int pos;
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
