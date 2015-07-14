#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;

enum {
	R       = 0,  /* invalid reference */
	NReg    = 32,
	Tmp0    = NReg+1,
	NString = 32,
	NPred   = 15,
	NBlk    = 128,
	NIns    = 256,
};

typedef struct Ins Ins;
typedef struct Phi Phi;
typedef struct Blk Blk;
typedef struct Sym Sym;
typedef struct Fn Fn;
typedef ushort Ref;

enum {
	RSym = 0,
	RConst = 1,

	RMask = 1,
	RShift = 1,
	NRefs = ((ushort)-1)>>RShift,
};

#define SYM(x)   (((x)<<RShift) | RSym)
#define CONST(x) (((x)<<RShift) | RConst)

enum {
	OXXX,
	OAdd,
	OSub,
	ODiv,
	OMod,
	OCopy,

	/* reserved instructions */
	OX86Div,
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
void *alloc(size_t);
Fn *parsefn(FILE *);

/* ssa.c */
void fillpreds(Fn *);
void fillrpo(Fn *);
void ssafix(Fn *, int);
