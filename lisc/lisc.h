#include <stdio.h>
#include <stdlib.h>

enum {
	R = -1,        /* Invalid reference. */
	Temp0 = 32,    /* First temporary, below are machine registers. */
	MaxPreds = 16, /* Maximum number of predecessors for a block. */
	MaxBlks = 128,
	MaxInss = 128,
	MaxPhis = 128,
};

typedef int Ref;
typedef struct Ins Ins;
typedef struct Phi Phi;
typedef struct Blk Blk;
typedef enum Op Op;
typedef enum Jmp Jmp;

enum Op {
	ONop,
	OAdd,
	OSub,
	OSDiv,
	OMod,
	OParam,
	OCall,

	/* x86 instructions (reserved) */
	XDiv,
};

enum Jmp {
	JRet,
	JJmp,
	JCnd,
};

struct Ins {
	Op op;
	Ref res;
	Ref arg0, arg1;
};

struct Phi {
	Ref res;
	int na;
	Ref args[MaxPreds];
};

struct Blk {
	int np;
	int ni;
	Phi *ps;
	Ins *is;
	struct {
		Jmp ty;
		Ref arg;
	} jmp;
	int suc0, suc1;
	int dpth;
};
