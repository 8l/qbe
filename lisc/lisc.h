#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

/*
  References have to be able to encode:
    - Results of other operations (temporaries).
    - Machine registers (for lowering).
    - Spill locations.
    - Constants/pointers to program data.
*/

enum {
	R = 0,          /* Invalid reference. */
	Temp0 = 33,     /* First temporary ref. */
	Const0 = 20000, /* First constant ref. */
	MaxIdnt = 32,
	MaxPreds = 16,
	MaxBlks = 128,
	MaxInss = 128,
	MaxPhis = 128,
};

typedef unsigned Ref;
typedef struct Ins Ins;
typedef struct Phi Phi;
typedef struct Blk Blk;
typedef struct Fn Fn;
typedef enum Op Op;
typedef enum Jmp Jmp;

enum Op {
	OAdd = 1,
	OSub,
	ODiv,
	OMod,

	/* Reserved instructions. */
	X86Div,
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
	Phi *ps;
	Ins *is;
	int np;
	int ni;
	struct {
		Jmp ty;
		Ref arg;
	} jmp;
	int suc0, suc1;
	int lvl;
};

struct Sym {
	enum {
		SUndef,
		SReg,
		SNum,
		STemp,
	} ty;
	union {
		char sreg[MaxIdnt];
		long long snum;
		struct {
			char id[MaxIdnt];
			int blk;
			enum {
				TPhi,
				TIns,
			} ty;
			int loc;
		} stemp;
	} u;
};

#define sreg u.sreg
#define snum u.snum
#define stemp u.stemp

struct Fn {
	Sym *sym;
	Blk *blk;
	int nblk;
	Ref nref;
};


/* parse.c */
Fn *parsefn(FILE *);
