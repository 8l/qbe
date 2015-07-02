#include <assert.h>
#include <stdio.h>

typedef unsgined int uint;
typedef unsigned short ushort;
typedef unsigned char uchar;

/* How do I deal with stack slots (alloc, set, get) ?
 *   It seems that computing the address of the slot
 *   and then dereferencing is a bad idea, it uses
 *   one register while I could use the machine
 *   addressing capabilities.
 */

enum {
	R = 0,           /* invalid reference */
	NRegs = 32,
	Temp0 = NRegs+1, /* first temporary */
	NString = 32,
	NPreds = 15,
	NBlks = 128,
	NInss = 256,
	NPhis = 32,
};

typedef struct Ins Ins;
typedef struct Phi Phi;
typedef struct Blk Blk;
typedef struct Fn Fn;
typedef ushort Ref;

enum {
	RTemp = 0,
	RData = 1,

	RMask = 1,
	RShift = 1,
	NRefs = USHRT_MAX>>RShift,
};

#define TEMP(x) (((x)<<RShift) | RTemp)
#define DATA(x) (((x)<<RShift) | RData)

enum {
	OXXX,
	OAdd,
	OSub,
	ODiv,
	OMod,
	OLoad,

	/* reserved instructions */
	OX86Div,
};

enum {
	JXXX,
	JRet,
	JJmp,
	JCnd,
};

struct Ins {
	short op;
	Ref to;
	Ref l;
	Ref r;
};

struct Phi {
	Ref to;
	Ref args[NPreds];
	int na;
};

struct Blk {
	Phi *ps;
	Ins *is;
	uint np;
	uint ni;
	struct {
		short type;
		Ref arg;
	} jmp;
	Blk *s1;
	Blk *s2;

	int rpo;
};

struct Sym {
	enum {
		SUndef,
		SReg,
		STemp,
	} type;
	char name[NString];
	Blk *blk;
	int pos; /* negative for phis */
};

struct Fn {
	Blk *start;
	Sym *sym;
	int ntemp;
};


/* parse.c */
Fn *parsefn(FILE *);
