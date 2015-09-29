#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned int uint;
typedef unsigned long ulong;

typedef struct Bits Bits;
typedef struct Ref Ref;
typedef struct OpDesc OpDesc;
typedef struct Ins Ins;
typedef struct Phi Phi;
typedef struct Blk Blk;
typedef struct Tmp Tmp;
typedef struct Con Con;
typedef struct Fn Fn;
typedef struct Typ Typ;

typedef enum { U, F, T } B3;

enum Reg {
	RXX,

	RAX, /* caller-save */
	RCX,
	RDX,
	RSI,
	RDI,
	R8,
	R9,
	R10,
	R11,

	RBX, /* callee-save */
	R12,
	R13,
	R14,
	R15,

	RBP, /* reserved */
	RSP,

	Tmp0, /* first non-reg temporary */

	NReg = R12 - RAX + 1,
	NRSave = 9,
	NRClob = 5,
};

enum {
	NString = 32,
	NPred   = 15,
	NBlk    = 128,
	NIns    = 256,
	NAlign  = 3,
	NSeg    = 32,
	NTyp    = 128,

	BITS    = 4,
	NBit    = 64,
};

struct Bits {
	ulong t[BITS];
};

#define BIT(n)     (1ul << (n))
#define BGET(b, n) (1&((b).t[n/NBit]>>(n%NBit)))
#define BSET(b, n) ((b).t[n/NBit] |= BIT(n%NBit))
#define BCLR(b, n) ((b).t[n/NBit] &= ~BIT(n%NBit))

struct Ref {
	uint16_t type:2;
	uint16_t val:14;
};

enum {
	RTmp,
	RCon,
	RSlot,
	RAlt,
	RCallm = 0x1000,
	NRef = (1<<14) - 1
};

#define R        (Ref){0, 0}
#define TMP(x)   (Ref){RTmp, x}
#define CON(x)   (Ref){RCon, x}
#define CON_Z    CON(0)          /* reserved zero constant */
#define SLOT(x)  (Ref){RSlot, x}
#define TYP(x)   (Ref){RAlt, x}
#define CALL(x)  (Ref){RAlt, (x)|RCallm}

static inline int req(Ref a, Ref b)
{ return a.type == b.type && a.val == b.val; }
static inline int rtype(Ref r)
{ return req(r, R) ? -1 : r.type; }
static inline int isreg(Ref r)
{ return rtype(r) == RTmp && r.val < Tmp0; }

#define CMPS(X) \
	X(eq) X(sle) X(slt) \
	X(sgt) X(sge) X(ne) /* mirror opposite cmps! */

enum Cmp {
#define C(c) C##c,
	CMPS(C)
#undef C
	NCmp
};

#define COP(c) (c==Ceq||c==Cne ? c : NCmp-1 - c)

enum Op {
	OXXX,

	/* public instructions */
	OAdd,
	OSub,
	ODiv,
	ORem,
	OMul,
	OAnd,
	OSext,
	OZext,
	OCmp,
	OCmp1 = OCmp + NCmp-1,
	OStorel,
	OStorew,
	OStores,
	OStoreb,
	OLoad,
	OLoadsh,
	OLoaduh,
	OLoadsb,
	OLoadub,
	OAlloc,
	OAlloc1 = OAlloc + NAlign-1,
	OCopy,
	NPubOp,

	/* function instructions */
	OPar = NPubOp,
	OParc,
	OArg,
	OArgc,
	OCall,

	/* reserved instructions */
	ONop,
	OAddr,
	OSwap,
	OSign,
	OSAlloc,
	OXPush,
	OXDiv,
	OXCmp,
	OXSet,
	OXSet1 = OXSet + NCmp-1,
	OXTest,
	NOp
};

enum Jmp {
	JXXX,
	JRet0,
	JRetw,
	JRetl,
	JRetc,
	JJmp,
	JJnz,
	JXJc,
	JXJc1 = JXJc + NCmp-1,
	NJmp
};

struct OpDesc {
	char *name;
	int nmem;
};

struct Ins {
	uint16_t op:15;
	uint16_t wide:1;
	Ref to;
	Ref arg[2];
};

struct Phi {
	Ref to;
	Ref arg[NPred];
	Blk *blk[NPred];
	uint narg;
	uint wide;
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

	int id;
	int visit;
	Blk **pred;
	uint npred;
	Bits in, out, gen;
	int nlive;
	int loop;
	char name[NString];
};

struct Tmp {
	char name[NString];
	uint ndef, nuse;
	uint cost;
	short spill;
	short wide;
	int hint;
	int phi;
};

struct Con {
	enum {
		CUndef,
		CNum,
		CAddr,
	} type;
	char label[NString];
	int64_t val;
};

struct Fn {
	Blk *start;
	Tmp *tmp;
	Con *con;
	int ntmp;
	int ncon;
	int nblk;
	int retty;
	Blk **rpo;
	ulong reg;
	int stk0, stk1;
	char name[NString];
};

struct Typ {
	char name[NString];
	int dark;
	uint size;
	int align;

	struct {
		uint flt:1;
		uint len:31;
	} seg[NSeg+1];
};


/* main.c */
extern char debug['Z'+1];
void dumpts(Bits *, Tmp *, FILE *);

/* parse.c */
extern Typ typ[NTyp];
extern OpDesc opdesc[NOp];
void diag(char *);
void *alloc(size_t);
Blk *blocka(void);
Fn *parse(FILE *);
void printfn(Fn *, FILE *);

/* ssa.c */
void fillpreds(Fn *);
void fillrpo(Fn *);
int phirepr(Tmp *, int);
void fillphi(Fn *);
void ssafix(Fn *, int);

/* live.c */
Bits liveon(Blk *, Blk *);
void filllive(Fn *);

/* isel.c */
extern int rsave[NRSave];
extern int rclob[NRClob];
ulong calldef(Ins, int *);
ulong calluse(Ins, int *);
ulong callclb(Ins, int *);
void isel(Fn *);

/* spill.c */
int bcnt(Bits *);
void fillcost(Fn *);
void spill(Fn *);

/* rega.c */
void rega(Fn *);

/* emit.c */
void emitfn(Fn *, FILE *);
