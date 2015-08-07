#include <assert.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned int uint;

typedef struct Bits Bits;
typedef struct Ref Ref;
typedef struct OpDesc OpDesc;
typedef struct Ins Ins;
typedef struct Phi Phi;
typedef struct Blk Blk;
typedef struct Tmp Tmp;
typedef struct Con Con;
typedef struct Fn Fn;

typedef enum { U, F, T } B3;

enum {
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

	EAX, /* 32bits */
	ECX,
	EDX,
	ESI,
	EDI,
	R8D,
	R9D,
	R10D,
	R11D,

	EBX,
	R12D,
	R13D,
	R14D,
	R15D,

	// NReg = R15 - RAX + 1
	NReg = 3 /* for test purposes */
};

#define WORD(r) (r + (EAX-RAX))
#define BASE(r) (r >= EAX ? r - (EAX-RAX) : r)

enum {
	NString = 32,
	NPred   = 15,
	NBlk    = 128,
	NIns    = 256,

	BITS    = 4,
	NBit    = 64,
};

struct Bits {
	uint64_t t[BITS];
};

#define BGET(b, n) (1&((b).t[n/NBit]>>(n%NBit)))
#define BSET(b, n) ((b).t[n/NBit] |= 1ll<<(n%NBit))
#define BCLR(b, n) ((b).t[n/NBit] &= ~(1ll<<(n%NBit)))

struct Ref {
	uint16_t type:2;
	uint16_t val:14;
};

enum {
	RTmp,
	RCon,
	RSlot,
	RReg,
	NRef = (1<<14) - 1
};

#define R        (Ref){0, 0}
#define TMP(x)   (Ref){RTmp, x}
#define CON(x)   (Ref){RCon, x}
#define CON_Z    CON(0)          /* reserved zero constant */
#define SLOT(x)  (Ref){RSlot, x}
#define REG(x)   (Ref){RReg, x}

static inline int req(Ref a, Ref b)
{ return a.type == b.type && a.val == b.val; }
static inline int rtype(Ref r)
{ return req(r, R) ? -1 : r.type; }

enum {
	Ceq,
	Csle,
	Cslt,
	Csgt, /* mirror opposite cmps! */
	Csge,
	Cne,
	NCmp,
};

#define COP(c) (c==Ceq||c==Cne ? c : NCmp-1 - c)

enum {
	OXXX,
	/* public instruction */
	OAdd,
	OSub,
	ODiv,
	ORem,
	OCmp,
	OCmp1 = OCmp + NCmp-1,
	OStore,
	OLoad,
	/* reserved instructions */
	ONop,
	OCopy,
	OSwap,
	OSign,
	OXDiv,
	OXCmpw,
	OXCmpl,
	OXSet,
	OXSet1 = OXSet + NCmp-1,
	OLast
};

enum {
	JXXX,
	JRet,
	JJmp,
	JJez,
	JXJc,
	JXJc1 = JXJc + NCmp-1,
	JLast
};

struct OpDesc {
	char *name;
	int arity;
	B3 comm;
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
	enum {
		TUndef,
		TWord,
		TLong,
	} type;
	char name[NString];
	uint ndef, nuse;
	uint cost;
	uint spill;
	int hint;
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
	Blk **rpo;
	uint nspill;
};


/* main.c */
extern char debug['Z'+1];
void dumpts(Bits *, Tmp *, FILE *);

/* parse.c */
extern OpDesc opdesc[];
void diag(char *);
void *alloc(size_t);
Blk *blocka(void);
Fn *parsefn(FILE *);
void printfn(Fn *, FILE *);

/* ssa.c */
void fillpreds(Fn *);
void fillrpo(Fn *);
void ssafix(Fn *, int);

/* live.c */
void filllive(Fn *);

/* isel.c */
void isel(Fn *);

/* spill.c */
int bcnt(Bits *);
void fillcost(Fn *);
void spill(Fn *);

/* rega.c */
void rega(Fn *);

/* emit.c */
void emitfn(Fn *, FILE *);
