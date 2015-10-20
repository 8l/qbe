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
typedef struct Dat Dat;

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

	NReg = RBX - RAX + 1,
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

enum Alt {
	AType,
	ACall,
	ASlot,

	AShift = 12,
	AMask = (1<<AShift) - 1
};

enum {
	RTmp,
	RCon,
	RAlt,

	RAType = RAlt + AType,
	RACall = RAlt + ACall,
	RASlot = RAlt + ASlot,

	NRef = (1<<14) - 1
};

#define R        (Ref){0, 0}
#define TMP(x)   (Ref){RTmp, x}
#define CON(x)   (Ref){RCon, x}
#define CON_Z    CON(0)          /* reserved zero constant */
#define TYPE(x)  (Ref){RAlt, (x)|(AType<<AShift)}
#define CALL(x)  (Ref){RAlt, (x)|(ACall<<AShift)}
#define SLOT(x)  (assert(x<(1<<(AShift-1)) && "too many slots"), \
                 (Ref){RAlt, (x)|(ASlot<<AShift)})

static inline int req(Ref a, Ref b)
{ return a.type == b.type && a.val == b.val; }
static inline int rtype(Ref r)
{
	if (req(r, R))
		return -1;
	if (r.type == RAlt)
		return RAlt + (r.val >> AShift);
	return r.type;
}
static inline int isreg(Ref r)
{ return rtype(r) == RTmp && r.val < Tmp0; }

#define CMPS(X) \
	X(eq) X(sle) X(slt) \
	X(sgt) X(sge) X(ne) /* mirror opposite cmps! */
#define COP(c) (c==Ceq||c==Cne ? c : NCmp-1 - c)

#define X(c) C##c,
enum Cmp { CMPS(X) NCmp };
#undef X

#define TYS(X) X(l) X(sw) X(uw) X(sh) X(uh) X(sb) X(ub)

#define X(t) T##t,
enum Ty { TYS(X) NTy };
#undef X

enum Op {
	OXXX,

	/* public instructions */
	OAdd,
	OSub,
	ODiv,
	ORem,
	OMul,
	OAnd,
	OCmp,
	OCmp1 = OCmp + NCmp-1,
	OStorel,
	OStorew,
	OStores,
	OStoreb,
	OLoad,
	OLoad1 = OLoad + NTy-1,
	OExt,
	OExt1 = OExt + NTy-1,
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
	OXScale1, /* memory addressing */
	OXScale2,
	OXScale3,
	OXScale4,
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
	short slot;
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
	int slot;
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

struct Dat {
	enum {
		DStart,
		DEnd,
		DName,
		DAlign,
		DA,
		DB,
		DH,
		DW,
		DL
	} type;
	union {
		int64_t num;
		char *str;
	} u;
};


/* main.c */
extern char debug['Z'+1];
void dumpts(Bits *, Tmp *, FILE *);

/* util.c */
extern Typ typ[NTyp];
extern Ins insb[NIns], *curi;
void diag(char *);
void *emalloc(size_t);
void *alloc(size_t);
void freeall(void);
Blk *bnew(void);
void emit(int, int, Ref, Ref, Ref);
void emiti(Ins);
int bcnt(Bits *);
void idup(Ins **, Ins *, ulong);
Ins *icpy(Ins *, Ins *, ulong);
void *vnew(ulong, size_t);
void vgrow(void *, ulong);
Ref newtmp(char *, Fn *);
Ref getcon(int64_t, Fn *);

/* parse.c */
extern OpDesc opdesc[NOp];
void parse(FILE *, void (Dat *), void (Fn *));
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
void fillcost(Fn *);
void spill(Fn *);

/* rega.c */
void rega(Fn *);

/* emit.c */
void emitfn(Fn *, FILE *);
void emitdat(Dat *, FILE *);
