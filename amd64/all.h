#include "../all.h"

typedef struct Amd64Op Amd64Op;

enum Amd64Reg {
	RAX = RXX+1, /* caller-save */
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

	RBP, /* globally live */
	RSP,

	XMM0, /* sse */
	XMM1,
	XMM2,
	XMM3,
	XMM4,
	XMM5,
	XMM6,
	XMM7,
	XMM8,
	XMM9,
	XMM10,
	XMM11,
	XMM12,
	XMM13,
	XMM14,
	XMM15,

	NFPR = XMM14 - XMM0 + 1, /* reserve XMM15 */
	NGPR = RSP - RAX + 1,
	NGPS = R11 - RAX + 1,
	NFPS = NFPR,
	NCLR = R15 - RBX + 1,
};
MAKESURE(reg_not_tmp, XMM15 < (int)Tmp0);

struct Amd64Op {
	char nmem;
	char zflag;
	char lflag;
};

/* targ.c */
extern Amd64Op amd64_op[];

/* sysv.c (abi) */
extern int amd64_sysv_rsave[];
extern int amd64_sysv_rclob[];
bits amd64_sysv_retregs(Ref, int[2]);
bits amd64_sysv_argregs(Ref, int[2]);
void amd64_sysv_abi(Fn *);

/* isel.c */
void amd64_isel(Fn *);

/* emit.c */
void amd64_emitfn(Fn *, FILE *);
