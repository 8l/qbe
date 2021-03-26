#include "../all.h"

enum Arm64Reg {
	R0 = RXX + 1,
	     R1,  R2,  R3,  R4,  R5,  R6,  R7,
	R8,  R9,  R10, R11, R12, R13, R14, R15,
	IP0, IP1, R18, R19, R20, R21, R22, R23,
	R24, R25, R26, R27, R28, FP,  LR,  SP,

	V0,  V1,  V2,  V3,  V4,  V5,  V6,  V7,
	V8,  V9,  V10, V11, V12, V13, V14, V15,
	V16, V17, V18, V19, V20, V21, V22, V23,
	V24, V25, V26, V27, V28, V29, V30, /* V31, */

	NFPR = V30 - V0 + 1,
	NGPR = SP - R0 + 1,
	NGPS = R18 - R0 + 1 /* LR */ + 1,
	NFPS = (V7 - V0 + 1) + (V30 - V16 + 1),
	NCLR = (R28 - R19 + 1) + (V15 - V8 + 1),
};
MAKESURE(reg_not_tmp, V30 < (int)Tmp0);

/* targ.c */
extern int arm64_rsave[];
extern int arm64_rclob[];

/* abi.c */
bits arm64_retregs(Ref, int[2]);
bits arm64_argregs(Ref, int[2]);
void arm64_abi(Fn *);

/* isel.c */
int arm64_logimm(uint64_t, int);
void arm64_isel(Fn *);

/* emit.c */
void arm64_emitfn(Fn *, FILE *);
