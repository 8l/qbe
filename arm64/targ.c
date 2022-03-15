#include "all.h"

int arm64_rsave[] = {
	R0,  R1,  R2,  R3,  R4,  R5,  R6,  R7,
	R8,  R9,  R10, R11, R12, R13, R14, R15,
	IP0, IP1, R18, LR,
	V0,  V1,  V2,  V3,  V4,  V5,  V6,  V7,
	V16, V17, V18, V19, V20, V21, V22, V23,
	V24, V25, V26, V27, V28, V29, V30,
	-1
};
int arm64_rclob[] = {
	R19, R20, R21, R22, R23, R24, R25, R26,
	R27, R28,
	V8,  V9,  V10, V11, V12, V13, V14, V15,
	-1
};

#define RGLOB (BIT(FP) | BIT(SP) | BIT(R18))

static int
arm64_memargs(int op)
{
	(void)op;
	return 0;
}

Target T_arm64 = {
	.name = "arm64",
	.gpr0 = R0,
	.ngpr = NGPR,
	.fpr0 = V0,
	.nfpr = NFPR,
	.rglob = RGLOB,
	.nrglob = 3,
	.rsave = arm64_rsave,
	.nrsave = {NGPS, NFPS},
	.retregs = arm64_retregs,
	.argregs = arm64_argregs,
	.memargs = arm64_memargs,
	.abi = arm64_abi,
	.isel = arm64_isel,
	.emitfn = arm64_emitfn,
};

MAKESURE(globals_are_not_arguments,
	(RGLOB & (BIT(R8+1) - 1)) == 0
);
MAKESURE(arrays_size_ok,
	sizeof arm64_rsave == (NGPS+NFPS+1) * sizeof(int) &&
	sizeof arm64_rclob == (NCLR+1) * sizeof(int)
);
