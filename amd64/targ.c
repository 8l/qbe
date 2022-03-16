#include "all.h"

Amd64Op amd64_op[NOp] = {
#define O(op, t, x) [O##op] =
#define X(nm, zf, lf) { nm, zf, lf, },
	#include "../ops.h"
};

static int
amd64_memargs(int op)
{
	return amd64_op[op].nmem;
}

Target T_amd64_sysv = {
	.name = "amd64_sysv",
	.gpr0 = RAX,
	.ngpr = NGPR,
	.fpr0 = XMM0,
	.nfpr = NFPR,
	.rglob = BIT(RBP) | BIT(RSP),
	.nrglob = 2,
	.rsave = amd64_sysv_rsave,
	.nrsave = {NGPS, NFPS},
	.retregs = amd64_sysv_retregs,
	.argregs = amd64_sysv_argregs,
	.memargs = amd64_memargs,
	.abi = amd64_sysv_abi,
	.isel = amd64_isel,
	.emitfn = amd64_emitfn,
};
