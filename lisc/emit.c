#include "lisc.h"


enum { SLong, SWord, SShort, SByte };
static char *rsub[][4] = {
	[RXX] = {"BLACK CAT", "BROKEN MIRROR", "666", "NOOOO!"},
	[RAX] = {"rax", "eax", "ax", "al"},
	[RBX] = {"rbx", "ebx", "bx", "bl"},
	[RCX] = {"rcx", "ecx", "cx", "cl"},
	[RDX] = {"rdx", "edx", "dx", "dl"},
	[RSI] = {"rsi", "esi", "si", "sil"},
	[RDI] = {"rdi", "edi", "di", "dil"},
	[RBP] = {"rbp", "ebp", "bp", "bpl"},
	[RSP] = {"rsp", "esp", "sp", "spl"},
	[R8 ] = {"r8" , "r8d", "r8w", "r8b"},
	[R9 ] = {"r9" , "r9d", "r9w", "r9b"},
	[R10] = {"r10", "r10d", "r10w", "r10b"},
	[R11] = {"r11", "r11d", "r11w", "r11b"},
	[R12] = {"r12", "r12d", "r12w", "r12b"},
	[R13] = {"r13", "r13d", "r13w", "r13b"},
	[R14] = {"r14", "r14d", "r14w", "r14b"},
	[R15] = {"r15", "r15d", "r15w", "r15b"},
};

static char *ctoa[NCmp] = {
	[Ceq ] = "e",
	[Csle] = "le",
	[Cslt] = "l",
	[Csgt] = "g",
	[Csge] = "ge",
	[Cne ] = "ne",
};

static char *
rtoa(int r)
{
	if (r < EAX)
		return rsub[r][SLong];
	else
		return rsub[RBASE(r)][SWord];
}

static int
cneg(int cmp)
{
	switch (cmp) {
	default:   diag("cneg: unhandled comparison");
	case Ceq:  return Cne;
	case Csle: return Csgt;
	case Cslt: return Csge;
	case Csgt: return Csle;
	case Csge: return Cslt;
	case Cne:  return Ceq;
	}
}

static void
econ(Con *c, FILE *f)
{
	switch (c->type) {
	case CAddr:
		fprintf(f, "%s", c->label);
		if (c->val)
			fprintf(f, "%+"PRId64, c->val);
		break;
	case CNum:
		fprintf(f, "%"PRId64, c->val);
		break;
	default:
		diag("econ: invalid constant");
	}
}

static void
eref(Ref r, Fn *fn, FILE *f)
{
	switch (rtype(r)) {
	default:
		diag("emit: invalid reference");
	case RTmp:
		assert(r.val < Tmp0);
		fprintf(f, "%%%s", rtoa(r.val));
		break;
	case RSlot:
		fprintf(f, "-%d(%%rbp)", 4 * r.val);
		break;
	case RCon:
		fprintf(f, "$");
		econ(&fn->con[r.val], f);
		break;
	}
}

static void
emem(Ref r, Fn *fn, FILE *f)
{
	switch (rtype(r)) {
	default:
		diag("emit: invalid memory reference");
	case RSlot:
		eref(r, fn, f);
		break;
	case RCon:
		econ(&fn->con[r.val], f);
		break;
	case RTmp:
		assert(r.val < EAX);
		fprintf(f, "(%%%s)", rtoa(r.val));
		break;
	}
}

static void
eop(char *op, Ref a, Ref b, Fn *fn, FILE *f)
{
	fprintf(f, "\t%s ", op);
	eref(a, fn, f);
	if (!req(b, R)) {
		fprintf(f, ", ");
		eref(b, fn, f);
	}
	fprintf(f, "\n");
}

static void
eins(Ins i, Fn *fn, FILE *f)
{
	static char *otoa[NOp] = {
		[OAdd]    = "add",
		[OSub]    = "sub",
		[OMul]    = "imul",
		[OAnd]    = "and",
		[OSext]   = "movslq",
		[OZext]   = "movzlq",
		[OLoad]   = "mov",
		[OLoadss] = "movsw",
		[OLoadus] = "movzw",
		[OLoadsb] = "movsb",
		[OLoadub] = "movzb",
		[OXCmpw]  = "cmpl",
		[OXCmpl]  = "cmpq",
		[OXTestw] = "testl",
		[OXTestl] = "testq",
	};
	static char *stoa[] = {
		[OStorel - OStorel] = "q",
		[OStorew - OStorel] = "l",
		[OStores - OStorel] = "w",
		[OStoreb - OStorel] = "b",
	};
	Ref r0, r1;
	int reg;
	int64_t val;

	switch (i.op) {
	case OMul:
		if (rtype(i.arg[1]) == RCon) {
			r0 = i.arg[1];
			r1 = i.arg[0];
		} else {
			r0 = i.arg[0];
			r1 = i.arg[1];
		}
		if (rtype(r0) == RCon && rtype(r1) == RTmp) {
			val = fn->con[r0.val].val;
			fprintf(f, "\timul $%"PRId64", %%%s, %%%s\n",
				val, rtoa(r1.val), rtoa(i.to.val));
			break;
		}
		/* fall through */
	case OAdd:
	case OSub:
	case OAnd:
		if (req(i.to, i.arg[1])) {
			if (i.op == OSub) {
				eop("neg", i.to, R, fn, f);
				eop("add", i.arg[0], i.to, fn, f);
				break;
			}
			i.arg[1] = i.arg[0];
			i.arg[0] = i.to;
		}
		if (!req(i.to, i.arg[0]))
			eop("mov", i.arg[0], i.to, fn, f);
		eop(otoa[i.op], i.arg[1], i.to, fn, f);
		break;
	case OSext:
	case OZext:
		if (rtype(i.to) != RTmp || i.to.val >= EAX
		|| (rtype(i.arg[0]) == RTmp && i.arg[0].val < EAX))
			diag("emit: invalid extension");
		eop(otoa[i.op], i.arg[0], i.to, fn, f);
		break;
	case OCopy:
		if (req(i.to, R))
			break;
		if (i.to.val < EAX && rtype(i.arg[0]) == RCon) {
			val = fn->con[i.arg[0].val].val;
			if (0 <= val && val <= UINT32_MAX) {
				fprintf(f, "\tmov $%"PRId64", %%%s\n",
					val, rsub[i.to.val][SWord]);
				break;
			}
		} else if (!req(i.arg[0], i.to))
			eop("mov", i.arg[0], i.to, fn, f);
		break;
	case OStorel:
	case OStorew:
	case OStores:
	case OStoreb:
		fprintf(f, "\tmov%s ", stoa[i.op - OStorel]);
		if (rtype(i.arg[0]) == RTmp) {
			assert(i.arg[0].val < Tmp0);
			reg = RBASE(i.arg[0].val);
			fprintf(f, "%%%s", rsub[reg][i.op - OStorel]);
		} else
			eref(i.arg[0], fn, f);
		fprintf(f, ", ");
		emem(i.arg[1], fn, f);
		fprintf(f, "\n");
		break;
	case OLoad:
	case OLoadss:
	case OLoadus:
	case OLoadsb:
	case OLoadub:
		fprintf(f, "\t%s", otoa[i.op]);
		if (i.to.val < EAX)
			fprintf(f, "q ");
		else
			fprintf(f, "l ");
		emem(i.arg[0], fn, f);
		fprintf(f, ", ");
		eref(i.to, fn, f);
		fprintf(f, "\n");
		break;
	case OAlloc:
		eop("sub", i.arg[0], TMP(RSP), fn, f);
		if (!req(i.to, R))
			eop("mov", TMP(RSP), i.to, fn ,f);
		break;
	case OAddr:
		if (rtype(i.arg[0]) != RSlot)
			diag("emit: invalid addr instruction");
		eop("lea", i.arg[0], i.to, fn, f);
		break;
	case OSwap:
		eop("xchg", i.arg[0], i.arg[1], fn, f);
		break;
	case OSign:
		if (req(i.to, TMP(RDX)) && req(i.arg[0], TMP(RAX)))
			fprintf(f, "\tcqto\n");
		else if (req(i.to, TMP(EDX)) && req(i.arg[0], TMP(EAX)))
			fprintf(f, "\tcltd\n");
		else
			diag("emit: unhandled instruction (2)");
		break;
	case OXDiv:
		eop("idiv", i.arg[0], R, fn, f);
		break;
	case OXCmpw:
	case OXCmpl:
	case OXTestw:
	case OXTestl:
		eop(otoa[i.op], i.arg[0], i.arg[1], fn, f);
		break;
	case ONop:
		break;
	default:
		if (OXSet <= i.op && i.op <= OXSet1) {
			fprintf(f, "\tset%s %%%s\n",
				ctoa[i.op-OXSet],
				rsub[RBASE(i.to.val)][SByte]);
			fprintf(f, "\tmovzb %%%s, %%%s\n",
				rsub[RBASE(i.to.val)][SByte],
				rtoa(i.to.val));
			break;
		}
		diag("emit: unhandled instruction (3)");
	}
}

void
emitfn(Fn *fn, FILE *f)
{
	Blk *b, *s;
	Ins *i;
	int c;

	fprintf(f,
		".text\n"
		".globl liscf\n"
		".type liscf, @function\n"
		"liscf:\n"
		"\tpush %%rbp\n"
		"\tmov %%rsp, %%rbp\n"
	);
	for (b=fn->start; b; b=b->link) {
		fprintf(f, ".L%s:\n", b->name);
		for (i=b->ins; i-b->ins < b->nins; i++)
			eins(*i, fn, f);
		switch (b->jmp.type) {
		case JRet:
			fprintf(f,
				"\tleave\n"
				"\tret\n"
			);
			break;
		case JJmp:
			if (b->s1 != b->link)
				fprintf(f, "\tjmp .L%s\n", b->s1->name);
			break;
		default:
			c = b->jmp.type - JXJc;
			if (0 <= c && c <= NCmp) {
				if (b->link == b->s2) {
					s = b->s1;
				} else if (b->link == b->s1) {
					c = cneg(c);
					s = b->s2;
				} else
					diag("emit: unhandled jump (1)");
				fprintf(f, "\tj%s .L%s\n", ctoa[c], s->name);
				break;
			}
			diag("emit: unhandled jump (2)");
		}
	}

}
