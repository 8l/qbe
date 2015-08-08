#include "lisc.h"


static char *rtoa[] = {
	[RXX] = "OH GOD!",
	[RAX] = "rax",
	[RBX] = "rbx",
	[RCX] = "rcx",
	[RDX] = "rdx",
	[RSI] = "rsi",
	[RDI] = "rdi",
	[RBP] = "rbp",
	[RSP] = "rsp",
	[R8] = "r8",
	[R9] = "r9",
	[R10] = "r10",
	[R11] = "r11",
	[R12] = "r12",
	[R13] = "r13",
	[R14] = "r14",
	[R15] = "r15",
	[EAX] = "eax",
	[EBX] = "ebx",
	[ECX] = "ecx",
	[EDX] = "edx",
	[ESI] = "esi",
	[EDI] = "edi",
	[R8D] = "r8d",
	[R9D] = "r9d",
	[R10D] = "r10d",
	[R11D] = "r11d",
	[R12D] = "r12d",
	[R13D] = "r13d",
	[R14D] = "r14d",
	[R15D] = "r15d",
};

static struct { char *s, *b; } rsub[] = {
	[RXX] = {"OH GOD!", "OH NO!"},
	[RAX] = {"ax", "al"},
	[RBX] = {"bx", "bl"},
	[RCX] = {"cx", "cl"},
	[RDX] = {"dx", "dl"},
	[RSI] = {"si", "sil"},
	[RDI] = {"di", "dil"},
	[RBP] = {"bp", "bpl"},
	[RSP] = {"sp", "spl"},
	[R8 ] = {"r8w", "r8b"},
	[R9 ] = {"r9w", "r9b"},
	[R10] = {"r10w", "r10b"},
	[R11] = {"r11w", "r11b"},
	[R12] = {"r12w", "r12b"},
	[R13] = {"r13w", "r13b"},
	[R14] = {"r14w", "r14b"},
	[R15] = {"r15w", "r15b"},
};

static char *ctoa[NCmp] = {
	[Ceq] = "e",
	[Csle] = "le",
	[Cslt] = "l",
	[Csgt] = "g",
	[Csge] = "ge",
	[Cne] = "ne",
};

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
eref(Ref r, Fn *fn, FILE *f)
{
	Con *c;

	switch (rtype(r)) {
	case RReg:
		fprintf(f, "%%%s", rtoa[r.val]);
		break;
	case RSlot:
		fprintf(f, "-%d(%%rbp)", 8 * r.val);
		break;
	case RCon:
		c = &fn->con[r.val];
		switch (c->type) {
		case CAddr:
			fprintf(f, "$%s", c->label);
			if (c->val)
				fprintf(f, "%+"PRId64, c->val);
			break;
		case CNum:
			fprintf(f, "$%"PRId64, c->val);
			break;
		default:
			diag("emitref: invalid constant");
		}
		break;
	default:
		diag("emitref: invalid reference");
	}
}

static void
emem(Ref r, Fn *fn, FILE *f)
{
	if (rtype(r) == RSlot)
		eref(r, fn, f);
	else {
		assert(rtype(r)!=RReg || BASE(r.val)==r.val);
		fprintf(f, "(");
		eref(r, fn, f);
		fprintf(f, ")");
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
		[OLoad]   = "mov",
		[OLoadss] = "movsw",
		[OLoadus] = "movzw",
		[OLoadsb] = "movsb",
		[OLoadub] = "movzb",
	};
	char *s;

	switch (i.op) {
	case OAdd:
	case OSub:
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
	case OCopy:
		if (!req(i.arg[0], i.to))
			eop("mov", i.arg[0], i.to, fn, f);
		break;
	case OStore:
		s = rtoa[i.arg[0].val];
		goto Store;
	case OStores:
		s = rsub[BASE(i.arg[0].val)].s;
		goto Store;
	case OStoreb:
		s = rsub[BASE(i.arg[0].val)].b;
	Store:
		assert(rtype(i.arg[0]) == RReg);
		fprintf(f, "\tmov %s, ", s);
		emem(i.arg[1], fn, f);
		fprintf(f, "\n");
		break;
	case OLoad:
	case OLoadss:
	case OLoadus:
	case OLoadsb:
	case OLoadub:
		fprintf(f, "\t%s ", otoa[i.op]);
		emem(i.arg[0], fn, f);
		fprintf(f, ", ");
		eref(i.to, fn, f);
		fprintf(f, "\n");
		break;
	case OSwap:
		eop("xchg", i.arg[0], i.arg[1], fn, f);
		break;
	case OSign:
		if (req(i.to, REG(RDX)) && req(i.arg[0], REG(RAX)))
			fprintf(f, "\tcqto\n");
		else if (req(i.to, REG(EDX)) && req(i.arg[0], REG(EAX)))
			fprintf(f, "\tcltd\n");
		else
			diag("emit: unhandled instruction (2)");
		break;
	case OXDiv:
		eop("idiv", i.arg[0], R, fn, f);
		break;
	case OXCmpw:
	case OXCmpl:
		eop(i.op == OXCmpw ? "cmpl" : "cmpq",
			i.arg[0], i.arg[1], fn, f);
		break;
	case ONop:
		break;
	default:
		if (OXSet <= i.op && i.op <= OXSet1) {
			eop("mov $0,", i.to, R, fn, f);
			fprintf(f, "\tset%s %%%s\n",
				ctoa[i.op-OXSet],
				rsub[BASE(i.to.val)].b);
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
		"\tsub $%u, %%rsp\n",
		fn->nspill * 8
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
