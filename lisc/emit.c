#include "lisc.h"


static char *rtoa[] = {
	[RXX] = "OH GOD!",

	[RAX] = "rax",
	[RCX] = "rcx",
	[RDX] = "rdx",
	[RSI] = "rsi",
	[RDI] = "rdi",
	[R8] = "r8",
	[R9] = "r9",
	[R10] = "r10",
	[R11] = "r11",

	[RBX] = "rbx",
	[R12] = "r12",
	[R13] = "r13",
	[R14] = "r14",
	[R15] = "r15",

	[RBP] = "rbp",
	[RSP] = "rsp",

	[EAX] = "eax",
	[ECX] = "ecx",
	[EDX] = "edx",
	[ESI] = "esi",
	[EDI] = "edi",
	[R8D] = "r8d",
	[R9D] = "r9d",
	[R10D] = "r10d",
	[R11D] = "r11d",

	[EBX] = "ebx",
	[R12D] = "r12d",
	[R13D] = "r13d",
	[R14D] = "r14d",
	[R15D] = "r15d",
};

static char *rbtoa[] = {
	[RXX] = "OH GOD!",


	[RAX] = "al",
	[RCX] = "cl",
	[RDX] = "dl",
	[RSI] = "sil",
	[RDI] = "dil",
	[R8] = "r8b",
	[R9] = "r9b",
	[R10] = "r10b",
	[R11] = "r11b",

	[RBX] = "bl",
	[R12] = "r12b",
	[R13] = "r13b",
	[R14] = "r14b",
	[R15] = "r15b",

	[RBP] = "bpl",
	[RSP] = "spl",

};

static char *ctoa[NCmp] = {
	[Ceq] = "e",
	[Csle] = "le",
};

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
				fprintf(f, "%+"PRIi64, c->val);
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
	static char *otoa[OLast] = {
		[OAdd] = "add",
		[OSub] = "sub",
	};

	switch (i.op) {
	case OAdd:
	case OSub:
		if (req(i.to, i.arg[1])) {
			if (!opdesc[i.op].comm)
				diag("emit: unhandled instruction (1)");
			i.arg[1] = i.arg[0];
			i.arg[0] = i.to;
		}
		if (!req(i.to, i.arg[0]))
			eop("mov", i.arg[0], i.to, fn, f);
		eop(otoa[i.op], i.arg[1], i.to, fn, f);
		break;
	case OStore:
		i.to = i.arg[1];
		/* fall through */
	case OCopy:
	case OLoad:
		if (!req(i.arg[0], i.to))
			eop("mov", i.arg[0], i.to, fn, f);
		break;
	case OSwap:
		eop("xchg", i.arg[0], i.arg[1], fn, f);
		break;
	case OSign:
		if (req(i.to, REG(RDX)) && req(i.arg[0], REG(RAX)))
			fprintf(f, "\tcqto\n");
		else if (req(i.to, REG(EDX)) && req(i.arg[0], REG(EAX)))
			fprintf(f, "\tcltq\n");
		else
			diag("emit: unhandled instruction (2)");
		break;
	case OXDiv:
		eop("idiv", i.arg[0], R, fn, f);
		break;
	case OXCmp:
		eop("cmp", i.arg[0], i.arg[1], fn, f);
		break;
	case ONop:
		break;
	default:
		if (OXSet <= i.op && i.op <= OXSet1) {
			eop("mov $0,", i.to, R, fn, f);
			fprintf(f, "\tset%s %%%s\n",
				ctoa[i.op-OXSet],
				rbtoa[BASE(i.to.val)]);
			break;
		}
		diag("emit: unhandled instruction (3)");
	}
}

void
emitfn(Fn *fn, FILE *f)
{
	char *js;
	Blk *b, *s;
	Ins *i;

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
		case JJez:
			if (b->s1 == b->link) {
				js = "jne";
				s = b->s2;
			} else if (b->s2 == b->link) {
				js = "je";
				s = b->s1;
			} else
				diag("emit: unhandled jump (1)");
			eop("cmp $0,", b->jmp.arg, R, fn, f);
			fprintf(f, "\t%s .L%s\n", js, s->name);
			break;
		default:
			diag("emit: unhandled jump (2)");
		}
	}

}
