#include "lisc.h"
#include <stdarg.h>

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

static void
emitf(Fn *fn, FILE *f, char *fmt, ...)
{
	static char stoa[] = "qlwb";
	va_list ap;
	char c, *s, *s1;
	int i, ty;
	Ref ref;
	Con *con;

	va_start(ap, fmt);
	ty = SWord;
	s = fmt;
Next:
	while ((c = *s++) != '%')
		if (!c) {
			va_end(ap);
			return;
		} else
			fputc(c, f);
	switch ((c = *s++)) {
	default:
		diag("emit: unknown escape");
	case 'w':
	case 'W':
		i = va_arg(ap, int);
		ty = i ? SLong: SWord;
	if (0) {
	case 't':
	case 'T':
		ty = va_arg(ap, int);
	}
		if (c == 't' || c == 'w')
			fputc(stoa[ty], f);
		break;
	case 's':
		s1 = va_arg(ap, char *);
		fputs(s1, f);
		break;
	case 'R':
		ref = va_arg(ap, Ref);
		switch (rtype(ref)) {
		default:
			diag("emit: invalid reference");
		case RTmp:
			assert(isreg(ref));
			fprintf(f, "%%%s", rsub[ref.val][ty]);
			break;
		case RSlot:
		Slot:
			fprintf(f, "-%d(%%rbp)", 4 * ref.val);
			break;
		case RCon:
			fputc('$', f);
		Con:
			con = &fn->con[ref.val];
			switch (con->type) {
			default:
				diag("emit: invalid constant");
			case CAddr:
				fputs(con->label, f);
				if (con->val)
					fprintf(f, "%+"PRId64, con->val);
				break;
			case CNum:
				fprintf(f, "%"PRId64, con->val);
				break;
			}
			break;
		}
		break;
	case 'M':
		ref = va_arg(ap, Ref);
		switch (rtype(ref)) {
		default:    diag("emit: invalid memory reference");
		case RSlot: goto Slot;
		case RCon:  goto Con;
		case RTmp:
			assert(isreg(ref));
			fprintf(f, "(%%%s)", rsub[ref.val][SLong]);
			break;
		}
		break;
	}
	goto Next;
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
eins(Ins i, Fn *fn, FILE *f)
{
	static char *otoa[NOp] = {
		[OAdd]    = "add",
		[OSub]    = "sub",
		[OMul]    = "imul",
		[OAnd]    = "and",
		[OSext]   = "movsl",
		[OZext]   = "movzl",
		[OLoad]   = "mov",
		[OLoadss] = "movsw",
		[OLoadus] = "movzw",
		[OLoadsb] = "movsb",
		[OLoadub] = "movzb",
	};
	Ref r0, r1;
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
			emitf(fn, f, "\timul%w %R, %R, %R\n", i.wide, r0, r1, i.to);
			break;
		}
		/* fall through */
	case OAdd:
	case OSub:
	case OAnd:
		if (req(i.to, i.arg[1])) {
			if (i.op == OSub) {
				emitf(fn, f, "\tneg%w %R\n", i.wide, i.to);
				emitf(fn, f, "\tadd%w %R, %R\n",
					i.wide, i.arg[0], i.to);
				break;
			}
			i.arg[1] = i.arg[0];
			i.arg[0] = i.to;
		}
		if (!req(i.to, i.arg[0]))
			emitf(fn, f, "\tmov%w %R, %R\n", i.wide, i.arg[0], i.to);
		emitf(fn, f, "\t%s%w %R, %R\n", otoa[i.op], i.wide, i.arg[1], i.to);
		break;
	case OSext:
	case OZext:
		emitf(fn, f, "\t%sq %R, %W%R\n", otoa[i.op],
			i.arg[0], i.wide, i.to.val);
		break;
	case OCopy:
		if (req(i.to, R))
			break;
		if (isreg(i.to)
		&& i.wide
		&& rtype(i.arg[0]) == RCon
		&& fn->con[i.arg[0].val].type == CNum
		&& (val = fn->con[i.arg[0].val].val) >= 0
		&& val <= UINT32_MAX) {
			emitf(fn, f, "\tmovl %R, %R\n", i.arg[0], i.to);
		} else if (!req(i.arg[0], i.to))
			emitf(fn, f, "\tmov%w %R, %R\n", i.wide, i.arg[0], i.to);
		break;
	case OStorel:
	case OStorew:
	case OStores:
	case OStoreb:
		emitf(fn, f, "\tmov%t %R, %M\n", i.op - OStorel, i.arg[0], i.arg[1]);
		break;
	case OLoad:
	case OLoadss:
	case OLoadus:
	case OLoadsb:
	case OLoadub:
		emitf(fn, f, "\t%s%w %M, %R\n", otoa[i.op], i.wide, i.arg[0], i.to);
		break;
	case OAlloc:
		emitf(fn, f, "\tsub%w %R, %R\n", 1, i.arg[0], TMP(RSP));
		emitf(fn, f, "\tmov%w %R, %R\n", 1, TMP(RSP), i.to);
		break;
	case OAddr:
		emitf(fn, f, "\tlea%w %M, %R\n", i.wide, i.arg[0], i.to);
		break;
	case OSwap:
		emitf(fn, f, "\txchg%w %R, %R", i.wide, i.arg[0], i.arg[1]);
		break;
	case OSign:
		if (req(i.to, TMP(RDX)) && req(i.arg[0], TMP(RAX))) {
			if (i.wide)
				fprintf(f, "\tcqto\n");
			else
				fprintf(f, "\tcltd\n");
		} else
			diag("emit: unhandled instruction (2)");
		break;
	case OXDiv:
		emitf(fn, f, "\tidiv%w %R\n", i.wide, i.arg[0]);
		break;
	case OXCmp:
		if (isreg(i.arg[1]) && req(i.arg[0], CON_Z)) {
			emitf(fn, f, "\ttest%w %R, %R\n", i.wide, i.arg[1], i.arg[1]);
			break;
		}
		emitf(fn, f, "\tcmp%w %R, %R\n", i.wide, i.arg[0], i.arg[1]);
		break;
	case OXTest:
		emitf(fn, f, "\ttest%w %R, %R\n", i.wide, i.arg[0], i.arg[1]);
		break;
	case ONop:
		break;
	default:
		if (OXSet <= i.op && i.op <= OXSet1) {
			emitf(fn, f, "\tset%s%t %R\n",
				ctoa[i.op-OXSet], SByte, i.to);
			emitf(fn, f, "\tmovzb%w %T%R, %W%R\n",
				i.wide, SByte, i.to, i.wide, i.to);
			break;
		}
		diag("emit: unhandled instruction (3)");
	}
}

static int
framesz(Fn *fn)
{
	int i, a, f;

	f = 0;
	for (i=NAlign-1, a=1<<i; i>=0; i--, a/=2)
		if (f == 0 || f - a == fn->svec[i])
			f = fn->svec[i];
	a = 1 << (NAlign-2);
	while ((f + a) % (2 * a) != a)
		f += a - f % a;
	return f * 16 / (1 << (NAlign-1));
}

void
emitfn(Fn *fn, FILE *f)
{
	Blk *b, *s;
	Ins *i;
	int c, fs;

	fprintf(f,
		".text\n"
		".globl liscf\n"
		".type liscf, @function\n"
		"liscf:\n"
		"\tpush %%rbp\n"
		"\tmov %%rsp, %%rbp\n"
	);
	fs = framesz(fn);
	if (fs)
		fprintf(f, "\tsub $%d, %%rsp\n", fs);
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
