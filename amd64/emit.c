#include "all.h"


#define CMP(X) \
	X(Ciule,      "be") \
	X(Ciult,      "b")  \
	X(Cisle,      "le") \
	X(Cislt,      "l")  \
	X(Cisgt,      "g")  \
	X(Cisge,      "ge") \
	X(Ciugt,      "a")  \
	X(Ciuge,      "ae") \
	X(Cieq,       "z")  \
	X(Cine,       "nz") \
	X(NCmpI+Cfle, "be") \
	X(NCmpI+Cflt, "b")  \
	X(NCmpI+Cfgt, "a")  \
	X(NCmpI+Cfge, "ae") \
	X(NCmpI+Cfeq, "z")  \
	X(NCmpI+Cfne, "nz") \
	X(NCmpI+Cfo,  "np") \
	X(NCmpI+Cfuo, "p")

enum {
	SLong = 0,
	SWord = 1,
	SShort = 2,
	SByte = 3,

	Ki = -1, /* matches Kw and Kl */
	Ka = -2, /* matches all classes */
};

/* Instruction format strings:
 *
 * if the format string starts with -, the instruction
 * is assumed to be 3-address and is put in 2-address
 * mode using an extra mov if necessary
 *
 * if the format string starts with +, the same as the
 * above applies, but commutativity is also assumed
 *
 * %k  is used to set the class of the instruction,
 *     it'll expand to "l", "q", "ss", "sd", depending
 *     on the instruction class
 * %0  designates the first argument
 * %1  designates the second argument
 * %=  designates the result
 *
 * if %k is not used, a prefix to 0, 1, or = must be
 * added, it can be:
 *   M - memory reference
 *   L - long  (64 bits)
 *   W - word  (32 bits)
 *   H - short (16 bits)
 *   B - byte  (8 bits)
 *   S - single precision float
 *   D - double precision float
 */
static struct {
	short op;
	short cls;
	char *asm;
} omap[] = {
	{ Oadd,    Ka, "+add%k %1, %=" },
	{ Osub,    Ka, "-sub%k %1, %=" },
	{ Oand,    Ki, "+and%k %1, %=" },
	{ Oor,     Ki, "+or%k %1, %=" },
	{ Oxor,    Ki, "+xor%k %1, %=" },
	{ Osar,    Ki, "-sar%k %B1, %=" },
	{ Oshr,    Ki, "-shr%k %B1, %=" },
	{ Oshl,    Ki, "-shl%k %B1, %=" },
	{ Omul,    Ki, "+imul%k %1, %=" },
	{ Omul,    Ks, "+mulss %1, %=" },
	{ Omul,    Kd, "+mulsd %1, %=" },
	{ Odiv,    Ka, "-div%k %1, %=" },
	{ Ostorel, Ka, "movq %L0, %M1" },
	{ Ostorew, Ka, "movl %W0, %M1" },
	{ Ostoreh, Ka, "movw %H0, %M1" },
	{ Ostoreb, Ka, "movb %B0, %M1" },
	{ Ostores, Ka, "movss %S0, %M1" },
	{ Ostored, Ka, "movsd %D0, %M1" },
	{ Oload,   Ka, "mov%k %M0, %=" },
	{ Oloadsw, Kl, "movslq %M0, %L=" },
	{ Oloadsw, Kw, "movl %M0, %W=" },
	{ Oloaduw, Ki, "movl %M0, %W=" },
	{ Oloadsh, Ki, "movsw%k %M0, %=" },
	{ Oloaduh, Ki, "movzw%k %M0, %=" },
	{ Oloadsb, Ki, "movsb%k %M0, %=" },
	{ Oloadub, Ki, "movzb%k %M0, %=" },
	{ Oextsw,  Kl, "movslq %W0, %L=" },
	{ Oextuw,  Kl, "movl %W0, %W=" },
	{ Oextsh,  Ki, "movsw%k %H0, %=" },
	{ Oextuh,  Ki, "movzw%k %H0, %=" },
	{ Oextsb,  Ki, "movsb%k %B0, %=" },
	{ Oextub,  Ki, "movzb%k %B0, %=" },

	{ Oexts,   Kd, "cvtss2sd %0, %=" },
	{ Otruncd, Ks, "cvtsd2ss %0, %=" },
	{ Ostosi,  Ki, "cvttss2si%k %0, %=" },
	{ Odtosi,  Ki, "cvttsd2si%k %0, %=" },
	{ Oswtof,  Ka, "cvtsi2%k %W0, %=" },
	{ Osltof,  Ka, "cvtsi2%k %L0, %=" },
	{ Ocast,   Ki, "movq %D0, %L=" },
	{ Ocast,   Ka, "movq %L0, %D=" },

	{ Oaddr,   Ki, "lea%k %M0, %=" },
	{ Oswap,   Ki, "xchg%k %0, %1" },
	{ Osign,   Kl, "cqto" },
	{ Osign,   Kw, "cltd" },
	{ Oxdiv,   Ki, "div%k %0" },
	{ Oxidiv,  Ki, "idiv%k %0" },
	{ Oxcmp,   Ks, "ucomiss %S0, %S1" },
	{ Oxcmp,   Kd, "ucomisd %D0, %D1" },
	{ Oxcmp,   Ki, "cmp%k %0, %1" },
	{ Oxtest,  Ki, "test%k %0, %1" },
#define X(c, s) \
	{ Oflag+c, Ki, "set" s " %B=\n\tmovzb%k %B=, %=" },
	CMP(X)
#undef X
	{ NOp, 0, 0 }
};

static char *rname[][4] = {
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


static int
slot(int s, Fn *fn)
{
	struct { int i:29; } x;

	/* sign extend s using a bitfield */
	x.i = s;
	assert(x.i <= fn->slot);
	/* specific to NAlign == 3 */
	if (x.i < 0)
		return -4 * x.i;
	else if (fn->vararg)
		return -176 + -4 * (fn->slot - x.i);
	else
		return -4 * (fn->slot - x.i);
}

static void
emitcon(Con *con, FILE *f)
{
	char *p, *l;

	switch (con->type) {
	case CAddr:
		l = str(con->label);
		p = con->local ? gasloc : l[0] == '"' ? "" : gassym;
		fprintf(f, "%s%s", p, l);
		if (con->bits.i)
			fprintf(f, "%+"PRId64, con->bits.i);
		break;
	case CBits:
		fprintf(f, "%"PRId64, con->bits.i);
		break;
	default:
		die("unreachable");
	}
}

static char *
regtoa(int reg, int sz)
{
	static char buf[6];

	assert(reg <= XMM15);
	if (reg >= XMM0) {
		sprintf(buf, "xmm%d", reg-XMM0);
		return buf;
	} else
		return rname[reg][sz];
}

static Ref
getarg(char c, Ins *i)
{
	switch (c) {
	case '0':
		return i->arg[0];
	case '1':
		return i->arg[1];
	case '=':
		return i->to;
	default:
		die("invalid arg letter %c", c);
	}
}

static void emitins(Ins, Fn *, FILE *);

static void
emitcopy(Ref r1, Ref r2, int k, Fn *fn, FILE *f)
{
	Ins icp;

	icp.op = Ocopy;
	icp.arg[0] = r2;
	icp.to = r1;
	icp.cls = k;
	emitins(icp, fn, f);
}

static void
emitf(char *s, Ins *i, Fn *fn, FILE *f)
{
	static char clstoa[][3] = {"l", "q", "ss", "sd"};
	char c;
	int sz;
	Ref ref;
	Mem *m;
	Con off;

	switch (*s) {
	case '+':
		if (req(i->arg[1], i->to)) {
			ref = i->arg[0];
			i->arg[0] = i->arg[1];
			i->arg[1] = ref;
		}
		/* fall through */
	case '-':
		assert((!req(i->arg[1], i->to) || req(i->arg[0], i->to)) &&
			"cannot convert to 2-address");
		emitcopy(i->to, i->arg[0], i->cls, fn, f);
		s++;
		break;
	}

	fputc('\t', f);
Next:
	while ((c = *s++) != '%')
		if (!c) {
			fputc('\n', f);
			return;
		} else
			fputc(c, f);
	switch ((c = *s++)) {
	case '%':
		fputc('%', f);
		break;
	case 'k':
		fputs(clstoa[i->cls], f);
		break;
	case '0':
	case '1':
	case '=':
		sz = KWIDE(i->cls) ? SLong : SWord;
		s--;
		goto Ref;
	case 'D':
	case 'S':
		sz = SLong; /* does not matter for floats */
	Ref:
		c = *s++;
		ref = getarg(c, i);
		switch (rtype(ref)) {
		case RTmp:
			assert(isreg(ref));
			fprintf(f, "%%%s", regtoa(ref.val, sz));
			break;
		case RSlot:
			fprintf(f, "%d(%%rbp)", slot(ref.val, fn));
			break;
		case RMem:
		Mem:
			m = &fn->mem[ref.val];
			if (rtype(m->base) == RSlot) {
				off.type = CBits;
				off.bits.i = slot(m->base.val, fn);
				addcon(&m->offset, &off);
				m->base = TMP(RBP);
			}
			if (m->offset.type != CUndef)
				emitcon(&m->offset, f);
			fputc('(', f);
			if (!req(m->base, R))
				fprintf(f, "%%%s", regtoa(m->base.val, SLong));
			else if (m->offset.type == CAddr)
				fprintf(f, "%%rip");
			if (!req(m->index, R))
				fprintf(f, ", %%%s, %d",
					regtoa(m->index.val, SLong),
					m->scale
				);
			fputc(')', f);
			break;
		case RCon:
			fputc('$', f);
			emitcon(&fn->con[ref.val], f);
			break;
		default:
			die("unreachable");
		}
		break;
	case 'L':
		sz = SLong;
		goto Ref;
	case 'W':
		sz = SWord;
		goto Ref;
	case 'H':
		sz = SShort;
		goto Ref;
	case 'B':
		sz = SByte;
		goto Ref;
	case 'M':
		c = *s++;
		ref = getarg(c, i);
		switch (rtype(ref)) {
		case RMem:
			goto Mem;
		case RSlot:
			fprintf(f, "%d(%%rbp)", slot(ref.val, fn));
			break;
		case RCon:
			off = fn->con[ref.val];
			emitcon(&off, f);
			if (off.type == CAddr)
				fprintf(f, "(%%rip)");
			break;
		case RTmp:
			assert(isreg(ref));
			fprintf(f, "(%%%s)", regtoa(ref.val, SLong));
			break;
		default:
			die("unreachable");
		}
		break;
	default:
		die("invalid format specifier %%%c", c);
	}
	goto Next;
}

static void *negmask[4] = {
	[Ks] = (uint32_t[4]){ 0x80000000 },
	[Kd] = (uint64_t[2]){ 0x8000000000000000 },
};

static void
emitins(Ins i, Fn *fn, FILE *f)
{
	Ref r;
	int64_t val;
	int o, t0;
	Ins ineg;

	switch (i.op) {
	default:
	Table:
		/* most instructions are just pulled out of
		 * the table omap[], some special cases are
		 * detailed below */
		for (o=0;; o++) {
			/* this linear search should really be a binary
			 * search */
			if (omap[o].op == NOp)
				die("no match for %s(%c)",
					optab[i.op].name, "wlsd"[i.cls]);
			if (omap[o].op == i.op)
			if (omap[o].cls == i.cls
			|| (omap[o].cls == Ki && KBASE(i.cls) == 0)
			|| (omap[o].cls == Ka))
				break;
		}
		emitf(omap[o].asm, &i, fn, f);
		break;
	case Onop:
		/* just do nothing for nops, they are inserted
		 * by some passes */
		break;
	case Omul:
		/* here, we try to use the 3-addresss form
		 * of multiplication when possible */
		if (rtype(i.arg[1]) == RCon) {
			r = i.arg[0];
			i.arg[0] = i.arg[1];
			i.arg[1] = r;
		}
		if (KBASE(i.cls) == 0 /* only available for ints */
		&& rtype(i.arg[0]) == RCon
		&& rtype(i.arg[1]) == RTmp) {
			emitf("imul%k %0, %1, %=", &i, fn, f);
			break;
		}
		goto Table;
	case Osub:
		/* we have to use the negation trick to handle
		 * some 3-address subtractions */
		if (req(i.to, i.arg[1]) && !req(i.arg[0], i.to)) {
			ineg = (Ins){Oneg, i.cls, i.to, {i.to}};
			emitins(ineg, fn, f);
			emitf("add%k %0, %=", &i, fn, f);
			break;
		}
		goto Table;
	case Oneg:
		if (!req(i.to, i.arg[0]))
			emitf("mov%k %0, %=", &i, fn, f);
		if (KBASE(i.cls) == 0)
			emitf("neg%k %=", &i, fn, f);
		else
			fprintf(f,
				"\txorp%c %sfp%d(%%rip), %%%s\n",
				"xxsd"[i.cls],
				gasloc,
				gasstash(negmask[i.cls], 16),
				regtoa(i.to.val, SLong)
			);
		break;
	case Odiv:
		/* use xmm15 to adjust the instruction when the
		 * conversion to 2-address in emitf() would fail */
		if (req(i.to, i.arg[1])) {
			i.arg[1] = TMP(XMM0+15);
			emitf("mov%k %=, %1", &i, fn, f);
			emitf("mov%k %0, %=", &i, fn, f);
			i.arg[0] = i.to;
		}
		goto Table;
	case Ocopy:
		/* copies are used for many things; see my note
		 * to understand how to load big constants:
		 * https://c9x.me/notes/2015-09-19.html */
		assert(rtype(i.to) != RMem);
		if (req(i.to, R) || req(i.arg[0], R))
			break;
		if (req(i.to, i.arg[0]))
			break;
		t0 = rtype(i.arg[0]);
		if (i.cls == Kl
		&& t0 == RCon
		&& fn->con[i.arg[0].val].type == CBits) {
			val = fn->con[i.arg[0].val].bits.i;
			if (isreg(i.to))
			if (val >= 0 && val <= UINT32_MAX) {
				emitf("movl %W0, %W=", &i, fn, f);
				break;
			}
			if (rtype(i.to) == RSlot)
			if (val < INT32_MIN || val > INT32_MAX) {
				emitf("movl %0, %=", &i, fn, f);
				emitf("movl %0>>32, 4+%=", &i, fn, f);
				break;
			}
		}
		if (isreg(i.to)
		&& t0 == RCon
		&& fn->con[i.arg[0].val].type == CAddr) {
			emitf("lea%k %M0, %=", &i, fn, f);
			break;
		}
		if (rtype(i.to) == RSlot
		&& (t0 == RSlot || t0 == RMem)) {
			i.cls = KWIDE(i.cls) ? Kd : Ks;
			i.arg[1] = TMP(XMM0+15);
			emitf("mov%k %0, %1", &i, fn, f);
			emitf("mov%k %1, %=", &i, fn, f);
			break;
		}
		/* conveniently, the assembler knows if it
		 * should use movabsq when reading movq */
		emitf("mov%k %0, %=", &i, fn, f);
		break;
	case Ocall:
		/* calls simply have a weird syntax in AT&T
		 * assembly... */
		switch (rtype(i.arg[0])) {
		case RCon:
			fprintf(f, "\tcallq ");
			emitcon(&fn->con[i.arg[0].val], f);
			fprintf(f, "\n");
			break;
		case RTmp:
			emitf("callq *%L0", &i, fn, f);
			break;
		default:
			die("invalid call argument");
		}
		break;
	case Osalloc:
		/* there is no good reason why this is here
		 * maybe we should split Osalloc in 2 different
		 * instructions depending on the result
		 */
		emitf("subq %L0, %%rsp", &i, fn, f);
		if (!req(i.to, R))
			emitcopy(i.to, TMP(RSP), Kl, fn, f);
		break;
	case Oswap:
		if (KBASE(i.cls) == 0)
			goto Table;
		/* for floats, there is no swap instruction
		 * so we use xmm15 as a temporary
		 */
		emitcopy(TMP(XMM0+15), i.arg[0], i.cls, fn, f);
		emitcopy(i.arg[0], i.arg[1], i.cls, fn, f);
		emitcopy(i.arg[1], TMP(XMM0+15), i.cls, fn, f);
		break;
	}
}

static uint64_t
framesz(Fn *fn)
{
	uint64_t i, o, f;

	/* specific to NAlign == 3 */
	for (i=0, o=0; i<NCLR; i++)
		o ^= 1 & (fn->reg >> amd64_sysv_rclob[i]);
	f = fn->slot;
	f = (f + 3) & -4;
	return 4*f + 8*o + 176*fn->vararg;
}

void
amd64_emitfn(Fn *fn, FILE *f)
{
	static char *ctoa[] = {
	#define X(c, s) [c] = s,
		CMP(X)
	#undef X
	};
	static int id0;
	Blk *b, *s;
	Ins *i, itmp;
	int *r, c, o, n, lbl;
	uint64_t fs;

	gasemitlnk(fn->name, &fn->lnk, ".text", f);
	fputs("\tpushq %rbp\n\tmovq %rsp, %rbp\n", f);
	fs = framesz(fn);
	if (fs)
		fprintf(f, "\tsubq $%"PRIu64", %%rsp\n", fs);
	if (fn->vararg) {
		o = -176;
		for (r=amd64_sysv_rsave; r<&amd64_sysv_rsave[6]; r++, o+=8)
			fprintf(f, "\tmovq %%%s, %d(%%rbp)\n", rname[*r][0], o);
		for (n=0; n<8; ++n, o+=16)
			fprintf(f, "\tmovaps %%xmm%d, %d(%%rbp)\n", n, o);
	}
	for (r=amd64_sysv_rclob; r<&amd64_sysv_rclob[NCLR]; r++)
		if (fn->reg & BIT(*r)) {
			itmp.arg[0] = TMP(*r);
			emitf("pushq %L0", &itmp, fn, f);
			fs += 8;
		}

	for (lbl=0, b=fn->start; b; b=b->link) {
		if (lbl || b->npred > 1)
			fprintf(f, "%sbb%d:\n", gasloc, id0+b->id);
		for (i=b->ins; i!=&b->ins[b->nins]; i++)
			emitins(*i, fn, f);
		lbl = 1;
		switch (b->jmp.type) {
		case Jret0:
			if (fn->dynalloc)
				fprintf(f,
					"\tmovq %%rbp, %%rsp\n"
					"\tsubq $%"PRIu64", %%rsp\n",
					fs
				);
			for (r=&amd64_sysv_rclob[NCLR]; r>amd64_sysv_rclob;)
				if (fn->reg & BIT(*--r)) {
					itmp.arg[0] = TMP(*r);
					emitf("popq %L0", &itmp, fn, f);
				}
			fprintf(f,
				"\tleave\n"
				"\tret\n"
			);
			break;
		case Jjmp:
		Jmp:
			if (b->s1 != b->link)
				fprintf(f, "\tjmp %sbb%d\n",
					gasloc, id0+b->s1->id);
			else
				lbl = 0;
			break;
		default:
			c = b->jmp.type - Jjf;
			if (0 <= c && c <= NCmp) {
				if (b->link == b->s2) {
					s = b->s1;
					b->s1 = b->s2;
					b->s2 = s;
				} else
					c = cmpneg(c);
				fprintf(f, "\tj%s %sbb%d\n", ctoa[c],
					gasloc, id0+b->s2->id);
				goto Jmp;
			}
			die("unhandled jump %d", b->jmp.type);
		}
	}
	id0 += fn->nblk;
}
