#include "all.h"

char *locprefix, *symprefix;

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
	{ Otruncd, Ks, "cvttsd2ss %0, %=" },
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
	{ Oxcmp,   Ks, "comiss %S0, %S1" },
	{ Oxcmp,   Kd, "comisd %D0, %D1" },
	{ Oxcmp,   Ki, "cmp%k %0, %1" },
	{ Oxtest,  Ki, "test%k %0, %1" },
	{ Oxset+ICule, Ki, "setbe %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICult, Ki, "setb %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICsle, Ki, "setle %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICslt, Ki, "setl %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICsgt, Ki, "setg %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICsge, Ki, "setge %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICugt, Ki, "seta %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICuge, Ki, "setae %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICeq,  Ki, "setz %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICne,  Ki, "setnz %B=\n\tmovzb%k %B=, %=" },
	{ Oxset+ICxnp, Ki, "setnp %B=\n\tmovsb%k %B=, %=" },
	{ Oxset+ICxp,  Ki, "setp %B=\n\tmovsb%k %B=, %=" },
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
	switch (con->type) {
	case CAddr:
		if (con->local)
			fprintf(f, "%s%s", locprefix, con->label);
		else
			fprintf(f, "%s%s", symprefix, con->label);
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
			if (req(m->base, R))
				fprintf(f, "%%rip");
			else
				fprintf(f, "%%%s", regtoa(m->base.val, SLong));
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
			emitcon(&fn->con[ref.val], f);
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

static void
emitins(Ins i, Fn *fn, FILE *f)
{
	Ref r;
	int64_t val;
	int o;

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
				die("no match for %s(%d)", opdesc[i.op].name, i.cls);
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
		 * some 3-address substractions */
		if (req(i.to, i.arg[1])) {
			emitf("neg%k %=", &i, fn, f);
			emitf("add%k %0, %=", &i, fn, f);
			break;
		}
		goto Table;
	case Ocopy:
		/* make sure we don't emit useless copies,
		 * also, we can use a trick to load 64-bits
		 * registers, it's detailed in my note below
		 * http://c9x.me/art/notes.html?09/19/2015 */
		if (req(i.to, R) || req(i.arg[0], R))
			break;
		if (isreg(i.to)
		&& rtype(i.arg[0]) == RCon
		&& i.cls == Kl
		&& fn->con[i.arg[0].val].type == CBits
		&& (val = fn->con[i.arg[0].val].bits.i) >= 0
		&& val <= UINT32_MAX) {
			emitf("movl %W0, %W=", &i, fn, f);
		} else if (isreg(i.to)
		&& rtype(i.arg[0]) == RCon
		&& fn->con[i.arg[0].val].type == CAddr) {
			emitf("lea%k %M0, %=", &i, fn, f);
		} else if (!req(i.arg[0], i.to))
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

static int
cneg(int cmp)
{
	switch (cmp) {
	default:    die("invalid int comparison %d", cmp);
	case ICule: return ICugt;
	case ICult: return ICuge;
	case ICsle: return ICsgt;
	case ICslt: return ICsge;
	case ICsgt: return ICsle;
	case ICsge: return ICslt;
	case ICugt: return ICule;
	case ICuge: return ICult;
	case ICeq:  return ICne;
	case ICne:  return ICeq;
	case ICxnp: return ICxp;
	case ICxp:  return ICxnp;
	}
}

static int
framesz(Fn *fn)
{
	int i, o, f;

	/* specific to NAlign == 3 */
	for (i=0, o=0; i<NRClob; i++)
		o ^= 1 & (fn->reg >> rclob[i]);
	f = fn->slot;
	f = (f + 3) & -4;
	return 4*f + 8*o + 176*fn->vararg;
}

void
emitfn(Fn *fn, FILE *f)
{
	static char *ctoa[] = {
		[ICeq]  = "z",
		[ICule] = "be",
		[ICult] = "b",
		[ICsle] = "le",
		[ICslt] = "l",
		[ICsgt] = "g",
		[ICsge] = "ge",
		[ICugt] = "a",
		[ICuge] = "ae",
		[ICne]  = "nz",
		[ICxnp] = "np",
		[ICxp]  = "p"
	};
	static int id0;
	Blk *b, *s;
	Ins *i, itmp;
	int *r, c, fs, o, n, lbl;

	fprintf(f, ".text\n");
	if (fn->export)
		fprintf(f, ".globl %s%s\n", symprefix, fn->name);
	fprintf(f,
		"%s%s:\n"
		"\tpushq %%rbp\n"
		"\tmovq %%rsp, %%rbp\n",
		symprefix, fn->name
	);
	fs = framesz(fn);
	if (fs)
		fprintf(f, "\tsub $%d, %%rsp\n", fs);
	if (fn->vararg) {
		o = -176;
		for (r=rsave; r-rsave<6; ++r, o+=8)
			fprintf(f, "\tmovq %%%s, %d(%%rbp)\n", rname[*r][0], o);
		for (n=0; n<8; ++n, o+=16)
			fprintf(f, "\tmovaps %%xmm%d, %d(%%rbp)\n", n, o);
	}
	for (r=rclob; r-rclob < NRClob; r++)
		if (fn->reg & BIT(*r)) {
			itmp.arg[0] = TMP(*r);
			emitf("pushq %L0", &itmp, fn, f);
		}

	for (lbl=0, b=fn->start; b; b=b->link) {
		if (lbl || b->npred > 1)
			fprintf(f, "%sbb%d:\n", locprefix, id0+b->id);
		for (i=b->ins; i!=&b->ins[b->nins]; i++)
			emitins(*i, fn, f);
		lbl = 1;
		switch (b->jmp.type) {
		case Jret0:
			for (r=&rclob[NRClob]; r>rclob;)
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
					locprefix, id0+b->s1->id);
			else
				lbl = 0;
			break;
		default:
			c = b->jmp.type - Jxjc;
			if (0 <= c && c <= NXICmp) {
				if (b->link == b->s2) {
					s = b->s1;
					b->s1 = b->s2;
					b->s2 = s;
				} else
					c = cneg(c);
				fprintf(f, "\tj%s %sbb%d\n", ctoa[c],
					locprefix, id0+b->s2->id);
				goto Jmp;
			}
			die("unhandled jump %d", b->jmp.type);
		}
	}
	id0 += fn->nblk;
}

void
emitdat(Dat *d, FILE *f)
{
	static int align;
	static char *dtoa[] = {
		[DAlign] = ".align",
		[DB] = "\t.byte",
		[DH] = "\t.value",
		[DW] = "\t.long",
		[DL] = "\t.quad"
	};

	switch (d->type) {
	case DStart:
		align = 0;
		fprintf(f, ".data\n");
		break;
	case DEnd:
		break;
	case DName:
		if (!align)
			fprintf(f, ".align 8\n");
		if (d->export)
			fprintf(f, ".globl %s%s\n", symprefix, d->u.str);
		fprintf(f, "%s%s:\n", symprefix, d->u.str);
		break;
	case DZ:
		fprintf(f, "\t.fill %"PRId64",1,0\n", d->u.num);
		break;
	default:
		if (d->type == DAlign)
			align = 1;

		if (d->isstr) {
			if (d->type != DB)
				err("strings only supported for 'b' currently");
			fprintf(f, "\t.ascii \"%s\"\n", d->u.str);
		}
		else if (d->isref) {
			fprintf(f, "%s %s%+"PRId64"\n",
				dtoa[d->type], d->u.ref.nam,
				d->u.ref.off);
		}
		else {
			fprintf(f, "%s %"PRId64"\n",
				dtoa[d->type], d->u.num);
		}
		break;
	}
}

typedef struct FBits FBits;

struct FBits {
	union {
		int64_t n;
		float f;
		double d;
	} bits;
	int wide;
	FBits *link;
};

static FBits *stash;

int
stashfp(int64_t n, int w)
{
	FBits **pb, *b;
	int i;

	/* does a dumb de-dup of fp constants
	 * this should be the linker's job */
	for (pb=&stash, i=0; (b=*pb); pb=&b->link, i++)
		if (n == b->bits.n && w == b->wide)
			return i;
	b = emalloc(sizeof *b);
	b->bits.n = n;
	b->wide = w;
	b->link = 0;
	*pb = b;
	return i;
}

void
emitfin(FILE *f)
{
	FBits *b;
	int i;

	if (!stash)
		return;
	fprintf(f, "/* floating point constants */\n");
	fprintf(f, ".data\n.align 8\n");
	for (b=stash, i=0; b; b=b->link, i++)
		if (b->wide)
			fprintf(f,
				"%sfp%d:\n"
				"\t.quad %"PRId64
				" /* %f */\n",
				locprefix, i, b->bits.n,
				b->bits.d
			);
	for (b=stash, i=0; b; b=b->link, i++)
		if (!b->wide)
			fprintf(f,
				"%sfp%d:\n"
				"\t.long %"PRId64
				" /* %lf */\n",
				locprefix, i, b->bits.n & 0xffffffff,
				b->bits.f
			);
	while ((b=stash)) {
		stash = b->link;
		free(b);
	}
}
