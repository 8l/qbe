#include "all.h"

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
	{ OAdd,    Ka, "+add%k %1, %=" },
	{ OSub,    Ka, "-sub%k %1, %=" },
	{ OAnd,    Ki, "+and%k %1, %=" },
	{ OOr,     Ki, "+or%k %1, %=" },
	{ OXor,    Ki, "+xor%k %1, %=" },
	{ OSar,    Ki, "-sar%k %B1, %=" },
	{ OShr,    Ki, "-shr%k %B1, %=" },
	{ OShl,    Ki, "-shl%k %B1, %=" },
	{ OMul,    Ki, "+imul%k %1, %=" },
	{ OMul,    Ks, "+mulss %1, %=" }, /* fixme */
	{ OMul,    Kd, "+mulsd %1, %=" },
	{ ODiv,    Ka, "-div%k %1, %=" },
	{ OStorel, Ka, "movq %L0, %M1" },
	{ OStorew, Ka, "movl %W0, %M1" },
	{ OStoreh, Ka, "movw %H0, %M1" },
	{ OStoreb, Ka, "movb %B0, %M1" },
	{ OStores, Ka, "movss %S0, %M1" },
	{ OStored, Ka, "movsd %D0, %M1" },
	{ OLoad,   Ka, "mov%k %M0, %=" },
	{ OLoadsw, Kl, "movslq %M0, %L=" },
	{ OLoadsw, Kw, "movl %M0, %W=" },
	{ OLoaduw, Ki, "movl %M0, %W=" },
	{ OLoadsh, Ki, "movsw%k %M0, %=" },
	{ OLoaduh, Ki, "movzw%k %M0, %=" },
	{ OLoadsb, Ki, "movsb%k %M0, %=" },
	{ OLoadub, Ki, "movzb%k %M0, %=" },
	{ OExtsw,  Kl, "movslq %W0, %L=" },
	{ OExtuw,  Kl, "movl %W0, %W=" },
	{ OExtsh,  Ki, "movsw%k %H0, %=" },
	{ OExtuh,  Ki, "movzw%k %H0, %=" },
	{ OExtsb,  Ki, "movsb%k %B0, %=" },
	{ OExtub,  Ki, "movzb%k %B0, %=" },

	{ OExts,   Kd, "cvtss2sd %0, %=" },  /* see if factorization is possible */
	{ OTruncd, Ks, "cvttsd2ss %0, %=" },
	{ OFtosi,  Kw, "cvttss2si %0, %=" },
	{ OFtosi,  Kl, "cvttsd2si %0, %=" },
	{ OSitof,  Ks, "cvtsi2ss %W0, %=" },
	{ OSitof,  Kd, "cvtsi2sd %L0, %=" },
	{ OCast,   Ki, "movq %D0, %L=" },
	{ OCast,   Ka, "movq %L0, %D=" },

	{ OAddr,   Ki, "lea%k %M0, %=" },
	{ OSwap,   Ki, "xchg%k %0, %1" },
	{ OSign,   Kl, "cqto" },
	{ OSign,   Kw, "cltd" },
	{ OXDiv,   Ki, "div%k %0" },
	{ OXIDiv,  Ki, "idiv%k %0" },
	{ OXCmp,   Ks, "comiss %S0, %S1" },  /* fixme, Kf */
	{ OXCmp,   Kd, "comisd %D0, %D1" },
	{ OXCmp,   Ki, "cmp%k %0, %1" },
	{ OXTest,  Ki, "test%k %0, %1" },
	{ OXSet+ICeq,  Ki, "setz %B=\n\tmovzb%k %B=, %=" },
	{ OXSet+ICsle, Ki, "setle %B=\n\tmovzb%k %B=, %=" },
	{ OXSet+ICslt, Ki, "setl %B=\n\tmovzb%k %B=, %=" },
	{ OXSet+ICsgt, Ki, "setg %B=\n\tmovzb%k %B=, %=" },
	{ OXSet+ICsge, Ki, "setge %B=\n\tmovzb%k %B=, %=" },
	{ OXSet+ICne,  Ki, "setnz %B=\n\tmovzb%k %B=, %=" },
	{ OXSet+ICXnp, Ki, "setnp %B=\n\tmovsb%k %B=, %=" },
	{ OXSet+ICXp,  Ki, "setp %B=\n\tmovsb%k %B=, %=" },
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
	struct { int i:14; } x;

	/* sign extend s using a bitfield */
	x.i = s;
	assert(NAlign == 3);
	if (x.i < 0)
		return -4 * x.i;
	else {
		assert(fn->slot >= x.i);
		return -4 * (fn->slot - x.i);
	}
}

static void
emitcon(Con *con, FILE *f)
{
	switch (con->type) {
	default:
		diag("emit: invalid constant");
	case CAddr:
		fputs(con->label, f);
		if (con->bits.i)
			fprintf(f, "%+"PRId64, con->bits.i);
		break;
	case CBits:
		fprintf(f, "%"PRId64, con->bits.i);
		break;
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
	default:
		diag("emit: 0, 1, = expected in format");
	case '0':
		return i->arg[0];
	case '1':
		return i->arg[1];
	case '=':
		return i->to;
	}
}

static void emitins(Ins, Fn *, FILE *);

static void
emitcopy(Ref r1, Ref r2, int k, Fn *fn, FILE *f)
{
	Ins icp;

	icp.op = OCopy;
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
		if (req(i->arg[1], i->to) && !req(i->arg[0], i->to))
			diag("emit: cannot convert to 2-address");
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
	default:
		diag("emit: invalid escape");
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
		/* fall through */
	case 'D':
	case 'S':
	Ref:
		c = *s++;
		ref = getarg(c, i);
		switch (rtype(ref)) {
		default:
			diag("emit: invalid reference");
		case RTmp:
			assert(isreg(ref));
			fprintf(f, "%%%s", regtoa(ref.val, sz));
			break;
		case RSlot:
			fprintf(f, "%d(%%rbp)", slot(ref.val, fn));
			break;
		case RAMem:
		Mem:
			m = &fn->mem[ref.val & AMask];
			if (rtype(m->base) == RSlot) {
				off.type = CBits;
				off.bits.i = slot(m->base.val, fn);
				addcon(&m->offset, &off);
				m->base = TMP(RBP);
			}
			if (m->offset.type != CUndef)
				emitcon(&m->offset, f);
			if (req(m->base, R) && req(m->index, R))
				break;
			fputc('(', f);
			if (!req(m->base, R))
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
		default:
			diag("emit: invalid memory reference");
		case RAMem:
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
		}
		break;
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
				diag("emit: no entry found for instruction");
			if (omap[o].op == i.op)
			if (omap[o].cls == i.cls
			|| (omap[o].cls == Ki && KBASE(i.cls) == 0)
			|| (omap[o].cls == Ka))
				break;
		}
		emitf(omap[o].asm, &i, fn, f);
		break;
	case ONop:
		/* just do nothing for nops, they are inserted
		 * by some passes */
		break;
	case OMul:
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
	case OSub:
		/* we have to use the negation trick to handle
		 * some 3-address substractions */
		if (req(i.to, i.arg[1])) {
			emitf("neg%k %=", &i, fn, f);
			emitf("add%k %0, %=", &i, fn, f);
			break;
		}
		goto Table;
	case OCopy:
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
		} else if (!req(i.arg[0], i.to))
			emitf("mov%k %0, %=", &i, fn, f);
		break;
	case OCall:
		/* calls simply have a weird syntax in AT&T
		 * assembly... */
		switch (rtype(i.arg[0])) {
		default:
			diag("emit: invalid call instruction");
		case RCon:
			fprintf(f, "\tcallq ");
			emitcon(&fn->con[i.arg[0].val], f);
			fprintf(f, "\n");
			break;
		case RTmp:
			emitf("callq *%L0", &i, fn, f);
			break;
		}
		break;
	case OSAlloc:
		/* there is no good reason why this is here
		 * maybe we should split OSAlloc in 2 different
		 * instructions depending on the result
		 */
		emitf("subq %L0, %%rsp", &i, fn, f);
		if (!req(i.to, R))
			emitcopy(i.to, TMP(RSP), Kl, fn, f);
		break;
	case OSwap:
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
	default:   diag("emit: cneg() unhandled comparison");
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
	case ICXnp: return ICXp;
	case ICXp:  return ICXnp;
	}
}

static int
framesz(Fn *fn)
{
	int i, o, f;

	assert(NAlign == 3);
	for (i=0, o=0; i<NRClob; i++)
		o ^= 1 & (fn->reg >> rclob[i]);
	f = fn->slot;
	f = (f + 3) & -4;
	return 4*f + 8*o;
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
		[ICXnp] = "np",
		[ICXp]  = "p"
	};
	Blk *b, *s;
	Ins *i, itmp;
	int *r, c, fs;

	fprintf(f,
		".text\n"
		".globl %s\n"
		".type %s, @function\n"
		"%s:\n"
		"\tpush %%rbp\n"
		"\tmov %%rsp, %%rbp\n",
		fn->name, fn->name, fn->name
	);
	fs = framesz(fn);
	if (fs)
		fprintf(f, "\tsub $%d, %%rsp\n", fs);
	for (r=rclob; r-rclob < NRClob; r++)
		if (fn->reg & BIT(*r)) {
			itmp.arg[0] = TMP(*r);
			emitf("pushq %L0", &itmp, fn, f);
		}

	for (b=fn->start; b; b=b->link) {
		fprintf(f, ".L%s:\n", b->name);
		for (i=b->ins; i!=&b->ins[b->nins]; i++)
			emitins(*i, fn, f);
		switch (b->jmp.type) {
		case JRet0:
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
		case JJmp:
			if (b->s1 != b->link)
				fprintf(f, "\tjmp .L%s\n", b->s1->name);
			break;
		default:
			c = b->jmp.type - JXJc;
			if (0 <= c && c <= NXICmp) {
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
		fprintf(f,
			".globl %s\n"
			".type %s, @object\n"
			"%s:\n",
			d->u.str, d->u.str, d->u.str
		);
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
	int64_t bits;
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
		if (n == b->bits && w == b->wide)
			return i;
	b = emalloc(sizeof *b);
	b->bits = n;
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
				".Lfp%d:\n"
				"\t.quad %"PRId64
				" /* %f */\n",
				i, b->bits,
				*(double *)&b->bits
			);
	for (b=stash, i=0; b; b=b->link, i++)
		if (!b->wide)
			fprintf(f,
				".Lfp%d:\n"
				"\t.long %"PRId64
				" /* %lf */\n",
				i, b->bits & 0xffffffff,
				*(float *)&b->bits
			);
	while ((b=stash)) {
		stash = b->link;
		free(b);
	}
}
