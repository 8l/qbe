#include "all.h"

typedef struct E E;

struct E {
	FILE *f;
	Fn *fn;
	uint64_t frame;
	uint padding;
};

#define CMP(X) \
	X(Cieq,       "eq") \
	X(Cine,       "ne") \
	X(Cisge,      "ge") \
	X(Cisgt,      "gt") \
	X(Cisle,      "le") \
	X(Cislt,      "lt") \
	X(Ciuge,      "cs") \
	X(Ciugt,      "hi") \
	X(Ciule,      "ls") \
	X(Ciult,      "cc") \
	X(NCmpI+Cfeq, "eq") \
	X(NCmpI+Cfge, "ge") \
	X(NCmpI+Cfgt, "gt") \
	X(NCmpI+Cfle, "ls") \
	X(NCmpI+Cflt, "mi") \
	X(NCmpI+Cfne, "ne") \
	X(NCmpI+Cfo,  "vc") \
	X(NCmpI+Cfuo, "vs")

enum {
	Ki = -1, /* matches Kw and Kl */
	Ka = -2, /* matches all classes */
};

static struct {
	short op;
	short cls;
	char *asm;
} omap[] = {
	{ Oadd,    Ki, "add %=, %0, %1" },
	{ Oadd,    Ka, "fadd %=, %0, %1" },
	{ Osub,    Ki, "sub %=, %0, %1" },
	{ Osub,    Ka, "fsub %=, %0, %1" },
	{ Oand,    Ki, "and %=, %0, %1" },
	{ Oor,     Ki, "orr %=, %0, %1" },
	{ Oxor,    Ki, "eor %=, %0, %1" },
	{ Osar,    Ki, "asr %=, %0, %1" },
	{ Oshr,    Ki, "lsr %=, %0, %1" },
	{ Oshl,    Ki, "lsl %=, %0, %1" },
	{ Omul,    Ki, "mul %=, %0, %1" },
	{ Omul,    Ka, "fmul %=, %0, %1" },
	{ Odiv,    Ki, "sdiv %=, %0, %1" },
	{ Odiv,    Ka, "fdiv %=, %0, %1" },
	{ Oudiv,   Ki, "udiv %=, %0, %1" },
	{ Orem,    Ki, "sdiv %?, %0, %1\n\tmsub\t%=, %?, %1, %0" },
	{ Ourem,   Ki, "udiv %?, %0, %1\n\tmsub\t%=, %?, %1, %0" },
	{ Ocopy,   Ki, "mov %=, %0" },
	{ Ocopy,   Ka, "fmov %=, %0" },
	{ Oswap,   Ki, "mov %?, %0\n\tmov\t%0, %1\n\tmov\t%1, %?" },
	{ Oswap,   Ka, "fmov %?, %0\n\tfmov\t%0, %1\n\tfmov\t%1, %?" },
	{ Ostoreb, Kw, "strb %W0, %M1" },
	{ Ostoreh, Kw, "strh %W0, %M1" },
	{ Ostorew, Kw, "str %W0, %M1" },
	{ Ostorel, Kw, "str %L0, %M1" },
	{ Ostores, Kw, "str %S0, %M1" },
	{ Ostored, Kw, "str %D0, %M1" },
	{ Oloadsb, Ki, "ldrsb %=, %M0" },
	{ Oloadub, Ki, "ldrb %W=, %M0" },
	{ Oloadsh, Ki, "ldrsh %=, %M0" },
	{ Oloaduh, Ki, "ldrh %W=, %M0" },
	{ Oloadsw, Kw, "ldr %=, %M0" },
	{ Oloadsw, Kl, "ldrsw %=, %M0" },
	{ Oloaduw, Ki, "ldr %W=, %M0" },
	{ Oload,   Ka, "ldr %=, %M0" },
	{ Oextsb,  Ki, "sxtb %=, %W0" },
	{ Oextub,  Ki, "uxtb %W=, %W0" },
	{ Oextsh,  Ki, "sxth %=, %W0" },
	{ Oextuh,  Ki, "uxth %W=, %W0" },
	{ Oextsw,  Ki, "sxtw %L=, %W0" },
	{ Oextuw,  Ki, "mov %W=, %W0" },
	{ Oexts,   Kd, "fcvt %=, %S0" },
	{ Otruncd, Ks, "fcvt %=, %D0" },
	{ Ocast,   Kw, "fmov %=, %S0" },
	{ Ocast,   Kl, "fmov %=, %D0" },
	{ Ocast,   Ks, "fmov %=, %W0" },
	{ Ocast,   Kd, "fmov %=, %L0" },
	{ Ostosi,  Ka, "fcvtzs %=, %S0" },
	{ Odtosi,  Ka, "fcvtzs %=, %D0" },
	{ Oswtof,  Ka, "scvtf %=, %W0" },
	{ Osltof,  Ka, "scvtf %=, %L0" },
	{ Ocall,   Kw, "blr %L0" },

	{ Oacmp,   Ki, "cmp %0, %1" },
	{ Oacmn,   Ki, "cmn %0, %1" },
	{ Oafcmp,  Ka, "fcmpe %0, %1" },

#define X(c, str) \
	{ Oflag+c, Ki, "cset %=, " str },
	CMP(X)
#undef X
	{ NOp, 0, 0 }
};

static char *
rname(int r, int k)
{
	static char buf[4];

	if (r == SP) {
		assert(k == Kl);
		sprintf(buf, "sp");
	}
	else if (R0 <= r && r <= LR)
		switch (k) {
		default: die("invalid class");
		case Kw: sprintf(buf, "w%d", r-R0); break;
		case Kx:
		case Kl: sprintf(buf, "x%d", r-R0); break;
		}
	else if (V0 <= r && r <= V30)
		switch (k) {
		default: die("invalid class");
		case Ks: sprintf(buf, "s%d", r-V0); break;
		case Kx:
		case Kd: sprintf(buf, "d%d", r-V0); break;
		}
	else
		die("invalid register");
	return buf;
}

static uint64_t
slot(int s, E *e)
{
	s = ((int32_t)s << 3) >> 3;
	if (s == -1)
		return 16 + e->frame;
	if (s < 0) {
		if (e->fn->vararg)
			return 16 + e->frame + 192 - (s+2)*8;
		else
			return 16 + e->frame - (s+2)*8;
	} else
		return 16 + e->padding + 4 * s;
}

static void
emitf(char *s, Ins *i, E *e)
{
	Ref r;
	int k, c;
	Con *pc;
	unsigned n, sp;

	fputc('\t', e->f);

	sp = 0;
	for (;;) {
		k = i->cls;
		while ((c = *s++) != '%')
			if (c == ' ' && !sp) {
				fputc('\t', e->f);
				sp = 1;
			} else if ( !c) {
				fputc('\n', e->f);
				return;
			} else
				fputc(c, e->f);
	Switch:
		switch ((c = *s++)) {
		default:
			die("invalid escape");
		case 'W':
			k = Kw;
			goto Switch;
		case 'L':
			k = Kl;
			goto Switch;
		case 'S':
			k = Ks;
			goto Switch;
		case 'D':
			k = Kd;
			goto Switch;
		case '?':
			if (KBASE(k) == 0)
				fputs(rname(R18, k), e->f);
			else
				fputs(k==Ks ? "s31" : "d31", e->f);
			break;
		case '=':
		case '0':
			r = c == '=' ? i->to : i->arg[0];
			assert(isreg(r));
			fputs(rname(r.val, k), e->f);
			break;
		case '1':
			r = i->arg[1];
			switch (rtype(r)) {
			default:
				die("invalid second argument");
			case RTmp:
				assert(isreg(r));
				fputs(rname(r.val, k), e->f);
				break;
			case RCon:
				pc = &e->fn->con[r.val];
				n = pc->bits.i;
				assert(pc->type == CBits);
				if (n & 0xfff000)
					fprintf(e->f, "#%u, lsl #12", n>>12);
				else
					fprintf(e->f, "#%u", n);
				break;
			}
			break;
		case 'M':
			c = *s++;
			assert(c == '0' || c == '1');
			r = i->arg[c - '0'];
			assert(isreg(r) && "TODO emit non reg addresses");
			fprintf(e->f, "[%s]", rname(r.val, Kl));
			break;
		}
	}
}

static void
loadcon(Con *c, int r, int k, FILE *f)
{
	char *rn, *p, off[32];
	int64_t n;
	int w, sh;

	w = KWIDE(k);
	rn = rname(r, k);
	n = c->bits.i;
	if (c->type == CAddr) {
		rn = rname(r, Kl);
		if (n)
			sprintf(off, "+%"PRIi64, n);
		else
			off[0] = 0;
		p = c->local ? ".L" : "";
		fprintf(f, "\tadrp\t%s, %s%s%s\n",
			rn, p, str(c->label), off);
		fprintf(f, "\tadd\t%s, %s, #:lo12:%s%s%s\n",
			rn, rn, p, str(c->label), off);
		return;
	}
	assert(c->type == CBits);
	if (!w)
		n = (int32_t)n;
	if ((n | 0xffff) == -1 || arm64_logimm(n, k)) {
		fprintf(f, "\tmov\t%s, #%"PRIi64"\n", rn, n);
	} else {
		fprintf(f, "\tmov\t%s, #%d\n",
			rn, (int)(n & 0xffff));
		for (sh=16; n>>=16; sh+=16) {
			if ((!w && sh == 32) || sh == 64)
				break;
			fprintf(f, "\tmovk\t%s, #0x%x, lsl #%d\n",
				rn, (unsigned)(n & 0xffff), sh);
		}
	}
}

static void
emitins(Ins *i, E *e)
{
	int o;

	switch (i->op) {
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
					optab[i->op].name, "wlsd"[i->cls]);
			if (omap[o].op == i->op)
			if (omap[o].cls == i->cls || omap[o].cls == Ka
			|| (omap[o].cls == Ki && KBASE(i->cls) == 0))
				break;
		}
		emitf(omap[o].asm, i, e);
		break;
	case Onop:
		break;
	case Ocopy:
		if (req(i->to, i->arg[0]))
			break;
		if (rtype(i->arg[0]) != RCon)
			goto Table;
		loadcon(&e->fn->con[i->arg[0].val], i->to.val, i->cls, e->f);
		break;
	case Oaddr:
		assert(rtype(i->arg[0]) == RSlot);
		fprintf(e->f, "\tadd\t%s, x29, #%"PRIu64"\n",
			rname(i->to.val, Kl), slot(i->arg[0].val, e)
		);
		break;
	}
}

static void
framelayout(E *e)
{
	int *r;
	uint o;
	uint64_t f;

	for (o=0, r=arm64_rclob; *r>=0; r++)
		o += 1 & (e->fn->reg >> *r);
	f = e->fn->slot;
	f = (f + 3) & -4;
	o += o & 1;
	e->padding = 4*(f-e->fn->slot);
	e->frame = 4*f + 8*o;
}

/*

  Stack-frame layout:

  +=============+
  | varargs     |
  |  save area  |
  +-------------+
  | callee-save |  ^
  |  registers  |  |
  +-------------+  |
  |    ...      |  |
  | spill slots |  |
  |    ...      |  | e->frame
  +-------------+  |
  |    ...      |  |
  |   locals    |  |
  |    ...      |  |
  +-------------+  |
  | e->padding  |  v
  +-------------+
  |  saved x29  |
  |  saved x30  |
  +=============+ <- x29

*/

void
arm64_emitfn(Fn *fn, FILE *out)
{
	static char *ctoa[] = {
	#define X(c, s) [c] = s,
		CMP(X)
	#undef X
	};
	static int id0;
	int n, c, lbl, *r;
	uint64_t o;
	Blk *b, *s;
	Ins *i;
	E *e;

	e = &(E){.f = out, .fn = fn};
	framelayout(e);

	fprintf(e->f, ".text\n");
	if (e->fn->export)
		fprintf(e->f, ".globl %s\n", e->fn->name);
	fprintf(e->f, "%s:\n", e->fn->name);

	if (e->fn->vararg) {
		for (n=7; n>=0; n--)
			fprintf(e->f, "\tstr\tq%d, [sp, -16]!\n", n);
		for (n=7; n>=0; n--)
			fprintf(e->f, "\tstr\tx%d, [sp, -8]!\n", n);
	}

	if (e->frame + 16 > 512)
		fprintf(e->f,
			"\tsub\tsp, sp, #%"PRIu64"\n"
			"\tstp\tx29, x30, [sp, -16]!\n",
			e->frame
		);
	else
		fprintf(e->f,
			"\tstp\tx29, x30, [sp, -%"PRIu64"]!\n",
			e->frame + 16
		);
	fputs("\tadd\tx29, sp, 0\n", e->f);
	for (o=e->frame+16, r=arm64_rclob; *r>=0; r++)
		if (e->fn->reg & BIT(*r))
			fprintf(e->f,
				"\tstr\t%s, [sp, %"PRIu64"]\n",
				rname(*r, Kx), o -= 8
			);

	for (lbl=0, b=e->fn->start; b; b=b->link) {
		if (lbl || b->npred > 1)
			fprintf(e->f, ".L%d:\n", id0+b->id);
		for (i=b->ins; i!=&b->ins[b->nins]; i++)
			emitins(i, e);
		lbl = 1;
		switch (b->jmp.type) {
		case Jret0:
			for (o=e->frame+16, r=arm64_rclob; *r>=0; r++)
				if (e->fn->reg & BIT(*r))
					fprintf(e->f,
						"\tldr\t%s, [sp, %"PRIu64"]\n",
						rname(*r, Kx), o -= 8
					);
			o = e->frame + 16;
			if (e->fn->vararg)
				o += 192;
			if (o > 504)
				fprintf(e->f,
					"\tldp\tx29, x30, [sp], 16\n"
					"\tadd\tsp, sp, #%"PRIu64"\n",
					o - 16
				);
			else
				fprintf(e->f,
					"\tldp\tx29, x30, [sp], %"PRIu64"\n",
					o
				);
			fprintf(e->f, "\tret\n");
			break;
		case Jjmp:
		Jmp:
			if (b->s1 != b->link)
				fprintf(e->f, "\tb\t.L%d\n", id0+b->s1->id);
			else
				lbl = 0;
			break;
		default:
			c = b->jmp.type - Jjf;
			if (c < 0 || c > NCmp)
				die("unhandled jump %d", b->jmp.type);
			if (b->link == b->s2) {
				s = b->s1;
				b->s1 = b->s2;
				b->s2 = s;
			} else
				c = cmpneg(c);
			fprintf(e->f, "\tb%s\t.L%d\n", ctoa[c], id0+b->s2->id);
			goto Jmp;
		}
	}
	id0 += e->fn->nblk;
}
