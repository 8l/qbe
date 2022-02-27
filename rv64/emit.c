#include "all.h"

enum {
	Ki = -1, /* matches Kw and Kl */
	Ka = -2, /* matches all classes */
};

static struct {
	short op;
	short cls;
	char *asm;
} omap[] = {
	{ Oadd,    Ki, "add%k %=, %0, %1" },
	{ Oadd,    Ka, "fadd.%k %=, %0, %1" },
	{ Osub,    Ki, "sub%k %=, %0, %1" },
	{ Osub,    Ka, "fsub.%k %=, %0, %1" },
	{ Oneg,    Ki, "neg%k %=, %0" },
	{ Oneg,    Ka, "fneg.%k %=, %0" },
	{ Odiv,    Ki, "div%k %=, %0, %1" },
	{ Odiv,    Ka, "fdiv.%k %=, %0, %1" },
	{ Orem,    Ki, "rem%k %=, %0, %1" },
	{ Orem,    Kl, "rem %=, %0, %1" },
	{ Oudiv,   Ki, "divu%k %=, %0, %1" },
	{ Ourem,   Ki, "remu%k %=, %0, %1" },
	{ Omul,    Ki, "mul%k %=, %0, %1" },
	{ Omul,    Ka, "fmul.%k %=, %0, %1" },
	{ Oand,    Ki, "and %=, %0, %1" },
	{ Oor,     Ki, "or %=, %0, %1" },
	{ Oxor,    Ki, "xor %=, %0, %1" },
	{ Osar,    Ki, "sra%k %=, %0, %1" },
	{ Oshr,    Ki, "srl%k %=, %0, %1" },
	{ Oshl,    Ki, "sll%k %=, %0, %1" },
	{ Ocsltl,  Ki, "slt %=, %0, %1" },
	{ Ocultl,  Ki, "sltu %=, %0, %1" },
	{ Oceqs,   Ki, "feq.s %=, %0, %1" },
	{ Ocges,   Ki, "fge.s %=, %0, %1" },
	{ Ocgts,   Ki, "fgt.s %=, %0, %1" },
	{ Ocles,   Ki, "fle.s %=, %0, %1" },
	{ Oclts,   Ki, "flt.s %=, %0, %1" },
	{ Oceqd,   Ki, "feq.d %=, %0, %1" },
	{ Ocged,   Ki, "fge.d %=, %0, %1" },
	{ Ocgtd,   Ki, "fgt.d %=, %0, %1" },
	{ Ocled,   Ki, "fle.d %=, %0, %1" },
	{ Ocltd,   Ki, "flt.d %=, %0, %1" },
	{ Ostoreb, Kw, "sb %0, %M1" },
	{ Ostoreh, Kw, "sh %0, %M1" },
	{ Ostorew, Kw, "sw %0, %M1" },
	{ Ostorel, Ki, "sd %0, %M1" },
	{ Ostores, Kw, "fsw %0, %M1" },
	{ Ostored, Kw, "fsd %0, %M1" },
	{ Oloadsb, Ki, "lb %=, %M0" },
	{ Oloadub, Ki, "lbu %=, %M0" },
	{ Oloadsh, Ki, "lh %=, %M0" },
	{ Oloaduh, Ki, "lhu %=, %M0" },
	{ Oloadsw, Ki, "lw %=, %M0" },
	/* riscv64 always sign-extends 32-bit
	 * values stored in 64-bit registers
	 */
	{ Oloaduw, Kw, "lw %=, %M0" },
	{ Oloaduw, Kl, "lwu %=, %M0" },
	{ Oload,   Kw, "lw %=, %M0" },
	{ Oload,   Kl, "ld %=, %M0" },
	{ Oload,   Ks, "flw %=, %M0" },
	{ Oload,   Kd, "fld %=, %M0" },
	{ Oextsb,  Ki, "sext.b %=, %0" },
	{ Oextub,  Ki, "zext.b %=, %0" },
	{ Oextsh,  Ki, "sext.h %=, %0" },
	{ Oextuh,  Ki, "zext.h %=, %0" },
	{ Oextsw,  Kl, "sext.w %=, %0" },
	{ Oextuw,  Kl, "zext.w %=, %0" },
	{ Otruncd, Ks, "fcvt.s.d %=, %0" },
	{ Oexts,   Kd, "fcvt.d.s %=, %0" },
	{ Ostosi,  Kw, "fcvt.w.s %=, %0, rtz" },
	{ Ostosi,  Kl, "fcvt.l.s %=, %0, rtz" },
	{ Ostoui,  Kw, "fcvt.wu.s %=, %0, rtz" },
	{ Ostoui,  Kl, "fcvt.lu.s %=, %0, rtz" },
	{ Odtosi,  Kw, "fcvt.w.d %=, %0, rtz" },
	{ Odtosi,  Kl, "fcvt.l.d %=, %0, rtz" },
	{ Odtoui,  Kw, "fcvt.wu.d %=, %0, rtz" },
	{ Odtoui,  Kl, "fcvt.lu.d %=, %0, rtz" },
	{ Oswtof,  Ka, "fcvt.%k.w %=, %0" },
	{ Ouwtof,  Ka, "fcvt.%k.wu %=, %0" },
	{ Osltof,  Ka, "fcvt.%k.l %=, %0" },
	{ Oultof,  Ka, "fcvt.%k.lu %=, %0" },
	{ Ocast,   Kw, "fmv.x.w %=, %0" },
	{ Ocast,   Kl, "fmv.x.d %=, %0" },
	{ Ocast,   Ks, "fmv.w.x %=, %0" },
	{ Ocast,   Kd, "fmv.d.x %=, %0" },
	{ Ocopy,   Ki, "mv %=, %0" },
	{ Ocopy,   Ka, "fmv.%k %=, %0" },
	{ Oswap,   Ki, "mv %?, %0\n\tmv %0, %1\n\tmv %1, %?" },
	{ Oreqz,   Ki, "seqz %=, %0" },
	{ Ornez,   Ki, "snez %=, %0" },
	{ Ocall,   Kw, "jalr %0" },
	{ NOp, 0, 0 }
};

static char *rname[] = {
	[FP] = "fp",
	[SP] = "sp",
	[GP] = "gp",
	[TP] = "tp",
	[RA] = "ra",
	[T6] = "t6",
	[T0] = "t0", "t1", "t2", "t3", "t4", "t5",
	[A0] = "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7",
	[S1] = "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8",
	       "s9", "s10", "s11",
	[FT0] = "ft0", "ft1", "ft2", "ft3", "ft4", "ft5", "ft6", "ft7",
	        "ft8", "ft9", "ft10", "ft11",
	[FA0] = "fa0", "fa1", "fa2", "fa3", "fa4", "fa5", "fa6", "fa7",
	[FS0] = "fs0", "fs1", "fs2", "fs3", "fs4", "fs5", "fs6", "fs7",
	        "fs8", "fs9", "fs10", "fs11",
};

static int64_t
slot(int s, Fn *fn)
{
	s = ((int32_t)s << 3) >> 3;
	assert(s <= fn->slot);
	if (s < 0)
		return 8 * -s;
	else
		return -4 * (fn->slot - s);
}

static void
emitaddr(Con *c, FILE *f)
{
	char off[32], *p;

	if (c->bits.i)
		sprintf(off, "+%"PRIi64, c->bits.i);
	else
		off[0] = 0;
	p = c->local ? ".L" : "";
	fprintf(f, "%s%s%s", p, str(c->label), off);
}

static void
emitf(char *s, Ins *i, Fn *fn, FILE *f)
{
	static char clschr[] = {'w', 'l', 's', 'd'};
	Ref r;
	int k, c;
	Con *pc;
	int64_t offset;

	fputc('\t', f);
	for (;;) {
		k = i->cls;
		while ((c = *s++) != '%')
			if (!c) {
				fputc('\n', f);
				return;
			} else
				fputc(c, f);
		switch ((c = *s++)) {
		default:
			die("invalid escape");
		case '?':
			if (KBASE(k) == 0)
				fputs("t6", f);
			else
				abort();
			break;
		case 'k':
			if (i->cls != Kl)
				fputc(clschr[i->cls], f);
			break;
		case '=':
		case '0':
			r = c == '=' ? i->to : i->arg[0];
			assert(isreg(r));
			fputs(rname[r.val], f);
			break;
		case '1':
			r = i->arg[1];
			switch (rtype(r)) {
			default:
				die("invalid second argument");
			case RTmp:
				assert(isreg(r));
				fputs(rname[r.val], f);
				break;
			case RCon:
				pc = &fn->con[r.val];
				assert(pc->type == CBits);
				assert(pc->bits.i >= -2048 && pc->bits.i < 2048);
				fprintf(f, "%d", (int)pc->bits.i);
				break;
			}
			break;
		case 'M':
			c = *s++;
			assert(c == '0' || c == '1');
			r = i->arg[c - '0'];
			switch (rtype(r)) {
			default:
				die("invalid address argument");
			case RTmp:
				fprintf(f, "0(%s)", rname[r.val]);
				break;
			case RCon:
				pc = &fn->con[r.val];
				assert(pc->type == CAddr);
				emitaddr(pc, f);
				if (isstore(i->op)
				|| (isload(i->op) && KBASE(i->cls) == 1)) {
					/* store (and float load)
					 * pseudo-instructions need a
					 * temporary register in which to
					 * load the address
					 */
					fprintf(f, ", t6");
				}
				break;
			case RSlot:
				offset = slot(r.val, fn);
				assert(offset >= -2048 && offset <= 2047);
				fprintf(f, "%d(fp)", (int)offset);
				break;
			}
			break;
		}
	}
}

static void
loadcon(Con *c, int r, int k, FILE *f)
{
	char *rn;
	int64_t n;
	int w;

	w = KWIDE(k);
	rn = rname[r];
	switch (c->type) {
	case CAddr:
		fprintf(f, "\tla %s, ", rn);
		emitaddr(c, f);
		fputc('\n', f);
		break;
	case CBits:
		n = c->bits.i;
		if (!w)
			n = (int32_t)n;
		fprintf(f, "\tli %s, %"PRIu64"\n", rn, n);
		break;
	default:
		die("invalid constant");
	}
}

static void
fixslot(Ref *pr, Fn *fn, FILE *f)
{
	Ref r;
	int64_t s;

	r = *pr;
	if (rtype(r) == RSlot) {
		s = slot(r.val, fn);
		if (s < -2048 || s > 2047) {
			fprintf(f, "\tli t6, %"PRId64"\n", s);
			fprintf(f, "\tadd t6, fp, t6\n");
			*pr = TMP(T6);
		}
	}
}

static void
emitins(Ins *i, Fn *fn, FILE *f)
{
	int o;
	char *rn;
	int64_t s;
	Con *con;

	switch (i->op) {
	default:
		if (isload(i->op))
			fixslot(&i->arg[0], fn, f);
		else if (isstore(i->op))
			fixslot(&i->arg[1], fn, f);
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
		emitf(omap[o].asm, i, fn, f);
		break;
	case Ocopy:
		if (req(i->to, i->arg[0]))
			break;
		if (rtype(i->to) == RSlot) {
			switch (rtype(i->arg[0])) {
			case RSlot:
			case RCon:
				die("unimplemented");
				break;
			default:
				assert(isreg(i->arg[0]));
				i->arg[1] = i->to;
				i->to = R;
				switch (i->cls) {
				case Kw: i->op = Ostorew; break;
				case Kl: i->op = Ostorel; break;
				case Ks: i->op = Ostores; break;
				case Kd: i->op = Ostored; break;
				}
				fixslot(&i->arg[1], fn, f);
				goto Table;
			}
			break;
		}
		assert(isreg(i->to));
		switch (rtype(i->arg[0])) {
		case RCon:
			loadcon(&fn->con[i->arg[0].val], i->to.val, i->cls, f);
			break;
		case RSlot:
			i->op = Oload;
			fixslot(&i->arg[0], fn, f);
			goto Table;
		default:
			assert(isreg(i->arg[0]));
			goto Table;
		}
		break;
	case Onop:
		break;
	case Oaddr:
		assert(rtype(i->arg[0]) == RSlot);
		rn = rname[i->to.val];
		s = slot(i->arg[0].val, fn);
		if (-s < 2048) {
			fprintf(f, "\tadd %s, fp, %"PRId64"\n", rn, s);
		} else {
			fprintf(f,
				"\tli %s, %"PRId64"\n"
				"\tadd %s, fp, %s\n",
				rn, s, rn, rn
			);
		}
		break;
	case Ocall:
		switch (rtype(i->arg[0])) {
		case RCon:
			con = &fn->con[i->arg[0].val];
			if (con->type != CAddr || con->bits.i)
				goto invalid;
			fprintf(f, "\tcall %s\n", str(con->label));
			break;
		case RTmp:
			emitf("jalr %0", i, fn, f);
			break;
		default:
		invalid:
			die("invalid call argument");
		}
		break;
	case Osalloc:
		emitf("sub sp, sp, %0", i, fn, f);
		if (!req(i->to, R))
			emitf("mv %=, sp", i, fn, f);
		break;
	}
}

/*

  Stack-frame layout:

  +=============+
  | varargs     |
  |  save area  |
  +-------------+
  |  saved ra   |
  |  saved fp   |
  +-------------+ <- fp
  |    ...      |
  | spill slots |
  |    ...      |
  +-------------+
  |    ...      |
  |   locals    |
  |    ...      |
  +-------------+
  |   padding   |
  +-------------+
  | callee-save |
  |  registers  |
  +=============+

*/

void
rv64_emitfn(Fn *fn, FILE *f)
{
	static int id0;
	int lbl, neg, off, frame, *pr, r;
	Blk *b, *s;
	Ins *i;

	gasemitlnk(fn->name, &fn->lnk, ".text", f);

	if (fn->vararg) {
		/* TODO: only need space for registers
		 * unused by named arguments
		 */
		fprintf(f, "\tadd sp, sp, -64\n");
		for (r=A0; r<=A7; r++)
			fprintf(f,
				"\tsd %s, %d(sp)\n",
				rname[r], 8 * (r - A0)
			);
	}
	fprintf(f, "\tsd fp, -16(sp)\n");
	fprintf(f, "\tsd ra, -8(sp)\n");
	fprintf(f, "\tadd fp, sp, -16\n");

	frame = (16 + 4 * fn->slot + 15) & ~15;
	for (pr=rv64_rclob; *pr>=0; pr++) {
		if (fn->reg & BIT(*pr))
			frame += 8;
	}
	frame = (frame + 15) & ~15;

	if (frame <= 2048)
		fprintf(f,
			"\tadd sp, sp, -%d\n",
			frame
		);
	else
		fprintf(f,
			"\tli t6, %d\n"
			"\tsub sp, sp, t6\n",
			frame
		);
	for (pr=rv64_rclob, off=0; *pr>=0; pr++) {
		if (fn->reg & BIT(*pr)) {
			fprintf(f,
				"\t%s %s, %d(sp)\n",
				*pr < FT0 ? "sd" : "fsd",
				rname[*pr], off
			);
			off += 8;
		}
	}

	for (lbl=0, b=fn->start; b; b=b->link) {
		if (lbl || b->npred > 1)
			fprintf(f, ".L%d:\n", id0+b->id);
		for (i=b->ins; i!=&b->ins[b->nins]; i++)
			emitins(i, fn, f);
		lbl = 1;
		switch (b->jmp.type) {
		case Jret0:
			if (fn->dynalloc) {
				if (frame - 16 <= 2048)
					fprintf(f,
						"\tadd sp, fp, -%d\n",
						frame - 16
					);
				else
					fprintf(f,
						"\tli t6, %d\n"
						"\tsub sp, fp, t6\n",
						frame - 16
					);
			}
			for (pr=rv64_rclob, off=0; *pr>=0; pr++) {
				if (fn->reg & BIT(*pr)) {
					fprintf(f,
						"\t%s %s, %d(sp)\n",
						*pr < FT0 ? "ld" : "fld",
						rname[*pr], off
					);
					off += 8;
				}
			}
			fprintf(f,
				"\tadd sp, fp, %d\n"
				"\tld ra, 8(fp)\n"
				"\tld fp, 0(fp)\n"
				"\tret\n",
				16 + fn->vararg * 64
			);
			break;
		case Jjmp:
		Jmp:
			if (b->s1 != b->link)
				fprintf(f, "\tj .L%d\n", id0+b->s1->id);
			else
				lbl = 0;
			break;
		case Jjnz:
			neg = 0;
			if (b->link == b->s2) {
				s = b->s1;
				b->s1 = b->s2;
				b->s2 = s;
				neg = 1;
			}
			assert(isreg(b->jmp.arg));
			fprintf(f,
				"\tb%sz %s, .L%d\n",
				neg ? "ne" : "eq",
				rname[b->jmp.arg.val],
				id0+b->s2->id
			);
			goto Jmp;
		}
	}
	id0 += fn->nblk;
}
