/* really crude parser
 */
#include "lisc.h"
#include <ctype.h>

enum {
	NTmp = 256,
	NCon = 256,
};

Ins insb[NIns], *curi;

OpDesc opdesc[NOp] = {
	/*            NAME   ARTY NM */
	[OAdd]    = { "add",    2, 2 },
	[OSub]    = { "sub",    2, 2 },
	[ODiv]    = { "div",    2, 2 },
	[ORem]    = { "rem",    2, 2 },
	[OAnd]    = { "and",    2, 2 },
	[OStorel] = { "storel", 2, 0 },
	[OStorew] = { "storew", 2, 0 },
	[OStores] = { "stores", 2, 0 },
	[OStoreb] = { "storeb", 2, 0 },
	[OLoad]   = { "load",   1, 0 },
	[OLoadss] = { "loadss", 1, 0 },
	[OLoadus] = { "loadus", 1, 0 },
	[OLoadsb] = { "loadsb", 1, 0 },
	[OLoadub] = { "loadub", 1, 0 },
	[OCopy]   = { "copy",   1, 1 },
	[ONop]    = { "nop",    0, 0 },
	[OSwap]   = { "swap",   2, 2 },
	[OSign]   = { "sign",   1, 0 },
	[OXDiv]   = { "xdiv",   1, 1 },
	[OXCmpw]  = { "xcmpw",  2, 1 },
	[OXCmpl]  = { "xcmpl",  2, 1 },
	[OXTestw] = { "xtestw", 2, 1 },
	[OXTestl] = { "xtestl", 2, 1 },
	[OAlloc]   = { "alloc4",  1, 1 },
	[OAlloc+1] = { "alloc8",  1, 1 },
	[OAlloc+2] = { "alloc16", 1, 1 },

	#define X(c)                        \
	[OCmp+C##c]  = { "c"    #c, 2, 0 }, \
	[OXSet+C##c] = { "xset" #c, 0, 0 }
	X(eq), X(sle), X(slt), X(sgt), X(sge), X(ne),
	#undef X
};

typedef enum {
	PXXX,
	PLbl,
	PPhi,
	PIns,
	PEnd,
} PState;

enum {
	TXXX = NPubOp,
	TPhi,
	TJmp,
	TJnz,
	TRet,
	TW,
	TL,

	TNum,
	TTmp,
	TLbl,
	TAddr,
	TEq,
	TComma,
	TLParen,
	TRParen,
	TNL,
	TEOF,
};


static FILE *inf;
static int thead;
static struct {
	int64_t num;
	char *str;
} tokval;
static int lnum;

static Tmp tmp[NTmp];
static Con con[NCon] = {[0] = {.type = CNum}};
static int ntmp;
static int ncon;
static Phi **plink;
static Blk *bmap[NBlk+1];
static Blk *curb;
static Blk **blink;
static int nblk;


void *
alloc(size_t n)
{
	void *p;

	/* todo, export in util.c */
	if (n == 0)
		return 0;
	p = calloc(1, n);
	if (!p)
		abort();
	return p;
}

void
diag(char *s)
{
	/* todo, export in util.c */
	fputs(s, stderr);
	fputc('\n', stderr);
	abort();
}

static void
err(char *s)
{
	char buf[100];

	snprintf(buf, sizeof buf, "parse: %s (line %d)", s, lnum);
	diag(buf);
}

static int
lex()
{
	static struct {
		char *str;
		int tok;
	} tmap[] = {
		{ "phi", TPhi },
		{ "jmp", TJmp },
		{ "jnz", TJnz },
		{ "ret", TRet },
		{ "w", TW },
		{ "l", TL },
		{ 0, TXXX }
	};
	static char tok[NString];
	int c, i, sgn;
	int t;

	do
		c = fgetc(inf);
	while (isblank(c));
	switch (c) {
	case EOF:
		return TEOF;
	case ',':
		return TComma;
	case '(':
		return TLParen;
	case ')':
		return TRParen;
	case '=':
		return TEq;
	case '%':
		t = TTmp;
		c = fgetc(inf);
		goto Alpha;
	case '@':
		t = TLbl;
		c = fgetc(inf);
		goto Alpha;
	case '$':
		t = TAddr;
		c = fgetc(inf);
		goto Alpha;
	case '#':
		while (fgetc(inf) != '\n')
			;
	case '\n':
		lnum++;
		return TNL;
	}
	if (isdigit(c) || c == '-') {
		if (c == '-') {
			tokval.num = 0;
			sgn = -1;
		} else {
			tokval.num = c - '0';
			sgn = 1;
		}
		for (;;) {
			c = fgetc(inf);
			if (!isdigit(c))
				break;
			tokval.num *= 10;
			tokval.num += c - '0';
		}
		ungetc(c, inf);
		tokval.num *= sgn;
		return TNum;
	}
	t = TXXX;
Alpha:
	if (!isalpha(c))
		err("lexing failure");
	i = 0;
	do {
		if (i >= NString-1)
			err("identifier too long");
		tok[i++] = c;
		c = fgetc(inf);
	} while (isalpha(c) || isdigit(c));
	tok[i] = 0;
	ungetc(c, inf);
	if (t != TXXX) {
		tokval.str = tok;
		return t;
	}
	for (i=0; i<NPubOp; i++)
		if (opdesc[i].name)
		if (strcmp(tok, opdesc[i].name) == 0)
			return i;
	for (i=0; tmap[i].str; i++)
		if (strcmp(tok, tmap[i].str) == 0)
			return tmap[i].tok;
	err("unknown keyword");
	return TXXX;
}

static int
peek()
{
	if (thead == TXXX)
		thead = lex();
	return thead;
}

static int
next()
{
	int t;

	t = peek();
	thead = TXXX;
	return t;
}

Blk *
blocka()
{
	static Blk zblock;
	Blk *b;

	b = alloc(sizeof *b);
	*b = zblock;
	b->id = nblk++;
	return b;
}

static Ref
tmpref(char *v, int use)
{
	int t;

	for (t=Tmp0; t<ntmp; t++)
		if (strcmp(v, tmp[t].name) == 0)
			goto Found;
	if (ntmp++ >= NTmp)
		err("too many temporaries");
	strcpy(tmp[t].name, v);
Found:
	tmp[t].ndef += !use;
	tmp[t].nuse += use;
	return TMP(t);
}

static Ref
parseref()
{
	Con c;
	int i;

	switch (next()) {
	case TTmp:
		return tmpref(tokval.str, 1);
	case TNum:
		c = (Con){.type = CNum, .val = tokval.num};
		strcpy(c.label, "");
	if (0) {
	case TAddr:
		c = (Con){.type = CAddr, .val = 0};
		strcpy(c.label, tokval.str);
	}
		for (i=0; i<ncon; i++)
			if (con[i].type == c.type
			&& con[i].val == c.val
			&& strcmp(con[i].label, c.label) == 0)
				return CON(i);
		if (ncon++ >= NCon)
			err("too many constants");
		con[i] = c;
		return CON(i);
	default:
		return R;
	}
}

static Blk *
findblk(char *name)
{
	int i;

	assert(name[0]);
	for (i=0; i<NBlk; i++)
		if (!bmap[i] || strcmp(bmap[i]->name, name) == 0)
			break;
	if (i == NBlk)
		err("too many blocks");
	if (!bmap[i]) {
		bmap[i] = blocka();
		strcpy(bmap[i]->name, name);
	}
	return bmap[i];
}

static void
expect(int t)
{
	static char *names[] = {
		[TLbl] = "label",
		[TComma] = "comma",
		[TEq] = "=",
		[TNL] = "newline",
		[TEOF] = 0,
	};
	char buf[128], *s1, *s2;
	int t1;

	t1 = next();
	if (t == t1)
		return;
	s1 = names[t] ? names[t] : "??";
	s2 = names[t1] ? names[t1] : "??";
	snprintf(buf, sizeof buf,
		"%s expected (got %s instead)", s1, s2);
	err(buf);
}

static void
closeblk()
{
	curb->nins = curi - insb;
	curb->ins = alloc(curb->nins * sizeof(Ins));
	memcpy(curb->ins, insb, curb->nins * sizeof(Ins));
	blink = &curb->link;
	curi = insb;
}

static PState
parseline(PState ps)
{
	Ref arg[NPred] = {R};
	Blk *blk[NPred];
	Phi *phi;
	Ref r;
	Blk *b;
	int t, op, i;

	do
		t = next();
	while (t == TNL);
	if (ps == PLbl && t != TLbl && t != TEOF)
		err("label or end of file expected");
	switch (t) {
	default:
		if (OStorel <= t && t <= OStoreb) {
			/* operations without result */
			r = R;
			op = t;
			goto DoOp;
		}
		err("label, instruction or jump expected");
	case TEOF:
		return PEnd;
	case TTmp:
		break;
	case TLbl:
		b = findblk(tokval.str);
		if (b->jmp.type != JXXX)
			err("multiple definitions of block");
		if (curb && curb->jmp.type == JXXX) {
			closeblk();
			curb->jmp.type = JJmp;
			curb->s1 = b;
		}
		*blink = b;
		curb = b;
		plink = &curb->phi;
		expect(TNL);
		return PPhi;
	case TRet:
		curb->jmp.type = JRet;
		goto Close;
	case TJmp:
		curb->jmp.type = JJmp;
		goto Jump;
	case TJnz:
		curb->jmp.type = JJnz;
		r = parseref();
		if (req(r, R))
			err("invalid argument for jnz jump");
		curb->jmp.arg = r;
		expect(TComma);
	Jump:
		expect(TLbl);
		curb->s1 = findblk(tokval.str);
		if (curb->jmp.type != JJmp) {
			expect(TComma);
			expect(TLbl);
			curb->s2 = findblk(tokval.str);
		}
	Close:
		expect(TNL);
		closeblk();
		return PLbl;
	}
	r = tmpref(tokval.str, 0);
	expect(TEq);
	switch (next()) {
	case TW:
		tmp[r.val].type = TWord;
		break;
	case TL:
		tmp[r.val].type = TLong;
		break;
	default:
		err("class expected after =");
	}
	op = next();
DoOp:
	if (op == TPhi) {
		if (ps != PPhi)
			err("unexpected phi instruction");
		op = -1;
	}
	if (op >= NPubOp)
		err("invalid instruction");
	i = 0;
	if (peek() != TNL)
		for (;;) {
			if (i == NPred)
				err("too many arguments");
			if (op == -1) {
				expect(TLbl);
				blk[i] = findblk(tokval.str);
			}
			arg[i] = parseref();
			if (req(arg[i], R))
				err("invalid instruction argument");
			i++;
			t = peek();
			if (t == TNL)
				break;
			if (t != TComma)
				err("comma or end of line expected");
			next();
		}
	next();
	if (op != -1 && i != opdesc[op].arity)
		err("invalid arity");
	if (op != -1) {
		if (curi - insb >= NIns)
			err("too many instructions in block");
		curi->op = op;
		curi->to = r;
		curi->arg[0] = arg[0];
		curi->arg[1] = arg[1];
		curi++;
		return PIns;
	} else {
		phi = alloc(sizeof *phi);
		phi->to = r;
		memcpy(phi->arg, arg, i * sizeof arg[0]);
		memcpy(phi->blk, blk, i * sizeof blk[0]);
		phi->narg = i;
		*plink = phi;
		plink = &phi->link;
		return PPhi;
	}
}

Fn *
parsefn(FILE *f)
{
	int i;
	PState ps;
	Fn *fn;

	inf = f;
	thead = TXXX;
	for (i=0; i<NBlk; i++)
		bmap[i] = 0;
	for (i=0; i<NTmp; i++)
		if (i < Tmp0)
			tmp[i] = (Tmp){.type = TReg};
		else
			tmp[i] = (Tmp){.name = ""};
	ntmp = Tmp0;
	ncon = 1; /* first constant must be 0 */
	curi = insb;
	curb = 0;
	lnum = 1;
	nblk = 0;
	fn = alloc(sizeof *fn);
	blink = &fn->start;
	ps = PLbl;
	do
		ps = parseline(ps);
	while (ps != PEnd);
	if (!curb)
		err("empty file");
	if (curb->jmp.type == JXXX)
		err("last block misses jump");
	fn->tmp = alloc(ntmp * sizeof tmp[0]);
	memcpy(fn->tmp, tmp, ntmp * sizeof tmp[0]);
	fn->con = alloc(ncon * sizeof con[0]);
	memcpy(fn->con, con, ncon * sizeof con[0]);
	fn->ntmp = ntmp;
	fn->ncon = ncon;
	fn->nblk = nblk;
	fn->rpo = 0;
	return fn;
}

static char *
printref(Ref r, Fn *fn, FILE *f)
{
	static char *ttoa[] = {
		[TUndef] = "?",
		[TWord] = "w",
		[TLong] = "l",
		[TReg] = "",
	};

	switch (r.type) {
	case RTmp:
		if (r.val < Tmp0)
			fprintf(f, "R%d", r.val);
		else
			fprintf(f, "%%%s", fn->tmp[r.val].name);
		return ttoa[fn->tmp[r.val].type];
	case RCon:
		switch (fn->con[r.val].type) {
		case CAddr:
			fprintf(f, "$%s", fn->con[r.val].label);
			if (fn->con[r.val].val)
				fprintf(f, "%+"PRIi64, fn->con[r.val].val);
			break;
		case CNum:
			fprintf(f, "%"PRIi64, fn->con[r.val].val);
			break;
		case CUndef:
			diag("printref: invalid constant");
		}
		break;
	case RSlot:
		fprintf(f, "S%d", r.val);
		break;
	case RMem:
		fprintf(f, "M%d", r.val);
		break;
	}
	return "";
}

void
printfn(Fn *fn, FILE *f)
{
	static char *jtoa[NJmp] = {
		[JJnz]      = "jnz",
		[JXJc+Ceq]  = "xjeq",
		[JXJc+Csle] = "xjsle",
		[JXJc+Cslt] = "xjslt",
		[JXJc+Csgt] = "xjsgt",
		[JXJc+Csge] = "xjsge",
		[JXJc+Cne]  = "xjne",
	};
	Blk *b;
	Phi *p;
	Ins *i;
	uint n;
	char *cl;

	for (b=fn->start; b; b=b->link) {
		fprintf(f, "@%s\n", b->name);
		for (p=b->phi; p; p=p->link) {
			fprintf(f, "\t");
			cl = printref(p->to, fn, f);
			fprintf(f, " =%s phi ", cl);
			assert(p->narg);
			for (n=0;; n++) {
				fprintf(f, "@%s ", p->blk[n]->name);
				printref(p->arg[n], fn, f);
				if (n == p->narg-1) {
					fprintf(f, "\n");
					break;
				} else
					fprintf(f, ", ");
			}
		}
		for (i=b->ins; i-b->ins < b->nins; i++) {
			fprintf(f, "\t");
			if (!req(i->to, R)) {
				cl = printref(i->to, fn, f);
				fprintf(f, " =%s ", cl);
			}
			assert(opdesc[i->op].name);
			fprintf(f, "%s", opdesc[i->op].name);
			n = opdesc[i->op].arity;
			if (n > 0) {
				fprintf(f, " ");
				printref(i->arg[0], fn, f);
			}
			if (n > 1) {
				fprintf(f, ", ");
				printref(i->arg[1], fn, f);
			}
			fprintf(f, "\n");
		}
		switch (b->jmp.type) {
		case JRet:
			fprintf(f, "\tret\n");
			break;
		case JJmp:
			if (b->s1 != b->link)
				fprintf(f, "\tjmp @%s\n", b->s1->name);
			break;
		default:
			fprintf(f, "\t%s ", jtoa[b->jmp.type]);
			if (b->jmp.type == JJnz) {
				printref(b->jmp.arg, fn, f);
				fprintf(f, ", ");
			}
			fprintf(f, "@%s, @%s\n", b->s1->name, b->s2->name);
			break;
		}
	}
}
