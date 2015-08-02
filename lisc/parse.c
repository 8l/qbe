/* really crude parser
 */
#include "lisc.h"
#include <ctype.h>

enum {
	NSym = 256,
	NCons = 256,
};

Ins insb[NIns], *curi;

OpDesc opdesc[OLast] = {
	/*            NAME  ARTY  C */
	[OAdd]    = { "add",   2, T },
	[OSub]    = { "sub",   2, F },
	[ODiv]    = { "div",   2, U },
	[ORem]    = { "rem",   2, U },
	[OStore]  = { "store", 2, U },
	[OLoad]   = { "load",  1, U },
	[ONop]    = { "nop",   0, U },
	[OCopy]   = { "copy",  1, U },
	[OSwap]   = { "swap",  2, T },
	[OSign]   = { "sign",  1, U },
	[OXDiv]   = { "xdiv",  1, U },
};

typedef enum {
	PXXX,
	PLbl,
	PPhi,
	PIns,
	PEnd,
} PState;

typedef enum {
	TXXX,
	TCopy,
	TAdd,
	TSub,
	TDiv,
	TRem,
	TPhi,
	TJmp,
	TJez,
	TRet,
	TW,
	TL,

	TNum,
	TVar,
	TLbl,
	TAddr,
	TEq,
	TComma,
	TLParen,
	TRParen,
	TNL,
	TEOF,
} Token;


static FILE *inf;
static Token thead;
static struct {
	int64_t num;
	char *str;
} tokval;
static int lnum;

static Sym sym[NSym];
static Cons cons[NCons];
static int nsym;
static int ncons;
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

static Token
lex()
{
	static struct {
		char *str;
		Token tok;
	} tmap[] = {
		{ "copy", TCopy },
		{ "add", TAdd },
		{ "sub", TSub },
		{ "div", TDiv },
		{ "rem", TRem },
		{ "phi", TPhi },
		{ "jmp", TJmp },
		{ "jez", TJez },
		{ "ret", TRet },
		{ "w", TW },
		{ "l", TL },
		{ 0, TXXX }
	};
	static char tok[NString];
	int c, i, sgn;
	Token t;

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
		t = TVar;
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
	for (i=0; tmap[i].str; i++)
		if (strcmp(tok, tmap[i].str) == 0)
			return tmap[i].tok;
	err("unknown keyword");
	return -1;
}

static Token
peek()
{
	if (thead == TXXX)
		thead = lex();
	return thead;
}

static Token
next()
{
	Token t;

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
varref(char *v)
{
	int s;

	for (s=0; s<nsym; s++)
		if (strcmp(v, sym[s].name) == 0)
			return SYM(s);
	if (nsym++ >= NSym)
		err("too many symbols");
	strcpy(sym[s].name, v);
	return SYM(s);
}

static Ref
parseref()
{
	Cons c;
	int i;

	switch (next()) {
	case TVar:
		return varref(tokval.str);
	case TNum:
		c = (Cons){.type = CNum, .val = tokval.num};
		strcpy(c.label, "");
	if (0) {
	case TAddr:
		c = (Cons){.type = CAddr, .val = 0};
		strcpy(c.label, tokval.str);
	}
		for (i=0; i<ncons; i++)
			if (cons[i].type == c.type
			&& cons[i].val == c.val
			&& strcmp(cons[i].label, c.label) == 0)
				return CONS(i);
		if (ncons++ >= NCons)
			err("too many constants");
		cons[i] = c;
		return CONS(i);
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
expect(Token t)
{
	static char *names[] = {
		[TLbl] = "label",
		[TComma] = "comma",
		[TEq] = "=",
		[TNL] = "newline",
		[TEOF] = 0,
	};
	char buf[128], *s1, *s2;
	Token t1;

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
	Token t;
	Blk *b;
	int op, i;

	do
		t = next();
	while (t == TNL);
	if (ps == PLbl && t != TLbl && t != TEOF)
		err("label or end of file expected");
	switch (t) {
	default:
		err("label, instruction or jump expected");
	case TEOF:
		return PEnd;
	case TVar:
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
	case TJez:
		curb->jmp.type = JJez;
		r = parseref();
		if (req(r, R))
			err("invalid argument for jez jump");
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
	r = varref(tokval.str);
	expect(TEq);
	switch (next()) {
	case TW:
		sym[r.val].class = CWord;
		break;
	case TL:
		sym[r.val].class = CLong;
		break;
	default:
		err("class expected after =");
	}
	switch (next()) {
	case TCopy:
		op = OCopy;
		break;
	case TAdd:
		op = OAdd;
		break;
	case TSub:
		op = OSub;
		break;
	case TDiv:
		op = ODiv;
		break;
	case TRem:
		op = ORem;
		break;
	case TPhi:
		if (ps != PPhi)
			err("unexpected phi instruction");
		op = -1;
		break;
	default:
		err("invalid instruction");
	}
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
	for (i=0; i<NBlk; i++)
		bmap[i] = 0;
	for (i=0; i<NSym; i++)
		sym[i] = (Sym){.name = ""};
	nsym = 0;
	ncons = 0;
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
	fn->sym = alloc(nsym * sizeof sym[0]);
	memcpy(fn->sym, sym, nsym * sizeof sym[0]);
	fn->cons = alloc(ncons * sizeof cons[0]);
	memcpy(fn->cons, cons, ncons * sizeof cons[0]);
	fn->nsym = nsym;
	fn->nblk = nblk;
	fn->rpo = 0;
	return fn;
}

static char *
printref(Ref r, Fn *fn, FILE *f)
{
	static char *ctoa[] = {
		[CXXX] = "?",
		[CWord] = "w",
		[CLong] = "l",
	};

	switch (r.type) {
	case RSym:
		fprintf(f, "%%%s", fn->sym[r.val].name);
		return ctoa[fn->sym[r.val].class];
	case RCons:
		switch (fn->cons[r.val].type) {
		case CAddr:
			fprintf(f, "$%s", fn->cons[r.val].label);
			if (fn->cons[r.val].val)
				fprintf(f, "%+"PRIi64, fn->cons[r.val].val);
			break;
		case CNum:
			fprintf(f, "%"PRIi64, fn->cons[r.val].val);
			break;
		case CUndef:
			diag("printref: invalid constant");
		}
		break;
	case RSlot:
		fprintf(f, "$%d", r.val);
		break;
	case RReg:
		fprintf(f, "???");
		break;
	}
	return "";
}

void
printfn(Fn *fn, FILE *f)
{
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
		case JJez:
			fprintf(f, "\tjez ");
			printref(b->jmp.arg, fn, f);
			fprintf(f, ", @%s, @%s\n", b->s1->name, b->s2->name);
			break;
		}
	}
}
