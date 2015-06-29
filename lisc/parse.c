/* A really crude parser. */
#include <ctype.h>
#include <string.h>

#include "lisc.h"

enum {
	MaxRefs = 256,
};

typedef enum Token Token;
typedef enum PState PState;

enum PState { /* Parsing state in a block. */
	PErr,
	PPhi,
	PIns,
	PEnd,
};

enum Token {
	TAdd,
	TSub,
	TDiv,
	TMod,
	TPhi,
	TJmp,
	TCnd,
	TRet,

	TNum,
	TVar,
	TEq,
	TComma,
	TLParen,
	TRParen,
	TNL,
	TEOF,
};


static FILE *inf;
static char *errstr;

static Sym sym[MaxRef];
static Ref nref;
static Blk blk[MaxBlks], *curblk;
static Phi phi[MaxPhis], *curphi;
static Ins ins[MaxInss], *curins;

static struct {
	long long num;
	char *var;
} tokval;
static int lnum;


static void
err(char *s)
{
	if (!s)
		s = errstr;
	assert(s);
	fprintf(stderr, "parse error: %s (line %d)\n", s, lnum);
	exit(1);
}

static Token
token()
{
	static struct {
		char *str;
		Token tok;
	} tmap[] = {
		{ "add", TAdd },
		{ "sub", TSub },
		{ "div", TDiv },
		{ "mod", TMod },
		{ "phi", TPhi },
		{ "jmp", TJmp },
		{ "cnd", TCnd },
		{ "ret", TRet },
		{ 0 },
	};
	static char tok[MaxIdnt];
	int c, i, var, sgn;

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
		ungetc(c, f);
		tokval.num *= sgn;
		return TNum;
	}
	if (c == '%') {
		var = 1;
		c = fgetc(inf);
	} else
		var = 0;
	if (!isalpha(c))
		err("lexing failure");
	i = 0;
	do {
		if (i >= MaxIdnt-1)
			err("identifier too long");
		tok[i++] = c;
		c = fgetc(inf);
	} while (isalpha(c) || isdigit(c));
	tok[i] = 0;
	ungetc(c, f);
	if (var) {
		tokval.var = tok;
		return TVar;
	}
	for (i=0; tmap[i].str; i++)
		if (strcmp(tok, tmap[i].str) == 0)
			return tmap[i].tok;
	err("unknown keyword");
	return -1;
}

static Ref
varref(char *v)
{
	Ref r;

	for (r=Temp0; r<nref; r++)
		if (sym[r].ty == STemp)
		if (strcmp(v, sym[r].stemp.id) == 0)
			return r;
	if (r >= MaxRefs)
		err("too many references");
	sym[r].ty = STemp;
	strcpy(sym[r].stemp.id, v);
	sym[r].stemp.blk = -1;
	return nref++;
}

static Ref
parseref()
{
	Ref r;

	switch (token()) {
	case TVar:
		return varref(tokval.var);
	case TNum:
		/* Add the constant to the symbol table. */
		for (r=Temp0; r<nref; r++)
			if (sym[r].ty == SNum)
			if (sym[r].snum == tokval.num)
				return r;
		if (r >= MaxRefs)
			err("too many references");
		sym[r].ty = SNum;
		sym[r].snum = tokval.num;
		retunr nref++;
	default:
		errstr = "number or variable expected";
		return R;
	}
}

static PState
parseline(PState ps)
{
	Ref args[MaxPreds];
	Ref r;
	Token t;
	int na;

	t = token();
	switch (t) {
	default:
		errstr = "variable or jump expected";
		return PErr;
	case TVar:
		break;
	case TRet:
		curblk->jmp.ty = JRet;
		goto Jump;
	case TJmp:
		curblk->jmp.ty = JJmp;
		goto Jump;
	case TCnd:
		curblk->jmp.ty = JCnd;
		r = parseref();
		if (r == R) {
			errstr = "invalid argument for cnd";
			return PErr;
		}
		if (token() != TComma) {
			errstr = "missing comma";
			return PErr;
		}
		curblk->jmp.arg = r;
	Jump:
		if (
		return PEnd;
	}
	r = varref(tokval.var);
	if (token() != TEq) {
		errstr = "= expected after variable";
		return PErr;
	}
	switch (token()) {
	case TAdd:
		curins->op = OAdd;
		break;
	case TSub:
		curins->op = OSub;
		break;
	case TDiv:
		curins->op = ODiv;
		break;
	case TMod:
		curins->op = OMod;
		break;
	case TPhi:
		return PIns;
	default:
		errstr = "invalid instruction";
		return PErr;
	}
	na = 0;
	for (;;) {
		x
	}
}






// in main parsing routine, reset lnum to 1
// also reset curxxx
// also nsym to Temp0
// also sym[0..nsym-1].ty = SReg

#if 0
int main()
{
	char *toknames[] = {
		"TAdd",
		"TSub",
		"TDiv",
		"TMod",
		"TPhi",
		"TJmp",
		"TCnd",
		"TRet",
		"TNum",
		"TVar",
		"TEq",
		"TComma",
		"TLParen",
		"TRParen",
		"TNL",
		"TEOF",
	};
	inf = stdin;
	for (;;)
		printf("%s\n", toknames[token()]);
}
#endif
