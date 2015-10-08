/* really crude parser
 */
#include "lisc.h"
#include <ctype.h>

enum {
	NTmp = 256,
	NCon = 256,
};

OpDesc opdesc[NOp] = {
	/*            NAME     NM */
	[OAdd]    = { "add",    2 },
	[OSub]    = { "sub",    2 },
	[ODiv]    = { "div",    2 },
	[ORem]    = { "rem",    2 },
	[OMul]    = { "mul",    2 },
	[OAnd]    = { "and",    2 },
	[OSext]   = { "sext",   1 },
	[OZext]   = { "zext",   1 },
	[OStorel] = { "storel", 0 },
	[OStorew] = { "storew", 0 },
	[OStores] = { "stores", 0 },
	[OStoreb] = { "storeb", 0 },
	[OLoad]   = { "load",   0 },
	[OLoadsh] = { "loadsh", 0 },
	[OLoaduh] = { "loaduh", 0 },
	[OLoadsb] = { "loadsb", 0 },
	[OLoadub] = { "loadub", 0 },
	[OCopy]   = { "copy",   1 },
	[ONop]    = { "nop",    0 },
	[OSwap]   = { "swap",   2 },
	[OSign]   = { "sign",   0 },
	[OXPush]  = { "xpush",  1 },
	[OSAlloc] = { "salloc", 0 },
	[OXDiv]   = { "xdiv",   1 },
	[OXCmp]   = { "xcmp",   1 },
	[OXTest]  = { "xtest",  1 },
	[OAddr]   = { "addr",   0 },
	[OPar]    = { "parn",   0 },
	[OParc]   = { "parc",   0 },
	[OArg]    = { "arg",    0 },
	[OArgc]   = { "argc",   0 },
	[OCall]   = { "call",   0 },
	[OAlloc]   = { "alloc4",  1 },
	[OAlloc+1] = { "alloc8",  1 },
	[OAlloc+2] = { "alloc16", 1 },

#define X(c) \
	[OCmp+C##c]  = { "c"    #c, 0 }, \
	[OXSet+C##c] = { "xset" #c, 0 },
	CMPS(X)
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
	TCall,
	TPhi,
	TJmp,
	TJnz,
	TRet,
	TFunc,
	TType,
	TData,
	TAlign,
	TL,
	TW,
	TH,
	TB,
	TD,
	TS,

	TNum,
	TTmp,
	TLbl,
	TGlo,
	TTyp,
	TStr,
	TEq,
	TComma,
	TLParen,
	TRParen,
	TLBrace,
	TRBrace,
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
static int rcls;
static int ntyp;


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
		{ "call", TCall },
		{ "phi", TPhi },
		{ "jmp", TJmp },
		{ "jnz", TJnz },
		{ "ret", TRet },
		{ "function", TFunc },
		{ "type", TType },
		{ "data", TData },
		{ "align", TAlign },
		{ "l", TL },
		{ "w", TW },
		{ "h", TS },
		{ "b", TB },
		{ "d", TD },
		{ "s", TS },
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
	case '{':
		return TLBrace;
	case '}':
		return TRBrace;
	case '=':
		return TEq;
	case '%':
		t = TTmp;
		goto Alpha;
	case '@':
		t = TLbl;
		goto Alpha;
	case '$':
		t = TGlo;
		goto Alpha;
	case ':':
		t = TTyp;
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
	if (c == '"') {
		tokval.str = valloc(0, 1);
		for (i=0;; i++) {
			c = fgetc(inf);
			if (c == '"')
			if (!i || tokval.str[i-1] != '\\')
				return TStr;
			vgrow(&tokval.str, i+1);
			tokval.str[i] = c;
		}
	}
	t = TXXX;
	if (0)
Alpha:		c = fgetc(inf);
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

static int
nextnl()
{
	int t;

	while ((t = next()) == TNL)
		;
	return t;
}

static void
expect(int t)
{
	static char *ttoa[] = {
		[TLbl] = "label",
		[TComma] = ",",
		[TEq] = "=",
		[TNL] = "newline",
		[TLParen] = "(",
		[TRParen] = ")",
		[TLBrace] = "{",
		[TRBrace] = "}",
		[TEOF] = 0,
	};
	char buf[128], *s1, *s2;
	int t1;

	t1 = next();
	if (t == t1)
		return;
	s1 = ttoa[t] ? ttoa[t] : "??";
	s2 = ttoa[t1] ? ttoa[t1] : "??";
	snprintf(buf, sizeof buf,
		"%s expected (got %s instead)", s1, s2);
	err(buf);
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
	case TGlo:
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

static int
parsecls(int *tyn)
{
	int i;

	switch (next()) {
	default:
		err("invalid class specifier");
	case TTyp:
		for (i=0; i<ntyp; i++)
			if (strcmp(tokval.str, typ[i].name) == 0) {
				*tyn = i;
				return 2;
			}
		err("undefined type");
	case TW:
		return 0;
	case TL:
		return 1;
	}
}

static void
parserefl(int arg)
{
	int w, t, ty;
	Ref r;

	expect(TLParen);
	if (peek() == TRParen) {
		next();
		return;
	}
	for (;;) {
		if (curi - insb >= NIns)
			err("too many instructions (1)");
		w = parsecls(&ty);
		r = parseref();
		if (req(r, R))
			err("invalid reference argument");
		if (!arg && rtype(r) != RTmp)
			err("invalid function parameter");
		if (w == 2)
			if (arg)
				*curi = (Ins){OArgc, 0, R, {TYP(ty), r}};
			else
				*curi = (Ins){OParc, 0, r, {TYP(ty)}};
		else
			if (arg)
				*curi = (Ins){OArg, w, R, {r}};
			else
				*curi = (Ins){OPar, w, r, {R}};
		curi++;
		t = next();
		if (t == TRParen)
			break;
		if (t != TComma)
			err(", or ) expected");
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
		bmap[i] = balloc();
		nblk++;
		strcpy(bmap[i]->name, name);
	}
	return bmap[i];
}

static void
closeblk()
{
	curb->nins = curi - insb;
	idup(&curb->ins, insb, curb->nins);
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
	int t, op, i, w, ty;

	t = nextnl();
	if (ps == PLbl && t != TLbl && t != TRBrace)
		err("label or } expected");
	switch (t) {
	default:
		if (OStorel <= t && t <= OStoreb) {
			/* operations without result */
			r = R;
			w = 0;
			op = t;
			goto DoOp;
		}
		err("label, instruction or jump expected");
	case TRBrace:
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
		curb->jmp.type = (int[]){
			JRetw, JRetl,
			JRetc, JRet0
		}[rcls];
		if (rcls < 3) {
			r = parseref();
			if (req(r, R))
				err("return value expected");
			curb->jmp.arg = r;
		}
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
	w = parsecls(&ty);
	op = next();
DoOp:
	if (op == TPhi) {
		if (ps != PPhi)
			err("unexpected phi instruction");
		op = -1;
	}
	if (op == TCall) {
		arg[0] = parseref();
		parserefl(1);
		expect(TNL);
		op = OCall;
		if (w == 2) {
			w = 0;
			arg[1] = TYP(ty);
		} else
			arg[1] = R;
		goto Ins;
	}
	if (w == 2)
		err("size class must be w or l");
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
				err(", or end of line expected");
			next();
		}
	next();
	if (op != -1) {
	Ins:
		if (curi - insb >= NIns)
			err("too many instructions (2)");
		curi->op = op;
		curi->wide = w;
		curi->to = r;
		curi->arg[0] = arg[0];
		curi->arg[1] = arg[1];
		curi++;
		return PIns;
	} else {
		phi = alloc(sizeof *phi);
		phi->to = r;
		phi->wide = w;
		memcpy(phi->arg, arg, i * sizeof arg[0]);
		memcpy(phi->blk, blk, i * sizeof blk[0]);
		phi->narg = i;
		*plink = phi;
		plink = &phi->link;
		return PPhi;
	}
}

static Fn *
parsefn()
{
	int i;
	PState ps;
	Fn *fn;

	ntmp = Tmp0;
	ncon = 1; /* first constant must be 0 */
	curb = 0;
	nblk = 0;
	curi = insb;
	fn = alloc(sizeof *fn);
	blink = &fn->start;
	for (i=0; i<NBlk; i++)
		bmap[i] = 0;
	for (i=Tmp0; i<NTmp; i++)
		tmp[i] = (Tmp){.name = ""};
	if (peek() != TGlo)
		rcls = parsecls(&fn->retty);
	else
		rcls = 3;
	if (next() != TGlo)
		err("function name expected");
	strcpy(fn->name, tokval.str);
	parserefl(0);
	if (nextnl() != TLBrace)
		err("function body must start with {");
	ps = PLbl;
	do
		ps = parseline(ps);
	while (ps != PEnd);
	if (!curb)
		err("empty file");
	if (curb->jmp.type == JXXX)
		err("last block misses jump");
	fn->tmp = valloc(ntmp, sizeof tmp[0]);
	memcpy(fn->tmp, tmp, ntmp * sizeof tmp[0]);
	fn->con = valloc(ncon, sizeof con[0]);
	memcpy(fn->con, con, ncon * sizeof con[0]);
	fn->ntmp = ntmp;
	fn->ncon = ncon;
	fn->nblk = nblk;
	fn->rpo = 0;
	return fn;
}

static void
parsetyp()
{
	Typ *ty;
	int t, n, sz, al, s, a, c, flt;

	if (ntyp >= NTyp)
		err("too many type definitions");
	ty = &typ[ntyp++];
	ty->align = -1;
	if (nextnl() != TTyp ||  nextnl() != TEq)
		err("type name, then = expected");
	strcpy(ty->name, tokval.str);
	t = nextnl();
	if (t == TAlign) {
		if (nextnl() != TNum)
			err("alignment expected");
		for (al=0; tokval.num /= 2; al++)
			;
		ty->align = al;
		t = nextnl();
	}
	if (t != TLBrace)
		err("type body must start with {");
	t = nextnl();
	if (t == TNum) {
		ty->dark = 1;
		ty->size = tokval.num;
		if (ty->align == -1)
			err("dark types need alignment");
		t = nextnl();
	} else {
		ty->dark = 0;
		n = -1;
		sz = 0;
		al = 0;
		for (;;) {
			flt = 0;
			switch (t) {
			default: err("invalid size specifier");
			case TD: flt = 1;
			case TL: s = 8; a = 3; break;
			case TS: flt = 1;
			case TW: s = 4; a = 2; break;
			case TH: s = 2; a = 1; break;
			case TB: s = 1; a = 0; break;
			}
			if (a > al)
				al = a;
			if ((a = sz & (s-1))) {
				a = s - a;
				if (++n < NSeg) {
					/* padding segment */
					ty->seg[n].flt = 0;
					ty->seg[n].len = a;
				}
			}
			t = nextnl();
			if (t == TNum) {
				c = tokval.num;
				t = nextnl();
			} else
				c = 1;
			while (c-- > 0) {
				if (++n < NSeg) {
					ty->seg[n].flt = flt;
					ty->seg[n].len = s;
				}
				sz += a + s;
			}
			if (t != TComma)
				break;
			t = nextnl();
		}
		if (++n >= NSeg)
			ty->dark = 1;
		else
			ty->seg[n].len = 0;
		if (ty->align == -1)
			ty->align = al;
		else
			al = ty->align;
		a = (1 << al) - 1;
		ty->size = (sz + a) & ~a;
	}
	if (t != TRBrace)
		err("expected closing }");
}

static void
parsedat(void cb(Dat *))
{
	int t;
	Dat d;

	if (nextnl() != TGlo || nextnl() != TEq)
		err("data name, then = expected");
	d.type = DName;
	d.u.str = tokval.str;
	cb(&d);
	t = nextnl();
	if (t == TAlign) {
		if (nextnl() != TNum)
			err("alignment expected");
		d.type = DAlign;
		d.u.num = tokval.num;
		cb(&d);
		t = nextnl();
	}
	if (t == TStr) {
		d.type = DA;
		d.u.str = tokval.str;
		cb(&d);
		return;
	}
	if (t != TLBrace)
		err("data contents must be { .. } or \" .. \"");
	for (;;) {
		switch (nextnl()) {
		case TL: d.type = DL; break;
		case TW: d.type = DW; break;
		case TH: d.type = DH; break;
		case TB: d.type = DB; break;
		}
		if (nextnl() != TNum)
			err("number expected");
		d.u.num = tokval.num;
		cb(&d);
		t = nextnl();
		if (t == TRBrace)
			break;
		if (t != TComma)
			err(", or } expected");
	}
}

Fn *
parse(FILE *f, void data(Dat *))
{
	Fn *fn;

	fn = 0;
	inf = f;
	lnum = 1;
	thead = TXXX;
	ntyp = 0;
	for (;;)
		switch (nextnl()) {
		case TFunc:
			if (fn)
				/* todo, support multiple
				 * functions per file
				 */
				diag("too many functions");
			fn = parsefn();
			break;
		case TType:
			parsetyp();
			break;
		case TData:
			parsedat(data);
			break;
		case TEOF:
			return fn;
		default:
			err("top-level definition expected");
			break;
		}
}

static void
printref(Ref r, Fn *fn, FILE *f)
{
	switch (r.type) {
	case RTmp:
		if (r.val < Tmp0)
			fprintf(f, "R%d", r.val);
		else
			fprintf(f, "%%%s", fn->tmp[r.val].name);
		break;
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
	case RAlt:
		if (r.val & RCallm)
			fprintf(f, "%x", r.val & (RCallm-1));
		else
			fprintf(f, ":%s", typ[r.val].name);
		break;
	}
}

void
printfn(Fn *fn, FILE *f)
{
	static char *jtoa[NJmp] = {
		[JRet0]     = "ret",
		[JRetw]     = "retw",
		[JRetl]     = "retl",
		[JRetc]     = "retc",
		[JJnz]      = "jnz",
	#define X(c) [JXJc+C##c] = "xj" #c,
		CMPS(X)
	#undef X
	};
	static char prcls[NOp] = {
		[OArg] = 1,
		[OSwap] = 1,
		[OXCmp] = 1,
		[OXTest] = 1,
		[OXPush] = 1,
		[OXDiv] = 1,
	};
	Blk *b;
	Phi *p;
	Ins *i;
	uint n;

	fprintf(f, "function $%s() {\n", fn->name);
	for (b=fn->start; b; b=b->link) {
		fprintf(f, "@%s\n", b->name);
		for (p=b->phi; p; p=p->link) {
			fprintf(f, "\t");
			printref(p->to, fn, f);
			fprintf(f, " =%s phi ", p->wide ? "l" : "w");
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
				printref(i->to, fn, f);
				fprintf(f, " =");
				fprintf(f, i->wide ? "l " : "w ");
			}
			assert(opdesc[i->op].name);
			fprintf(f, "%s", opdesc[i->op].name);
			if (req(i->to, R) && prcls[i->op])
				fprintf(f, i->wide ? "l" : "w");
			if (!req(i->arg[0], R)) {
				fprintf(f, " ");
				printref(i->arg[0], fn, f);
			}
			if (!req(i->arg[1], R)) {
				fprintf(f, ", ");
				printref(i->arg[1], fn, f);
			}
			fprintf(f, "\n");
		}
		switch (b->jmp.type) {
		case JRet0:
		case JRetw:
		case JRetl:
		case JRetc:
			fprintf(f, "\t%s", jtoa[b->jmp.type]);
			if (b->jmp.type != JRet0) {
				fprintf(f, " ");
				printref(b->jmp.arg, fn, f);
			}
			fprintf(f, "\n");
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
	fprintf(f, "}\n");
}
