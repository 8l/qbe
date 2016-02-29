#include "lisc.h"
#include <ctype.h>
#include <stdarg.h>

OpDesc opdesc[NOp] = {
	/*            NAME     NM */
	[OAdd]    = { "add",    2 },
	[OSub]    = { "sub",    2 },
	[ODiv]    = { "div",    2 },
	[ORem]    = { "rem",    2 },
	[OMul]    = { "mul",    2 },
	[OAnd]    = { "and",    2 },
	[OStored] = { "stored", 0 },
	[OStores] = { "stores", 0 },
	[OStorel] = { "storel", 0 },
	[OStorew] = { "storew", 0 },
	[OStoreh] = { "storeh", 0 },
	[OStoreb] = { "storeb", 0 },
	[OLoad]   = { "load",   0 },
	[OLoadsw] = { "loadsw", 0 },
	[OLoaduw] = { "loaduw", 0 },
	[OLoadsh] = { "loadsh", 0 },
	[OLoaduh] = { "loaduh", 0 },
	[OLoadsb] = { "loadsb", 0 },
	[OLoadub] = { "loadub", 0 },
	[OExtsw]  = { "extsw",  0 },
	[OExtuw]  = { "extuw",  0 },
	[OExtsh]  = { "extsh",  0 },
	[OExtuh]  = { "extuh",  0 },
	[OExtsb]  = { "extsb",  0 },
	[OExtub]  = { "extub",  0 },
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
	[OXSetnp] = { "xsetnp", 0},
	[OXSetp]  = { "xsetp",  0},
#define X(c) \
	[OCmpw+IC##c] = { "c"    #c "w", 0 }, \
	[OCmpl+IC##c] = { "c"    #c "l", 0 }, \
	[OXSet+IC##c] = { "xset" #c,     0 },
	ICMPS(X)
#undef X
#define X(c) \
	[OCmps+FC##c] = { "c"    #c "s", 0 }, \
	[OCmpd+FC##c] = { "c"    #c "d", 0 },
	FCMPS(X)
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
	TZ,

	TPlus,

	TInt,
	TFlts,
	TFltd,
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
static char *inpath;
static int thead;
static struct {
	char chr;
	double fltd;
	float flts;
	int64_t num;
	char *str;
} tokval;
static int lnum;

static Tmp *tmp;
static Con *con;
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
err(char *s, ...)
{
	char buf[100], *p, *end;
	va_list ap;


	p = buf;
	end = buf + sizeof(buf);

	va_start(ap, s);
	p += snprintf(p, end - p, "%s:%d: ", inpath, lnum);
	p += vsnprintf(p, end - p, s, ap);
	va_end(ap);

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
		{ "z", TZ },
		{ "loadw", OLoad }, /* for convenience */
		{ "loadl", OLoad },
		{ "loads", OLoad },
		{ "loadd", OLoad },
		{ 0, TXXX }
	};
	static char tok[NString];
	int c, i;
	int t;

	do
		c = fgetc(inf);
	while (isblank(c));
	t = TXXX;
	tokval.chr = c;
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
	case '+':
		return TPlus;
	case 's':
		if (fscanf(inf, "_%f", &tokval.flts) != 1)
			break;
		return TFlts;
	case 'd':
		if (fscanf(inf, "_%lf", &tokval.fltd) != 1)
			break;
		return TFltd;
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
	if (isdigit(c) || c == '-' || c == '+') {
		ungetc(c, inf);
		if (fscanf(inf, "%"SCNd64, &tokval.num) != 1)
			err("invalid integer literal");
		return TInt;
	}
	if (c == '"') {
		tokval.str = vnew(0, 1);
		for (i=0;; i++) {
			c = fgetc(inf);
			if (c == '"')
			if (!i || tokval.str[i-1] != '\\')
				return TStr;
			vgrow(&tokval.str, i+1);
			tokval.str[i] = c;
		}
	}
	if (0)
Alpha:		c = fgetc(inf);
	if (!isalpha(c) && c != '.' && c != '_')
		err("lexing failure: invalid character %c (%d)", c, c);
	i = 0;
	do {
		if (i >= NString-1)
			err("identifier too long");
		tok[i++] = c;
		c = fgetc(inf);
	} while (isalpha(c) || c == '$' || c == '.' || c == '_' || isdigit(c));
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
tmpref(char *v)
{
	int t;

	for (t=Tmp0; t<ntmp; t++)
		if (strcmp(v, tmp[t].name) == 0)
			return TMP(t);
	vgrow(&tmp, ++ntmp);
	strcpy(tmp[t].name, v);
	return TMP(t);
}

static Ref
parseref()
{
	Con c;
	int i;

	memset(&c, 0, sizeof c);
	switch (next()) {
	case TTmp:
		return tmpref(tokval.str);
	case TInt:
		c.type = CBits;
		c.bits.i = tokval.num;
		goto Look;
	case TFlts:
		c.type = CBits;
		c.bits.s = tokval.flts;
		c.flt = 1;
		goto Look;
	case TFltd:
		c.type = CBits;
		c.bits.d = tokval.fltd;
		c.flt = 2;
		goto Look;
	case TGlo:
		c.type = CAddr;
		strcpy(c.label, tokval.str);
	Look:
		for (i=0; i<ncon; i++)
			if (con[i].type == c.type
			&& con[i].bits.i == c.bits.i
			&& strcmp(con[i].label, c.label) == 0)
				return CON(i);
		vgrow(&con, ++ncon);
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
				return 4;
			}
		err("undefined type");
	case TW:
		return Kw;
	case TL:
		return Kl;
	case TS:
		return Ks;
	case TD:
		return Kd;
	}
}

static void
parserefl(int arg)
{
	int k, t, ty;
	Ref r;

	expect(TLParen);
	if (peek() == TRParen) {
		next();
		return;
	}
	for (;;) {
		if (curi - insb >= NIns)
			err("too many instructions (1)");
		k = parsecls(&ty);
		r = parseref();
		if (req(r, R))
			err("invalid reference argument");
		if (!arg && rtype(r) != RTmp)
			err("invalid function parameter");
		if (k == 4)
			if (arg)
				*curi = (Ins){OArgc, R, {TYPE(ty), r}, Kl};
			else
				*curi = (Ins){OParc, r, {TYPE(ty)}, Kl};
		else
			if (arg)
				*curi = (Ins){OArg, R, {r}, k};
			else
				*curi = (Ins){OPar, r, {R}, k};
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
		bmap[i] = bnew();
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
	int t, op, i, k, ty;

	t = nextnl();
	if (ps == PLbl && t != TLbl && t != TRBrace)
		err("label or } expected");
	switch (t) {
	default:
		if (isstore(t)) {
			/* operations without result */
			r = R;
			k = 0;
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
			JRets, JRetd,
			JRetc, JRet0
		}[rcls];
		if (rcls < 5) {
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
	r = tmpref(tokval.str);
	expect(TEq);
	k = parsecls(&ty);
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
		if (k == 4) {
			k = 0;
			arg[1] = TYPE(ty);
		} else
			arg[1] = R;
		goto Ins;
	}
	if (k == 4)
		err("size class must be w, l, s, or d");
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
		curi->cls = k;
		curi->to = r;
		curi->arg[0] = arg[0];
		curi->arg[1] = arg[1];
		curi++;
		return PIns;
	} else {
		phi = alloc(sizeof *phi);
		phi->to = r;
		phi->cls = k;
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
	tmp = vnew(ntmp, sizeof tmp[0]);
	con = vnew(ncon, sizeof con[0]);
	con[0].type = CBits;
	fn = alloc(sizeof *fn);
	blink = &fn->start;
	for (i=0; i<NBlk; i++)
		bmap[i] = 0;
	if (peek() != TGlo)
		rcls = parsecls(&fn->retty);
	else
		rcls = 5;
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
	fn->tmp = tmp;
	fn->con = con;
	fn->mem = vnew(0, sizeof fn->mem[0]);
	fn->ntmp = ntmp;
	fn->ncon = ncon;
	fn->nmem = 0;
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
		if (nextnl() != TInt)
			err("alignment expected");
		for (al=0; tokval.num /= 2; al++)
			;
		ty->align = al;
		t = nextnl();
	}
	if (t != TLBrace)
		err("type body must start with {");
	t = nextnl();
	if (t == TInt) {
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
			default: err("invalid size specifier %c", tokval.chr);
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
			if (t == TInt) {
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
parsedataref(Dat *d)
{
	int t;

	d->isref = 1;
	d->u.ref.nam = tokval.str;
	d->u.ref.off = 0;
	t = peek();
	if (t == TPlus) {
		next();
		if (next() != TInt)
			err("invalid token after offset in ref");
		d->u.ref.off = tokval.num;
	}
}

static void
parsedatastr(Dat *d)
{
	d->isstr = 1;
	d->u.str = tokval.str;
}

static void
parsedat(void cb(Dat *))
{
	char s[NString];
	int t;
	Dat d;

	d.type = DStart;
	cb(&d);
	if (nextnl() != TGlo || nextnl() != TEq)
		err("data name, then = expected");
	strcpy(s, tokval.str);
	t = nextnl();
	if (t == TAlign) {
		if (nextnl() != TInt)
			err("alignment expected");
		d.type = DAlign;
		d.u.num = tokval.num;
		cb(&d);
		t = nextnl();
	}
	d.type = DName;
	d.u.str = s;
	cb(&d);

	if (t != TLBrace)
		err("expected data contents in { .. }");
	for (;;) {
		switch (nextnl()) {
		default: err("invalid size specifier %c in data", tokval.chr);
		case TRBrace: goto Done;
		case TL: d.type = DL; break;
		case TW: d.type = DW; break;
		case TH: d.type = DH; break;
		case TB: d.type = DB; break;
		case TS: d.type = DW; break;
		case TD: d.type = DL; break;
		case TZ: d.type = DZ; break;
		}
		t = nextnl();
		do {
			d.isref = 0;
			d.isstr = 0;
			memset(&d.u, 0, sizeof d.u);
			if (t == TFlts)
				d.u.flts = tokval.flts;
			else if (t == TFltd)
				d.u.fltd = tokval.fltd;
			else if (t == TInt)
				d.u.num = tokval.num;
			else if (t == TGlo)
				parsedataref(&d);
			else if (t == TStr)
				parsedatastr(&d);
			else
				err("constant literal expected");
			cb(&d);
			t = nextnl();
		} while (t == TInt || t == TFlts || t == TFltd);
		if (t == TRBrace)
			break;
		if (t != TComma)
			err(", or } expected");
	}
Done:
	d.type = DEnd;
	cb(&d);
}

void
parse(FILE *f, char *path, void data(Dat *), void func(Fn *))
{
	inf = f;
	inpath = path;
	lnum = 1;
	thead = TXXX;
	ntyp = 0;
	for (;;)
		switch (nextnl()) {
		case TFunc:
			func(parsefn());
			break;
		case TType:
			parsetyp();
			break;
		case TData:
			parsedat(data);
			break;
		case TEOF:
			return;
		default:
			err("top-level definition expected");
			break;
		}
}

static void
printcon(Con *c, FILE *f)
{
	switch (c->type) {
	case CUndef:
		break;
	case CAddr:
		fprintf(f, "$%s", c->label);
		if (c->bits.i)
			fprintf(f, "%+"PRIi64, c->bits.i);
		break;
	case CBits:
		if (c->flt == 1)
			fprintf(f, "s_%f", c->bits.s);
		else if (c->flt == 2)
			fprintf(f, "d_%lf", c->bits.d);
		else
			fprintf(f, "%"PRIi64, c->bits.i);
		break;
	}
}

void
printref(Ref r, Fn *fn, FILE *f)
{
	int i;
	Mem *m;

	switch (rtype(r)) {
	case RTmp:
		if (r.val < Tmp0)
			fprintf(f, "R%d", r.val);
		else
			fprintf(f, "%%%s", fn->tmp[r.val].name);
		break;
	case RCon:
		printcon(&fn->con[r.val], f);
		break;
	case RSlot:
		fprintf(f, "S%d", r.val);
		break;
	case RACall:
		fprintf(f, "%03x", r.val & AMask);
		break;
	case RAType:
		fprintf(f, ":%s", typ[r.val & AMask].name);
		break;
	case RAMem:
		i = 0;
		m = &fn->mem[r.val & AMask];
		fputc('[', f);
		if (m->offset.type != CUndef) {
			printcon(&m->offset, f);
			i = 1;
		}
		if (!req(m->base, R)) {
			if (i)
				fprintf(f, " + ");
			printref(m->base, fn, f);
			i = 1;
		}
		if (!req(m->index, R)) {
			if (i)
				fprintf(f, " + ");
			fprintf(f, "%d * ", m->scale);
			printref(m->index, fn, f);
		}
		fputc(']', f);
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
		[JRets]     = "rets",
		[JRetd]     = "retd",
		[JJnz]      = "jnz",
		[JXJnp]     = "xjnp",
		[JXJp]      = "xjp",
	#define X(c) [JXJc+IC##c] = "xj" #c,
		ICMPS(X)
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
	static char ktoc[] = "wlsd";
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
			fprintf(f, " =%c phi ", ktoc[p->cls]);
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
				fprintf(f, " =%c ", ktoc[i->cls]);
			}
			assert(opdesc[i->op].name);
			fprintf(f, "%s", opdesc[i->op].name);
			if (req(i->to, R) && prcls[i->op])
				fputc(ktoc[i->cls], f);
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
		case JRets:
		case JRetd:
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
