#include "all.h"
#include <ctype.h>
#include <stdarg.h>

enum {
	Ke = -2, /* Erroneous mode */
	Km = Kl, /* Memory pointer (for x64) */
};

OpDesc opdesc[NOp] = {
#define A(a,b,c,d) {[Kw]=K##a, [Kl]=K##b, [Ks]=K##c, [Kd]=K##d}

	/*            NAME       NM      ARGCLS0     ARGCLS1  SF LF FLD*/
	[Oadd]    = { "add",      2, {A(w,l,s,d), A(w,l,s,d)}, 1, 0, 1 },
	[Osub]    = { "sub",      2, {A(w,l,s,d), A(w,l,s,d)}, 1, 0, 1 },
	[Odiv]    = { "div",      2, {A(w,l,s,d), A(w,l,s,d)}, 0, 0, 1 },
	[Orem]    = { "rem",      2, {A(w,l,e,e), A(w,l,e,e)}, 0, 0, 1 },
	[Oudiv]   = { "udiv",     2, {A(w,l,e,e), A(w,l,e,e)}, 0, 0, 1 },
	[Ourem]   = { "urem",     2, {A(w,l,e,e), A(w,l,e,e)}, 0, 0, 1 },
	[Omul]    = { "mul",      2, {A(w,l,s,d), A(w,l,s,d)}, 0, 0, 1 },
	[Oand]    = { "and",      2, {A(w,l,e,e), A(w,l,e,e)}, 1, 0, 1 },
	[Oor]     = { "or",       2, {A(w,l,e,e), A(w,l,e,e)}, 1, 0, 1 },
	[Oxor]    = { "xor",      2, {A(w,l,e,e), A(w,l,e,e)}, 1, 0, 1 },
	[Osar]    = { "sar",      1, {A(w,l,e,e), A(w,w,e,e)}, 1, 0, 1 },
	[Oshr]    = { "shr",      1, {A(w,l,e,e), A(w,w,e,e)}, 1, 0, 1 },
	[Oshl]    = { "shl",      1, {A(w,l,e,e), A(w,w,e,e)}, 1, 0, 1 },
	[Ostored] = { "stored",   0, {A(d,d,d,d), A(m,m,m,m)}, 0, 1, 0 },
	[Ostores] = { "stores",   0, {A(s,s,s,s), A(m,m,m,m)}, 0, 1, 0 },
	[Ostorel] = { "storel",   0, {A(l,l,l,l), A(m,m,m,m)}, 0, 1, 0 },
	[Ostorew] = { "storew",   0, {A(w,w,w,w), A(m,m,m,m)}, 0, 1, 0 },
	[Ostoreh] = { "storeh",   0, {A(w,w,w,w), A(m,m,m,m)}, 0, 1, 0 },
	[Ostoreb] = { "storeb",   0, {A(w,w,w,w), A(m,m,m,m)}, 0, 1, 0 },
	[Oload]   = { "load",     0, {A(m,m,m,m), A(x,x,x,x)}, 0, 1, 0 },
	[Oloadsw] = { "loadsw",   0, {A(m,m,e,e), A(x,x,e,e)}, 0, 1, 0 },
	[Oloaduw] = { "loaduw",   0, {A(m,m,e,e), A(x,x,e,e)}, 0, 1, 0 },
	[Oloadsh] = { "loadsh",   0, {A(m,m,e,e), A(x,x,e,e)}, 0, 1, 0 },
	[Oloaduh] = { "loaduh",   0, {A(m,m,e,e), A(x,x,e,e)}, 0, 1, 0 },
	[Oloadsb] = { "loadsb",   0, {A(m,m,e,e), A(x,x,e,e)}, 0, 1, 0 },
	[Oloadub] = { "loadub",   0, {A(m,m,e,e), A(x,x,e,e)}, 0, 1, 0 },
	[Oextsw]  = { "extsw",    0, {A(e,w,e,e), A(e,x,e,e)}, 0, 1, 1 },
	[Oextuw]  = { "extuw",    0, {A(e,w,e,e), A(e,x,e,e)}, 0, 1, 1 },
	[Oextsh]  = { "extsh",    0, {A(w,w,e,e), A(x,x,e,e)}, 0, 1, 1 },
	[Oextuh]  = { "extuh",    0, {A(w,w,e,e), A(x,x,e,e)}, 0, 1, 1 },
	[Oextsb]  = { "extsb",    0, {A(w,w,e,e), A(x,x,e,e)}, 0, 1, 1 },
	[Oextub]  = { "extub",    0, {A(w,w,e,e), A(x,x,e,e)}, 0, 1, 1 },
	[Oexts]   = { "exts",     0, {A(e,e,e,s), A(e,e,e,x)}, 0, 1, 1 },
	[Otruncd] = { "truncd",   0, {A(e,e,d,e), A(e,e,x,e)}, 0, 1, 1 },
	[Ostosi]  = { "stosi",    0, {A(s,s,e,e), A(x,x,e,e)}, 0, 1, 1 },
	[Odtosi]  = { "dtosi",    0, {A(d,d,e,e), A(x,x,e,e)}, 0, 1, 1 },
	[Oswtof]  = { "swtof",    0, {A(e,e,w,w), A(e,e,x,x)}, 0, 1, 1 },
	[Osltof]  = { "sltof",    0, {A(e,e,l,l), A(e,e,x,x)}, 0, 1, 1 },
	[Ocast]   = { "cast",     0, {A(s,d,w,l), A(x,x,x,x)}, 0, 1, 1 },
	[Ocopy]   = { "copy",     1, {A(w,l,s,d), A(x,x,x,x)}, 0, 1, 0 },
	[Onop]    = { "nop",      0, {A(x,x,x,x), A(x,x,x,x)}, 0, 1, 0 },
	[Oswap]   = { "swap",     2, {A(w,l,s,d), A(w,l,s,d)}, 0, 0, 0 },
	[Osign]   = { "sign",     0, {A(w,l,e,e), A(x,x,e,e)}, 0, 0, 0 },
	[Osalloc] = { "salloc",   0, {A(e,l,e,e), A(e,x,e,e)}, 0, 0, 0 },
	[Oxidiv]  = { "xidiv",    1, {A(w,l,e,e), A(x,x,e,e)}, 0, 0, 0 },
	[Oxdiv]   = { "xdiv",     1, {A(w,l,e,e), A(x,x,e,e)}, 0, 0, 0 },
	[Oxcmp]   = { "xcmp",     1, {A(w,l,s,d), A(w,l,s,d)}, 1, 0, 0 },
	[Oxtest]  = { "xtest",    1, {A(w,l,e,e), A(w,l,e,e)}, 1, 0, 0 },
	[Oaddr]   = { "addr",     0, {A(m,m,e,e), A(x,x,e,e)}, 0, 1, 0 },
	[Opar]    = { "parn",     0, {A(x,x,x,x), A(x,x,x,x)}, 0, 0, 0 },
	[Oparc]   = { "parc",     0, {A(e,x,e,e), A(e,x,e,e)}, 0, 0, 0 },
	[Oarg]    = { "arg",      0, {A(w,l,s,d), A(x,x,x,x)}, 0, 0, 0 },
	[Oargc]   = { "argc",     0, {A(e,x,e,e), A(e,l,e,e)}, 0, 0, 0 },
	[Ocall]   = { "call",     0, {A(m,m,m,m), A(x,x,x,x)}, 0, 0, 0 },
	[Oxsetnp] = { "xsetnp",   0, {A(x,x,e,e), A(x,x,e,e)}, 0, 0, 0 },
	[Oxsetp]  = { "xsetp",    0, {A(x,x,e,e), A(x,x,e,e)}, 0, 0, 0 },
	[Oalloc]   = { "alloc4",  1, {A(e,l,e,e), A(e,x,e,e)}, 0, 0, 0 },
	[Oalloc+1] = { "alloc8",  1, {A(e,l,e,e), A(e,x,e,e)}, 0, 0, 0 },
	[Oalloc+2] = { "alloc16", 1, {A(e,l,e,e), A(e,x,e,e)}, 0, 0, 0 },
#define X(c) \
	[Ocmpw+IC##c] = { "c"    #c "w", 0, {A(w,w,e,e), A(w,w,e,e)}, 1, 0, 1 }, \
	[Ocmpl+IC##c] = { "c"    #c "l", 0, {A(l,l,e,e), A(l,l,e,e)}, 1, 0, 1 }, \
	[Oxset+IC##c] = { "xset" #c,     0, {A(x,x,e,e), A(x,x,e,e)}, 0, 1, 0 },
	ICMPS(X)
#undef X
#define X(c) \
	[Ocmps+FC##c] = { "c"    #c "s", 0, {A(s,s,e,e), A(s,s,e,e)}, 1, 0, 1 }, \
	[Ocmpd+FC##c] = { "c"    #c "d", 0, {A(d,d,e,e), A(d,d,e,e)}, 1, 0, 1 },
	FCMPS(X)
#undef X

};
#undef A

typedef enum {
	PXXX,
	PLbl,
	PPhi,
	PIns,
	PEnd,
} PState;

enum {
	Txxx = NPubOp,
	Tcall,
	Tphi,
	Tjmp,
	Tjnz,
	Tret,
	Texport,
	Tfunc,
	Ttype,
	Tdata,
	Talign,
	Tl,
	Tw,
	Th,
	Tb,
	Td,
	Ts,
	Tz,

	Tint,
	Tflts,
	Tfltd,
	Ttmp,
	Tlbl,
	Tglo,
	TTyp,
	TStr,

	Tplus,
	Teq,
	Tcomma,
	Tlparen,
	Trparen,
	Tlbrace,
	Trbrace,
	Tnl,
	Teof,
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

static Fn *curf;
static Phi **plink;
static Blk **bmap;
static Blk *curb;
static Blk **blink;
static int nblk;
static int rcls;
static int ntyp;


void
err(char *s, ...)
{
	va_list ap;

	va_start(ap, s);
	fprintf(stderr, "%s:%d: ", inpath, lnum);
	vfprintf(stderr, s, ap);
	fprintf(stderr, "\n");
	va_end(ap);
	exit(1);
}

static int
lex()
{
	static struct {
		char *str;
		int tok;
	} tmap[] = {
		{ "call", Tcall },
		{ "phi", Tphi },
		{ "jmp", Tjmp },
		{ "jnz", Tjnz },
		{ "ret", Tret },
		{ "export", Texport },
		{ "function", Tfunc },
		{ "type", Ttype },
		{ "data", Tdata },
		{ "align", Talign },
		{ "l", Tl },
		{ "w", Tw },
		{ "h", Th },
		{ "b", Tb },
		{ "d", Td },
		{ "s", Ts },
		{ "z", Tz },
		{ "loadw", Oload }, /* for convenience */
		{ "loadl", Oload },
		{ "loads", Oload },
		{ "loadd", Oload },
		{ "alloc1", Oalloc },
		{ "alloc2", Oalloc },
		{ 0, Txxx }
	};
	static char tok[NString];
	int c, i;
	int t;

	do
		c = fgetc(inf);
	while (isblank(c));
	t = Txxx;
	tokval.chr = c;
	switch (c) {
	case EOF:
		return Teof;
	case ',':
		return Tcomma;
	case '(':
		return Tlparen;
	case ')':
		return Trparen;
	case '{':
		return Tlbrace;
	case '}':
		return Trbrace;
	case '=':
		return Teq;
	case '+':
		return Tplus;
	case 's':
		if (fscanf(inf, "_%f", &tokval.flts) != 1)
			break;
		return Tflts;
	case 'd':
		if (fscanf(inf, "_%lf", &tokval.fltd) != 1)
			break;
		return Tfltd;
	case '%':
		t = Ttmp;
		goto Alpha;
	case '@':
		t = Tlbl;
		goto Alpha;
	case '$':
		t = Tglo;
		goto Alpha;
	case ':':
		t = TTyp;
		goto Alpha;
	case '#':
		while ((c=fgetc(inf)) != '\n' && c != EOF)
			;
	case '\n':
		lnum++;
		return Tnl;
	}
	if (isdigit(c) || c == '-' || c == '+') {
		ungetc(c, inf);
		if (fscanf(inf, "%"SCNd64, &tokval.num) != 1)
			err("invalid integer literal");
		return Tint;
	}
	if (c == '"') {
		tokval.str = vnew(0, 1);
		for (i=0;; i++) {
			c = fgetc(inf);
			if (c == EOF)
				err("unterminated string");
			vgrow(&tokval.str, i+1);
			if (c == '"')
			if (!i || tokval.str[i-1] != '\\') {
				tokval.str[i] = 0;
				return TStr;
			}
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
	tokval.str = tok;
	if (t != Txxx) {
		return t;
	}
	for (i=0; i<NPubOp; i++)
		if (opdesc[i].name)
		if (strcmp(tok, opdesc[i].name) == 0)
			return i;
	for (i=0; tmap[i].str; i++)
		if (strcmp(tok, tmap[i].str) == 0)
			return tmap[i].tok;
	err("unknown keyword %s", tokval.str);
	return Txxx;
}

static int
peek()
{
	if (thead == Txxx)
		thead = lex();
	return thead;
}

static int
next()
{
	int t;

	t = peek();
	thead = Txxx;
	return t;
}

static int
nextnl()
{
	int t;

	while ((t = next()) == Tnl)
		;
	return t;
}

static void
expect(int t)
{
	static char *ttoa[] = {
		[Tlbl] = "label",
		[Tcomma] = ",",
		[Teq] = "=",
		[Tnl] = "newline",
		[Tlparen] = "(",
		[Trparen] = ")",
		[Tlbrace] = "{",
		[Trbrace] = "}",
		[Teof] = 0,
	};
	char buf[128], *s1, *s2;
	int t1;

	t1 = next();
	if (t == t1)
		return;
	s1 = ttoa[t] ? ttoa[t] : "??";
	s2 = ttoa[t1] ? ttoa[t1] : "??";
	sprintf(buf, "%s expected, got %s instead", s1, s2);
	err(buf);
}

static Ref
tmpref(char *v)
{
	int t;

	for (t=Tmp0; t<curf->ntmp; t++)
		if (strcmp(v, curf->tmp[t].name) == 0)
			return TMP(t);
	newtmp(0, Kx, curf);
	strcpy(curf->tmp[t].name, v);
	return TMP(t);
}

static Ref
parseref()
{
	Con c;
	int i;

	memset(&c, 0, sizeof c);
	switch (next()) {
	case Ttmp:
		return tmpref(tokval.str);
	case Tint:
		c.type = CBits;
		c.bits.i = tokval.num;
		goto Look;
	case Tflts:
		c.type = CBits;
		c.bits.s = tokval.flts;
		c.flt = 1;
		goto Look;
	case Tfltd:
		c.type = CBits;
		c.bits.d = tokval.fltd;
		c.flt = 2;
		goto Look;
	case Tglo:
		c.type = CAddr;
		strcpy(c.label, tokval.str);
	Look:
		for (i=0; i<curf->ncon; i++)
			if (curf->con[i].type == c.type
			&& curf->con[i].bits.i == c.bits.i
			&& strcmp(curf->con[i].label, c.label) == 0)
				return CON(i);
		vgrow(&curf->con, ++curf->ncon);
		curf->con[i] = c;
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
	case Tw:
		return Kw;
	case Tl:
		return Kl;
	case Ts:
		return Ks;
	case Td:
		return Kd;
	}
}

static void
parserefl(int arg)
{
	int k, ty;
	Ref r;

	expect(Tlparen);
	while (peek() != Trparen) {
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
				*curi = (Ins){Oargc, R, {TYPE(ty), r}, Kl};
			else
				*curi = (Ins){Oparc, r, {TYPE(ty)}, Kl};
		else
			if (arg)
				*curi = (Ins){Oarg, R, {r}, k};
			else
				*curi = (Ins){Opar, r, {R}, k};
		curi++;
		if (peek() == Trparen)
			break;
		expect(Tcomma);
	}
	next();
}

static Blk *
findblk(char *name)
{
	int i;

	for (i=0; i<nblk; i++)
		if (strcmp(bmap[i]->name, name) == 0)
			return bmap[i];
	vgrow(&bmap, ++nblk);
	bmap[i] = blknew();
	bmap[i]->id = i;
	strcpy(bmap[i]->name, name);
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
	if (ps == PLbl && t != Tlbl && t != Trbrace)
		err("label or } expected");
	switch (t) {
	default:
		if (isstore(t) || t == Tcall) {
			/* operations without result */
			r = R;
			k = Kw;
			op = t;
			goto DoOp;
		}
		err("label, instruction or jump expected");
	case Trbrace:
		return PEnd;
	case Ttmp:
		break;
	case Tlbl:
		b = findblk(tokval.str);
		if (curb && curb->jmp.type == Jxxx) {
			closeblk();
			curb->jmp.type = Jjmp;
			curb->s1 = b;
		}
		if (b->jmp.type != Jxxx)
			err("multiple definitions of block @%s", b->name);
		*blink = b;
		curb = b;
		plink = &curb->phi;
		expect(Tnl);
		return PPhi;
	case Tret:
		curb->jmp.type = (int[]){
			Jretw, Jretl,
			Jrets, Jretd,
			Jretc, Jret0
		}[rcls];
		if (rcls < 5) {
			r = parseref();
			if (req(r, R))
				err("return value expected");
			curb->jmp.arg = r;
		}
		goto Close;
	case Tjmp:
		curb->jmp.type = Jjmp;
		goto Jump;
	case Tjnz:
		curb->jmp.type = Jjnz;
		r = parseref();
		if (req(r, R))
			err("invalid argument for jnz jump");
		curb->jmp.arg = r;
		expect(Tcomma);
	Jump:
		expect(Tlbl);
		curb->s1 = findblk(tokval.str);
		if (curb->jmp.type != Jjmp) {
			expect(Tcomma);
			expect(Tlbl);
			curb->s2 = findblk(tokval.str);
		}
		if (curb->s1 == curf->start || curb->s2 == curf->start)
			err("invalid jump to the start node");
	Close:
		expect(Tnl);
		closeblk();
		return PLbl;
	}
	r = tmpref(tokval.str);
	expect(Teq);
	k = parsecls(&ty);
	op = next();
DoOp:
	if (op == Tphi) {
		if (ps != PPhi || curb == curf->start)
			err("unexpected phi instruction");
		op = -1;
	}
	if (op == Tcall) {
		arg[0] = parseref();
		parserefl(1);
		expect(Tnl);
		op = Ocall;
		if (k == 4) {
			k = Kl;
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
	if (peek() != Tnl)
		for (;;) {
			if (i == NPred)
				err("too many arguments");
			if (op == -1) {
				expect(Tlbl);
				blk[i] = findblk(tokval.str);
			}
			arg[i] = parseref();
			if (req(arg[i], R))
				err("invalid instruction argument");
			i++;
			t = peek();
			if (t == Tnl)
				break;
			if (t != Tcomma)
				err(", or end of line expected");
			next();
		}
	next();
Ins:
	if (op != -1) {
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

static int
usecheck(Ref r, int k, Fn *fn)
{
	return rtype(r) != RTmp || fn->tmp[r.val].cls == k
		|| (fn->tmp[r.val].cls == Kl && k == Kw);
}

static void
typecheck(Fn *fn)
{
	Blk *b;
	Phi *p;
	Ins *i;
	uint n;
	int k;
	Tmp *t;
	Ref r;
	BSet pb[1], ppb[1];

	fillpreds(fn);
	bsinit(pb, fn->nblk);
	bsinit(ppb, fn->nblk);
	for (b=fn->start; b; b=b->link) {
		for (p=b->phi; p; p=p->link)
			fn->tmp[p->to.val].cls = p->cls;
		for (i=b->ins; i-b->ins < b->nins; i++)
			if (rtype(i->to) == RTmp) {
				t = &fn->tmp[i->to.val];
				if (clsmerge(&t->cls, i->cls))
					err("temporary %%%s is assigned with"
						" multiple types", t->name);
			}
	}
	for (b=fn->start; b; b=b->link) {
		bszero(pb);
		for (n=0; n<b->npred; n++)
			bsset(pb, b->pred[n]->id);
		for (p=b->phi; p; p=p->link) {
			bszero(ppb);
			t = &fn->tmp[p->to.val];
			for (n=0; n<p->narg; n++) {
				k = t->cls;
				if (bshas(ppb, p->blk[n]->id))
					err("multiple entries for @%s in phi %%%s",
						p->blk[n]->name, t->name);
				if (!usecheck(p->arg[n], k, fn))
					err("invalid type for operand %%%s in phi %%%s",
						fn->tmp[p->arg[n].val].name, t->name);
				bsset(ppb, p->blk[n]->id);
			}
			if (!bsequal(pb, ppb))
				err("predecessors not matched in phi %%%s", t->name);
		}
		for (i=b->ins; i-b->ins < b->nins; i++)
			for (n=0; n<2; n++) {
				k = opdesc[i->op].argcls[n][i->cls];
				r = i->arg[n];
				t = &fn->tmp[r.val];
				if (k == Ke)
					err("invalid instruction type in %s",
						opdesc[i->op].name);
				if (rtype(r) == RType)
					continue;
				if (rtype(r) != -1 && k == Kx)
					err("no %s operand expected in %s",
						n == 1 ? "second" : "first",
						opdesc[i->op].name);
				if (rtype(r) == -1 && k != Kx)
					err("missing %s operand in %s",
						n == 1 ? "second" : "first",
						opdesc[i->op].name);
				if (!usecheck(r, k, fn))
					err("invalid type for %s operand %%%s in %s",
						n == 1 ? "second" : "first",
						t->name, opdesc[i->op].name);
			}
		r = b->jmp.arg;
		if (isret(b->jmp.type)) {
			if (b->jmp.type == Jretc) {
				if (!usecheck(r, Kl, fn))
					goto JErr;
			} else if (!usecheck(r, b->jmp.type-Jretw, fn))
				goto JErr;
		}
		if (b->jmp.type == Jjnz && !usecheck(r, Kw, fn))
		JErr:
			err("invalid type for jump argument %%%s in block @%s",
				fn->tmp[r.val].name, b->name);
		if (b->s1 && b->s1->jmp.type == Jxxx)
			err("block @%s is used undefined", b->s1->name);
		if (b->s2 && b->s2->jmp.type == Jxxx)
			err("block @%s is used undefined", b->s2->name);
	}
}

static Fn *
parsefn(int export)
{
	int r;
	PState ps;

	curb = 0;
	nblk = 0;
	curi = insb;
	curf = alloc(sizeof *curf);
	curf->ntmp = 0;
	curf->ncon = 1; /* first constant must be 0 */
	curf->tmp = vnew(curf->ntmp, sizeof curf->tmp[0]);
	curf->con = vnew(curf->ncon, sizeof curf->con[0]);
	for (r=0; r<Tmp0; r++)
		newtmp(0, r < XMM0 ? Kl : Kd, curf);
	bmap = vnew(nblk, sizeof bmap[0]);
	curf->con[0].type = CBits;
	curf->export = export;
	blink = &curf->start;
	curf->retty = Kx;
	if (peek() != Tglo)
		rcls = parsecls(&curf->retty);
	else
		rcls = 5;
	if (next() != Tglo)
		err("function name expected");
	strcpy(curf->name, tokval.str);
	parserefl(0);
	if (nextnl() != Tlbrace)
		err("function body must start with {");
	ps = PLbl;
	do
		ps = parseline(ps);
	while (ps != PEnd);
	if (!curb)
		err("empty function");
	if (curb->jmp.type == Jxxx)
		err("last block misses jump");
	curf->mem = vnew(0, sizeof curf->mem[0]);
	curf->nmem = 0;
	curf->nblk = nblk;
	curf->rpo = 0;
	typecheck(curf);
	return curf;
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
	if (nextnl() != TTyp ||  nextnl() != Teq)
		err("type name, then = expected");
	strcpy(ty->name, tokval.str);
	t = nextnl();
	if (t == Talign) {
		if (nextnl() != Tint)
			err("alignment expected");
		for (al=0; tokval.num /= 2; al++)
			;
		ty->align = al;
		t = nextnl();
	}
	if (t != Tlbrace)
		err("type body must start with {");
	t = nextnl();
	if (t == Tint) {
		ty->dark = 1;
		ty->size = tokval.num;
		if (ty->align == -1)
			err("dark types need alignment");
		t = nextnl();
	} else {
		ty->dark = 0;
		n = 0;
		sz = 0;
		al = 0;
		while (t != Trbrace) {
			flt = 0;
			switch (t) {
			default: err("invalid size specifier %c", tokval.chr);
			case Td: flt = 1;
			case Tl: s = 8; a = 3; break;
			case Ts: flt = 1;
			case Tw: s = 4; a = 2; break;
			case Th: s = 2; a = 1; break;
			case Tb: s = 1; a = 0; break;
			}
			if (a > al)
				al = a;
			if ((a = sz & (s-1))) {
				a = s - a;
				if (n < NSeg) {
					/* padding segment */
					ty->seg[n].ispad = 1;
					ty->seg[n].len = a;
					n++;
				}
			}
			t = nextnl();
			if (t == Tint) {
				c = tokval.num;
				t = nextnl();
			} else
				c = 1;
			while (c-- > 0)
				if (n < NSeg) {
					ty->seg[n].isflt = flt;
					ty->seg[n].ispad = 0;
					ty->seg[n].len = s;
					sz += a + s;
					n++;
				}
			if (t != Tcomma)
				break;
			t = nextnl();
		}
		if (n >= NSeg)
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
	if (t != Trbrace)
		err(", or } expected");
}

static void
parsedatref(Dat *d)
{
	int t;

	d->isref = 1;
	d->u.ref.nam = tokval.str;
	d->u.ref.off = 0;
	t = peek();
	if (t == Tplus) {
		next();
		if (next() != Tint)
			err("invalid token after offset in ref");
		d->u.ref.off = tokval.num;
	}
}

static void
parsedatstr(Dat *d)
{
	d->isstr = 1;
	d->u.str = tokval.str;
}

static void
parsedat(void cb(Dat *), int export)
{
	char s[NString];
	int t;
	Dat d;

	d.type = DStart;
	d.isstr = 0;
	d.isref = 0;
	d.export = export;
	cb(&d);
	if (nextnl() != Tglo || nextnl() != Teq)
		err("data name, then = expected");
	strcpy(s, tokval.str);
	t = nextnl();
	if (t == Talign) {
		if (nextnl() != Tint)
			err("alignment expected");
		d.type = DAlign;
		d.u.num = tokval.num;
		cb(&d);
		t = nextnl();
	}
	d.type = DName;
	d.u.str = s;
	cb(&d);

	if (t != Tlbrace)
		err("expected data contents in { .. }");
	for (;;) {
		switch (nextnl()) {
		default: err("invalid size specifier %c in data", tokval.chr);
		case Trbrace: goto Done;
		case Tl: d.type = DL; break;
		case Tw: d.type = DW; break;
		case Th: d.type = DH; break;
		case Tb: d.type = DB; break;
		case Ts: d.type = DW; break;
		case Td: d.type = DL; break;
		case Tz: d.type = DZ; break;
		}
		t = nextnl();
		do {
			d.isref = 0;
			d.isstr = 0;
			memset(&d.u, 0, sizeof d.u);
			if (t == Tflts)
				d.u.flts = tokval.flts;
			else if (t == Tfltd)
				d.u.fltd = tokval.fltd;
			else if (t == Tint)
				d.u.num = tokval.num;
			else if (t == Tglo)
				parsedatref(&d);
			else if (t == TStr)
				parsedatstr(&d);
			else
				err("constant literal expected");
			cb(&d);
			t = nextnl();
		} while (t == Tint || t == Tflts || t == Tfltd);
		if (t == Trbrace)
			break;
		if (t != Tcomma)
			err(", or } expected");
	}
Done:
	d.type = DEnd;
	cb(&d);
}

void
parse(FILE *f, char *path, void data(Dat *), void func(Fn *))
{
	int t, export;

	inf = f;
	inpath = path;
	lnum = 1;
	thead = Txxx;
	ntyp = 0;
	for (;;) {
		export = 0;
		switch (nextnl()) {
		default:
			err("top-level definition expected");
		case Texport:
			export = 1;
			t = nextnl();
			if (t == Tfunc) {
		case Tfunc:
				func(parsefn(export));
				break;
			}
			else if (t == Tdata) {
		case Tdata:
				parsedat(data, export);
				break;
			}
			else
				err("export can only qualify data and function");
		case Ttype:
			parsetyp();
			break;
		case Teof:
			return;
		}
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
		fprintf(f, "S%d", (r.val&(1<<28)) ? r.val-(1<<29) : r.val);
		break;
	case RCall:
		fprintf(f, "%03x", r.val);
		break;
	case RType:
		fprintf(f, ":%s", typ[r.val].name);
		break;
	case RMem:
		i = 0;
		m = &fn->mem[r.val];
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
		[Jret0]     = "ret",
		[Jretw]     = "retw",
		[Jretl]     = "retl",
		[Jretc]     = "retc",
		[Jrets]     = "rets",
		[Jretd]     = "retd",
		[Jjnz]      = "jnz",
		[Jxjnp]     = "xjnp",
		[Jxjp]      = "xjp",
	#define X(c) [Jxjc+IC##c] = "xj" #c,
		ICMPS(X)
	#undef X
	};
	static char prcls[NOp] = {
		[Oarg] = 1,
		[Oswap] = 1,
		[Oxcmp] = 1,
		[Oxtest] = 1,
		[Oxdiv] = 1,
		[Oxidiv] = 1,
	};
	static char ktoc[] = "wlsd";
	Blk *b;
	Phi *p;
	Ins *i;
	uint n;

	if (fn->export)
		fprintf(f, "export ");
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
		case Jret0:
		case Jretw:
		case Jretl:
		case Jrets:
		case Jretd:
		case Jretc:
			fprintf(f, "\t%s", jtoa[b->jmp.type]);
			if (b->jmp.type != Jret0 || !req(b->jmp.arg, R)) {
				fprintf(f, " ");
				printref(b->jmp.arg, fn, f);
			}
			if (b->jmp.type == Jretc)
				fprintf(f, ", :%s", typ[fn->retty].name);
			fprintf(f, "\n");
			break;
		case Jjmp:
			if (b->s1 != b->link)
				fprintf(f, "\tjmp @%s\n", b->s1->name);
			break;
		default:
			fprintf(f, "\t%s ", jtoa[b->jmp.type]);
			if (b->jmp.type == Jjnz) {
				printref(b->jmp.arg, fn, f);
				fprintf(f, ", ");
			}
			fprintf(f, "@%s, @%s\n", b->s1->name, b->s2->name);
			break;
		}
	}
	fprintf(f, "}\n");
}
