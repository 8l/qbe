%{

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum {
	NString = 16,
	NVar = 256,
	NStr = 256,
};

enum { /* minic types */
	INT = 0,
	LNG = 1,
	PTR = 2,
};

#define IDIR(x) (((x) << 2) + PTR)
#define DREF(x) ((x) >> 2)
#define KIND(x) ((x) & 3)
#define SIZE(x) (KIND(x) == INT ? 4 : 8)

typedef struct Node Node;
typedef struct Symb Symb;
typedef struct Stmt Stmt;

struct Node {
	char op;
	union {
		int n;
		char v[NString];
	} u;
	Node *l, *r;
};

struct Symb {
	enum {
		Con,
		Tmp,
		Var,
		Glo,
	} t;
	union {
		int n;
		char v[NString];
	} u;
	unsigned long ctyp;
};

struct Stmt {
	enum {
		If,
		While,
		Seq,
		Expr,
	} t;
	void *p1, *p2, *p3;
};

int yylex(void), yyerror(char *);
Symb expr(Node *), lval(Node *);

FILE *of;
int lbl, tmp, str;
char *slit[NStr];
struct {
	char v[NString];
	unsigned ctyp;
} varh[NVar];

void
die(char *s)
{
	fprintf(stderr, "error: %s\n", s);
	exit(1);
}

void *
alloc(size_t s)
{
	void *p;

	p = malloc(s);
	if (!p)
		die("out of memory");
	return p;
}

unsigned
hash(char *s)
{
	unsigned h;

	h = 42;
	while (*s)
		h += 11 * h + *s++;
	return h % NVar;
}

void
varclr()
{
	unsigned h;

	for (h=0; h<NVar; h++)
		varh[h].v[0] = 0;
}

void
varadd(char *v, unsigned ctyp)
{
	unsigned h0, h;

	h0 = hash(v);
	h = h0;
	do {
		if (varh[h].v[0] == 0) {
			strcpy(varh[h].v, v);
			varh[h].ctyp = ctyp;
			return;
		}
		if (strcmp(varh[h].v, v) == 0)
			die("double definition");
	} while(++h != h0);
	die("too many variables");
}

unsigned
varctyp(char *v)
{
	unsigned h0, h;

	h0 = hash(v);
	h = h0;
	do {
		if (strcmp(varh[h].v, v) == 0)
			return varh[h].ctyp;
	} while (++h != h0 && varh[h].v[0] != 0);
	die("undeclared variable");
	return -1;
}

char
irtyp(unsigned ctyp)
{
	switch (KIND(ctyp)) {
	default:
		die("internal error");
	case INT:
		return 'w';
	case PTR:
	case LNG:
		return 'l';
	}
}

void
psymb(Symb s)
{
	switch (s.t) {
	case Tmp:
		fprintf(of, "%%t%d", s.u.n);
		break;
	case Var:
		fprintf(of, "%%%s", s.u.v);
		break;
	case Con:
		fprintf(of, "%d", s.u.n);
		break;
	case Glo:
		fprintf(of, "$%s", s.u.v);
		break;
	}
}

void
sext(Symb *s)
{
	fprintf(of, "\t%%t%d =l sext ", tmp);
	psymb(*s);
	fprintf(of, "\n");
	s->t = Tmp;
	s->ctyp = LNG;
	s->u.n = tmp++;
}

unsigned
prom(int op, Symb *l, Symb *r)
{
	Symb *t;
	int sz;

	if (l->ctyp == r->ctyp && KIND(l->ctyp) != PTR)
		return l->ctyp;

	if (l->ctyp == LNG && r->ctyp == INT) {
		sext(r);
		return LNG;
	}
	if (l->ctyp == INT && r->ctyp == LNG) {
		sext(l);
		return LNG;
	}

	if (op == '+') {
		if (KIND(r->ctyp) == PTR) {
			t = l;
			l = r;
			r = t;
		}
		if (KIND(r->ctyp) == PTR)
			die("pointers added");
		goto Scale;
	}

	if (op == '-') {
		if (KIND(l->ctyp) != PTR)
			die("pointer substracted from integer");
		if (KIND(r->ctyp) != PTR)
			goto Scale;
		if (l->ctyp != r->ctyp)
			die("non-homogeneous pointers in substraction");
		return LNG;
	}

Scale:
	if (irtyp(r->ctyp) != 'l')
		sext(r);
	sz = SIZE(DREF(l->ctyp));
	fprintf(of, "\t%%t%d =l mul %d, ", tmp, sz);
	psymb(*r);
	fprintf(of, "\n");
	r->u.n = tmp++;
	return l->ctyp;
}

void
load(Symb d, Symb s)
{
	fprintf(of, "\t");
	psymb(d);
	fprintf(of, " =%c load ", irtyp(d.ctyp));
	psymb(s);
	fprintf(of, "\n");
}

Symb
expr(Node *n)
{
	static char *otoa[] = {
		['+'] = "add",
		['-'] = "sub",
		['*'] = "mul",
		['/'] = "div",
		['%'] = "rem",
		['<'] = "cslt",  /* meeeeh, careful with pointers */
		['l'] = "csle",
		['e'] = "ceq",
		['n'] = "cne",
	};
	Symb sr, s0, s1, sl;
	int o;

	sr.t = Tmp;
	sr.u.n = tmp++;

	switch (n->op) {

	case 'V':
		s0 = lval(n);
		sr.ctyp = s0.ctyp;
		load(sr, s0);
		break;

	case 'N':
		sr.t = Con;
		sr.u.n = n->u.n;
		sr.ctyp = INT;
		break;

	case 'S':
		sr.t = Glo;
		sprintf(sr.u.v, "str%d", n->u.n);
		sr.ctyp = IDIR(INT);
		break;

	case '@':
		s0 = expr(n->l);
		if (KIND(s0.ctyp) != PTR)
			die("dereference of a non-pointer");
		sr.ctyp = DREF(s0.ctyp);
		load(sr, s0);
		break;

	case '&':
		sr = lval(n->l);
		sr.ctyp = IDIR(sr.ctyp);
		break;

	case '=':
		s0 = expr(n->r);
		s1 = lval(n->l);
		sr = s0;
		if (s1.ctyp == LNG &&  s0.ctyp == INT)
			sext(&s0);
		if (s1.ctyp != s0.ctyp)
			die("invalid assignment");
		fprintf(of, "\tstore%c ", irtyp(s1.ctyp));
		goto Args;

	case 'P':
	case 'M':
		o = n->op == 'P' ? '+' : '-';
		sl = lval(n->l);
		s0.t = Tmp;
		s0.u.n = tmp++;
		s0.ctyp = sl.ctyp;
		load(s0, sl);
		s1.t = Con;
		s1.u.n = 1;
		s1.ctyp = INT;
		goto Binop;

	default:
		s0 = expr(n->l);
		s1 = expr(n->r);
		o = n->op;
	Binop:
		sr.ctyp = prom(o, &s0, &s1);
		if (strchr("ne<l", n->op))
			sr.ctyp = INT;
		fprintf(of, "\t");
		psymb(sr);
		fprintf(of, " =%c", irtyp(sr.ctyp));
		fprintf(of, " %s ", otoa[o]);
	Args:
		psymb(s0);
		fprintf(of, ", ");
		psymb(s1);
		fprintf(of, "\n");
		break;

	}
	if (n->op == '-'
	&&  KIND(s0.ctyp) == PTR
	&&  KIND(s1.ctyp) == PTR) {
		fprintf(of, "\t%%t%d =l div ", tmp);
		psymb(sr);
		fprintf(of, ", %d\n", SIZE(DREF(s0.ctyp)));
		sr.u.n = tmp++;
	}
	if (n->op == 'P' || n->op == 'M') {
		fprintf(of, "\tstore%c ", irtyp(sl.ctyp));
		psymb(sr);
		fprintf(of, ", ");
		psymb(sl);
		fprintf(of, "\n");
		sr = s0;
	}
	return sr;
}

Symb
lval(Node *n)
{
	Symb sr;

	switch (n->op) {
	default:
		die("invalid lvalue");
	case 'V':
		sr.t = Var;
		sr.ctyp = varctyp(n->u.v);
		strcpy(sr.u.v, n->u.v);
		break;
	case '@':
		sr = expr(n->l);
		if (KIND(sr.ctyp) != PTR)
			die("dereference of a non-pointer");
		sr.ctyp = DREF(sr.ctyp);
		break;
	}
	return sr;
}

void
stmt(Stmt *s)
{
	int l;
	Symb x;
Again:
	if (!s)
		return;

	switch (s->t) {
	case Expr:
		expr(s->p1);
		break;
	case Seq:
		stmt(s->p1);
		s = s->p2;
		goto Again;
	case If:
		x = expr(s->p1);
		fprintf(of, "\tjnz ");  /* to be clean, a comparison to 0 should be inserted here */
		psymb(x);
		l = lbl;
		lbl += 3;
		fprintf(of, ", @l%d, @l%d\n", l, l+1);
		fprintf(of, "@l%d\n", l);
		stmt(s->p2);
		if (s->p3)
			fprintf(of, "\tjmp @l%d\n", l+2);
		fprintf(of, "@l%d\n", l+1);
		if (s->p3) {
			stmt(s->p3);
			fprintf(of, "@l%d\n", l+2);
		}
		break;
	case While:
		l = lbl;
		lbl += 3;
		fprintf(of, "@l%d\n", l);
		x = expr(s->p1);
		fprintf(of, "\tjnz ");                  /* ditto */
		psymb(x);
		fprintf(of, ", @l%d, @l%d\n", l+1, l+2);
		fprintf(of, "@l%d\n", l+1);
		stmt(s->p2);
		fprintf(of, "\tjmp @l%d\n", l);
		fprintf(of, "@l%d\n", l+2);
		break;
	}
}

Node *
mknode(char op, Node *l, Node *r)
{
	Node *n;

	n = alloc(sizeof *n);
	n->op = op;
	n->l = l;
	n->r = r;
	return n;
}

Node *
mkidx(Node *a, Node *i)
{
	Node *n;

	n = mknode('+', a, i);
	n = mknode('@', n, 0);
	return n;
}

Node *
mkneg(Node *n)
{
	static Node *z;

	if (!z) {
		z = mknode('N', 0, 0);
		z->u.n = 0;
	}
	return mknode('-', z, n);
}

Stmt *
mkstmt(int t, void *p1, void *p2, void *p3)
{
	Stmt *s;

	s = alloc(sizeof *s);
	s->t = t;
	s->p1 = p1;
	s->p2 = p2;
	s->p3 = p3;
	return s;
}

%}

%union {
	Node *n;
	Stmt *s;
	unsigned u;
}

%token <n> NUM
%token <n> STR
%token <n> IDENT
%token PP MM LE GE

%token TINT TLNG
%token IF ELSE WHILE

%right '='
%left '+' '-'
%left '*' '/' '%'
%nonassoc '&'
%left EQ NE
%left '<' '>' LE GE
%nonassoc '['

%type <u> type
%type <s> stmt stmts
%type <n> expr pref post

%%

prog: prot '{' dcls stmts '}'
{
	int i;

	stmt($4);
	fprintf(of, "\tret\n");
	fprintf(of, "}\n\n");
	for (i = 0; i < str; i++)
		fprintf(of, "data $str%d = \"%s\"\n", i, slit[i]);
};

prot: IDENT '(' ')'
{
	varclr();
	lbl = 0;
	tmp = 0;
	fprintf(of, "function $%s() {\n", $1->u.v);
	fprintf(of, "@l%d\n", lbl++);
};

dcls: | dcls type IDENT ';'
{
	int s;
	char *v;

	v = $3->u.v;
	s = SIZE($2);
	varadd(v, $2);
	fprintf(of, "\t%%%s =l alloc%d %d\n", v, s, s);
};

type: type '*' { $$ = IDIR($1); }
    | TINT     { $$ = INT; }
    | TLNG     { $$ = LNG; }
    ;

stmt: ';'                            { $$ = 0; }
    | '{' stmts '}'                  { $$ = $2; }
    | expr ';'                       { $$ = mkstmt(Expr, $1, 0, 0); }
    | WHILE '(' expr ')' stmt        { $$ = mkstmt(While, $3, $5, 0); }
    | IF '(' expr ')' stmt ELSE stmt { $$ = mkstmt(If, $3, $5, $7); }
    | IF '(' expr ')' stmt           { $$ = mkstmt(If, $3, $5, 0); }
    ;

stmts: stmts stmt { $$ = mkstmt(Seq, $1, $2, 0); }
     |            { $$ = 0; }
     ;

expr: pref
    | expr '=' expr     { $$ = mknode('=', $1, $3); }
    | expr '+' expr     { $$ = mknode('+', $1, $3); }
    | expr '-' expr     { $$ = mknode('-', $1, $3); }
    | expr '*' expr     { $$ = mknode('*', $1, $3); }
    | expr '/' expr     { $$ = mknode('/', $1, $3); }
    | expr '%' expr     { $$ = mknode('%', $1, $3); }
    | expr '<' expr     { $$ = mknode('<', $1, $3); }
    | expr '>' expr     { $$ = mknode('<', $3, $1); }
    | expr LE expr      { $$ = mknode('l', $1, $3); }
    | expr GE expr      { $$ = mknode('l', $3, $1); }
    | expr EQ expr      { $$ = mknode('e', $1, $3); }
    | expr NE expr      { $$ = mknode('n', $1, $3); }
    ;

pref: post
    | '-' pref          { $$ = mkneg($2); }
    | '*' pref          { $$ = mknode('@', $2, 0); }
    | '&' pref          { $$ = mknode('&', $2, 0); }
    ;

post: NUM
    | STR
    | IDENT
    | '(' expr ')'      { $$ = $2; }
    | post '[' expr ']' { $$ = mkidx($1, $3); }
    | post PP           { $$ = mknode('P', $1, 0); }
    | post MM           { $$ = mknode('M', $1, 0); }
    ;

%%

int
yylex()
{
	struct {
		char *s;
		int t;
	} kwds[] = {
		{ "int", TINT },
		{ "long", TLNG },
		{ "if", IF },
		{ "else", ELSE },
		{ "while", WHILE },
		{ 0, 0 }
	};
	int i, c, c1, n;
	char v[NString], *p;

	do
		c = getchar();
	while (isspace(c));

	if (c == EOF)
		return 0;

	if (isdigit(c)) {
		n = 0;
		do {
			n *= 10;
			n += c-'0';
			c = getchar();
		} while (isdigit(c));
		ungetc(c, stdin);
		yylval.n = mknode('N', 0, 0);
		yylval.n->u.n = n;
		return NUM;
	}

	if (isalpha(c)) {
		p = v;
		do {
			if (p == &v[NString-1])
				die("ident too long");
			*p++ = c;
			c = getchar();
		} while (isalpha(c));
		*p = 0;
		ungetc(c, stdin);
		for (i=0; kwds[i].s; i++)
			if (strcmp(v, kwds[i].s) == 0)
				return kwds[i].t;
		yylval.n = mknode('V', 0, 0);
		strcpy(yylval.n->u.v, v);
		return IDENT;
	}

	if (c == '"') {
		if (str == NStr)
			die("too many string literals");
		i = 0;
		n = 32;
		p = alloc(n);
		for (i=0;; i++) {
			c = getchar();
			if (c == EOF)
				die("unclosed string literal");
			if (c == '"' && (!i || p[i-1]!='\\'))
				break;
			if (i >= n) {
				p = memcpy(alloc(n*2), p, n);
				n *= 2;
			}
			p[i] = c;
		}
		slit[str] = p;
		yylval.n = mknode('S', 0, 0);
		yylval.n->u.n = str++;
		return STR;
	}

	c1 = getchar();
#define DI(a, b) a + b*256
	switch (DI(c,c1)) {
	case DI('!','='): return NE;
	case DI('=','='): return EQ;
	case DI('<','='): return LE;
	case DI('>','='): return GE;
	case DI('+','+'): return PP;
	case DI('-','-'): return MM;
	}
#undef DI
	ungetc(c1, stdin);

	return c;
}

int
yyerror(char *err)
{
	die("parse error");
	return 0;
}

int
main()
{
	of = stdout;
	if (yyparse() != 0)
		die("parse error");
	return 0;
}
