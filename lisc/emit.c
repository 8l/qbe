#include "lisc.h"


static void
eref(Ref r, Fn *fn, FILE *f)
{
	Const *c;

	switch (rtype(r)) {
	case RSym:
		assert(fn->sym[r.val].type == SReg);
		fprintf(f, "%%%s", fn->sym[r.val].name);
		break;
	case RSlot:
		fprintf(f, "-%d(%%rbp)", 8 * r.val);
		break;
	case RConst:
		c = &fn->cst[r.val];
		switch (c->type) {
		case CAddr:
			fprintf(f, "$%s", c->label);
			if (c->val)
				fprintf(f, "%+"PRIi64, c->val);
			break;
		case CNum:
			fprintf(f, "$%"PRId64, c->val);
			break;
		default:
			diag("emitref: invalid constant");
		}
		break;
	default:
		diag("emitref: invalid reference");
	}
}

static void
eop(char *op, Ref a, Ref b, Fn *fn, FILE *f)
{
	fprintf(f, "\t%s ", op);
	eref(a, fn, f);
	if (!req(b, R)) {
		fprintf(f, ", ");
		eref(b, fn, f);
	}
	fprintf(f, "\n");
}

static void
eins(Ins i, Fn *fn, FILE *f)
{
	static char *opi[] = {
		[OAdd] = "add",
		[OSub] = "sub",
	};

	switch (i.op) {
	case OAdd:
	case OSub:
		if (!req(i.to, i.arg[0]))
			eop("mov", i.arg[0], i.to, fn, f);
		eop(opi[i.op], i.arg[1], i.to, fn, f);
		break;
	case OStore:
		i.to = i.arg[1];
		/* fall through */
	case OCopy:
	case OLoad:
		if (!req(i.arg[0], i.to))
			eop("mov", i.arg[0], i.to, fn, f);
		break;
	case OSwap:
		eop("xchg", i.arg[0], i.arg[1], fn, f);
		break;
	case OIACltd:
		fprintf(f, "\tcltd\n");
		break;
	case OIADiv:
		eop("idiv", i.arg[0], R, fn, f);
		break;
	case ONop:
		break;
	default:
		diag("emit: unhandled instruction");
	}
}

void
emitfn(Fn *fn, FILE *f)
{
	char *js;
	Blk *b, *s;
	Ins *i;

	fprintf(f,
		".text\n"
		".globl liscf\n"
		".type liscf, @function\n"
		"liscf:\n"
		"\tpush %%rbp\n"
		"\tmov %%rsp, %%rbp\n"
		"\tsub $%u, %%rsp\n",
		fn->nspill * 8
	);
	for (b=fn->start; b; b=b->link) {
		fprintf(f, ".L%s:\n", b->name);
		for (i=b->ins; i-b->ins < b->nins; i++)
			eins(*i, fn, f);
		switch (b->jmp.type) {
		case JRet:
			fprintf(f,
				"\tleave\n"
				"\tret\n"
			);
			break;
		case JJmp:
			if (b->s1 != b->link)
				fprintf(f, "\tjmp .L%s\n", b->s1->name);
			break;
		case JJez:
			if (b->s1 == b->link) {
				js = "jnz";
				s = b->s2;
			} else if (b->s2 == b->link) {
				js = "jz";
				s = b->s1;
			} else
				diag("emit: unhandled jump (1)");
			eop("test", b->jmp.arg, b->jmp.arg, fn, f);
			fprintf(f, "\t%s .L%s\n", js, s->name);
			break;
		default:
			diag("emit: unhandled jump (2)");
		}
	}

}
