#ifndef X /* amd64 */
	#define X(NMemArgs, SetsZeroFlag, LeavesFlags)
#endif

#define T(a,b,c,d,e,f,g,h) {                          \
	{[Kw]=K##a, [Kl]=K##b, [Ks]=K##c, [Kd]=K##d}, \
	{[Kw]=K##e, [Kl]=K##f, [Ks]=K##g, [Kd]=K##h}  \
}


/*********************/
/* PUBLIC OPERATIONS */
/*********************/

/* Arithmetic and Bits */
O(add,     T(w,l,s,d, w,l,s,d), 1) X(2, 1, 0)
O(sub,     T(w,l,s,d, w,l,s,d), 1) X(2, 1, 0)
O(div,     T(w,l,s,d, w,l,s,d), 1) X(0, 0, 0)
O(rem,     T(w,l,e,e, w,l,e,e), 1) X(0, 0, 0)
O(udiv,    T(w,l,e,e, w,l,e,e), 1) X(0, 0, 0)
O(urem,    T(w,l,e,e, w,l,e,e), 1) X(0, 0, 0)
O(mul,     T(w,l,s,d, w,l,s,d), 1) X(2, 0, 0)
O(and,     T(w,l,e,e, w,l,e,e), 1) X(2, 1, 0)
O(or,      T(w,l,e,e, w,l,e,e), 1) X(2, 1, 0)
O(xor,     T(w,l,e,e, w,l,e,e), 1) X(2, 1, 0)
O(sar,     T(w,l,e,e, w,w,e,e), 1) X(1, 1, 0)
O(shr,     T(w,l,e,e, w,w,e,e), 1) X(1, 1, 0)
O(shl,     T(w,l,e,e, w,w,e,e), 1) X(1, 1, 0)

/* Comparisons */
O(ceqw,    T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)
O(cnew,    T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)
O(csgew,   T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)
O(csgtw,   T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)
O(cslew,   T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)
O(csltw,   T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)
O(cugew,   T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)
O(cugtw,   T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)
O(culew,   T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)
O(cultw,   T(w,w,e,e, w,w,e,e), 1) X(0, 1, 0)

O(ceql,    T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)
O(cnel,    T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)
O(csgel,   T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)
O(csgtl,   T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)
O(cslel,   T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)
O(csltl,   T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)
O(cugel,   T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)
O(cugtl,   T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)
O(culel,   T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)
O(cultl,   T(l,l,e,e, l,l,e,e), 1) X(0, 1, 0)

O(ceqs,    T(s,s,e,e, s,s,e,e), 1) X(0, 1, 0)
O(cges,    T(s,s,e,e, s,s,e,e), 1) X(0, 1, 0)
O(cgts,    T(s,s,e,e, s,s,e,e), 1) X(0, 1, 0)
O(cles,    T(s,s,e,e, s,s,e,e), 1) X(0, 1, 0)
O(clts,    T(s,s,e,e, s,s,e,e), 1) X(0, 1, 0)
O(cnes,    T(s,s,e,e, s,s,e,e), 1) X(0, 1, 0)
O(cos,     T(s,s,e,e, s,s,e,e), 1) X(0, 1, 0)
O(cuos,    T(s,s,e,e, s,s,e,e), 1) X(0, 1, 0)

O(ceqd,    T(d,d,e,e, d,d,e,e), 1) X(0, 1, 0)
O(cged,    T(d,d,e,e, d,d,e,e), 1) X(0, 1, 0)
O(cgtd,    T(d,d,e,e, d,d,e,e), 1) X(0, 1, 0)
O(cled,    T(d,d,e,e, d,d,e,e), 1) X(0, 1, 0)
O(cltd,    T(d,d,e,e, d,d,e,e), 1) X(0, 1, 0)
O(cned,    T(d,d,e,e, d,d,e,e), 1) X(0, 1, 0)
O(cod,     T(d,d,e,e, d,d,e,e), 1) X(0, 1, 0)
O(cuod,    T(d,d,e,e, d,d,e,e), 1) X(0, 1, 0)

/* Memory */
O(storeb,  T(w,e,e,e, m,e,e,e), 0) X(0, 0, 1)
O(storeh,  T(w,e,e,e, m,e,e,e), 0) X(0, 0, 1)
O(storew,  T(w,e,e,e, m,e,e,e), 0) X(0, 0, 1)
O(storel,  T(l,e,e,e, m,e,e,e), 0) X(0, 0, 1)
O(stores,  T(s,e,e,e, m,e,e,e), 0) X(0, 0, 1)
O(stored,  T(d,e,e,e, m,e,e,e), 0) X(0, 0, 1)

O(loadsb,  T(m,m,e,e, x,x,e,e), 0) X(0, 0, 1)
O(loadub,  T(m,m,e,e, x,x,e,e), 0) X(0, 0, 1)
O(loadsh,  T(m,m,e,e, x,x,e,e), 0) X(0, 0, 1)
O(loaduh,  T(m,m,e,e, x,x,e,e), 0) X(0, 0, 1)
O(loadsw,  T(m,m,e,e, x,x,e,e), 0) X(0, 0, 1)
O(loaduw,  T(m,m,e,e, x,x,e,e), 0) X(0, 0, 1)
O(load,    T(m,m,m,m, x,x,x,x), 0) X(0, 0, 1)

/* Extensions and Truncations */
O(extsb,   T(w,w,e,e, x,x,e,e), 1) X(0, 0, 1)
O(extub,   T(w,w,e,e, x,x,e,e), 1) X(0, 0, 1)
O(extsh,   T(w,w,e,e, x,x,e,e), 1) X(0, 0, 1)
O(extuh,   T(w,w,e,e, x,x,e,e), 1) X(0, 0, 1)
O(extsw,   T(e,w,e,e, e,x,e,e), 1) X(0, 0, 1)
O(extuw,   T(e,w,e,e, e,x,e,e), 1) X(0, 0, 1)

O(exts,    T(e,e,e,s, e,e,e,x), 1) X(0, 0, 1)
O(truncd,  T(e,e,d,e, e,e,x,e), 1) X(0, 0, 1)
O(stosi,   T(s,s,e,e, x,x,e,e), 1) X(0, 0, 1)
O(dtosi,   T(d,d,e,e, x,x,e,e), 1) X(0, 0, 1)
O(swtof,   T(e,e,w,w, e,e,x,x), 1) X(0, 0, 1)
O(sltof,   T(e,e,l,l, e,e,x,x), 1) X(0, 0, 1)
O(cast,    T(s,d,w,l, x,x,x,x), 1) X(0, 0, 1)

/* Stack Allocation */
O(alloc4,  T(e,l,e,e, e,x,e,e), 0) X(0, 0, 0)
O(alloc8,  T(e,l,e,e, e,x,e,e), 0) X(0, 0, 0)
O(alloc16, T(e,l,e,e, e,x,e,e), 0) X(0, 0, 0)

/* Variadic Function Helpers */
O(vaarg,   T(m,m,m,m, x,x,x,x), 0) X(0, 0, 0)
O(vastart, T(m,e,e,e, x,e,e,e), 0) X(0, 0, 0)

O(copy,    T(w,l,s,d, x,x,x,x), 0) X(0, 0, 1)


/****************************************/
/* INTERNAL OPERATIONS (keep nop first) */
/****************************************/

/* Miscellaneous and Architecture-Specific Operations */
O(nop,     T(x,x,x,x, x,x,x,x), 0) X(0, 0, 1)
O(addr,    T(m,m,e,e, x,x,e,e), 0) X(0, 0, 1)
O(swap,    T(w,l,s,d, w,l,s,d), 0) X(1, 0, 0)
O(sign,    T(w,l,e,e, x,x,e,e), 0) X(0, 0, 0)
O(salloc,  T(e,l,e,e, e,x,e,e), 0) X(0, 0, 0)
O(xidiv,   T(w,l,e,e, x,x,e,e), 0) X(1, 0, 0)
O(xdiv,    T(w,l,e,e, x,x,e,e), 0) X(1, 0, 0)
O(xcmp,    T(w,l,s,d, w,l,s,d), 0) X(1, 1, 0)
O(xtest,   T(w,l,e,e, w,l,e,e), 0) X(1, 1, 0)
O(acmp,    T(w,l,e,e, w,l,e,e), 0) X(0, 0, 0)
O(acmn,    T(w,l,e,e, w,l,e,e), 0) X(0, 0, 0)
O(afcmp,   T(e,e,s,d, e,e,s,d), 0) X(0, 0, 0)

/* Arguments, Parameters, and Calls */
O(par,     T(x,x,x,x, x,x,x,x), 0) X(0, 0, 0)
O(parc,    T(e,x,e,e, e,x,e,e), 0) X(0, 0, 0)
O(pare,    T(e,x,e,e, e,x,e,e), 0) X(0, 0, 0)
O(arg,     T(w,l,s,d, x,x,x,x), 0) X(0, 0, 0)
O(argc,    T(e,x,e,e, e,l,e,e), 0) X(0, 0, 0)
O(arge,    T(e,l,e,e, e,x,e,e), 0) X(0, 0, 0)
O(argv,    T(x,x,x,x, x,x,x,x), 0) X(0, 0, 0)
O(call,    T(m,m,m,m, x,x,x,x), 0) X(0, 0, 0)

/* Flags Setting */
O(flagieq,  T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagine,  T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagisge, T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagisgt, T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagisle, T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagislt, T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagiuge, T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagiugt, T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagiule, T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagiult, T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagfeq,  T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagfge,  T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagfgt,  T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagfle,  T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagflt,  T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagfne,  T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagfo,   T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)
O(flagfuo,  T(x,x,e,e, x,x,e,e), 0) X(0, 0, 1)


#undef T
#undef X
#undef O

/*
| column -t -o ' '
*/
