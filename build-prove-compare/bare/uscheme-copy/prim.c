#include "all.h"
/* prim.c ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) */
static int32_t divide(int32_t n, int32_t m);
/* prim.c 171c */
static int32_t projectint32(Exp e, Value v) {
    if (v.alt != NUM)
        runerror("in %e, expected an integer, but got %v", e, v);
    return v.u.num;
}
/* prim.c 172a */
Value arith(Exp e, int tag, Valuelist args) {
    checkargc(e, 2, lengthVL(args));
    int32_t n = projectint32(e, nthVL(args, 0));
    int32_t m = projectint32(e, nthVL(args, 1));

    switch (tag) {
    case PLUS:
        checkarith('+', n, m, 32); // OMIT
        return mkNum(n + m);
    case MINUS:
        checkarith('-', n, m, 32); // OMIT
        return mkNum(n - m);
    case TIMES:
        checkarith('*', n, m, 32); // OMIT
        return mkNum(n * m);
    case DIV:
        if (m==0)
            runerror("division by zero");
        checkarith('/', n, m, 32); // OMIT
        return mkNum(divide(n, m));  // round to minus infinity
    case LT:
        return mkBoolv(n < m);
    case GT:
        return mkBoolv(n > m);
    default:
        assert(0);
    }
}
/* prim.c 172b */
/* version of cons() in which C variables are treated as machine registers */
Value cons(Value v, Value w) { 
    pushreg(&v);
    pushreg(&w);
    Value *car = allocate(v);
    Value pair = mkPair(car, car); // temporary; preserves invariant
    car = NULL;
    pushreg(&pair);
    pair.u.pair.cdr = allocate(w);
    popreg(&pair);
    popreg(&w);
    popreg(&v);
    cyclecheck(&pair);
    return pair;
}
/* prim.c 173a */
Value unary(Exp e, int tag, Valuelist args) {
    checkargc(e, 1, lengthVL(args));
    Value v = nthVL(args, 0);
    switch (tag) {
    case NULLP:
        return mkBoolv(v.alt == NIL);
    case CAR:
        if (v.alt == NIL)
            runerror("in %e, car applied to empty list", e);
        else if (v.alt != PAIR)
            runerror("car applied to non-pair %v in %e", v, e);
        return *v.u.pair.car;
    case PRINTU:
        if (v.alt != NUM)
            runerror("printu applied to non-number %v in %e", v, e);
        print_utf8(v.u.num);
        return v;
    case ERROR:
        runerror("%v", v);
        return v;
    /* other cases for unary primitives S154a */
    case BOOLEANP:
        return mkBoolv(v.alt == BOOLV);
    case NUMBERP:
        return mkBoolv(v.alt == NUM);
    case SYMBOLP:
        return mkBoolv(v.alt == SYM);
    case PAIRP:
        return mkBoolv(v.alt == PAIR);
    case PROCEDUREP:
        return mkBoolv(v.alt == CLOSURE || v.alt == PRIMITIVE);
    case CDR:
        if (v.alt == NIL)
            runerror("in %e, cdr applied to empty list", e);
        else if (v.alt != PAIR)
            runerror("cdr applied to non-pair %v in %e", v, e);
        return *v.u.pair.cdr;
    case PRINTLN:
        print("%v\n", v);
        return v;
    case PRINT:
        print("%v", v);
        return v;
    default:
        assert(0);
    }
}
/* prim.c S152a */
static int32_t divide(int32_t n, int32_t m) {
    if (n >= 0)
        if (m >= 0)
            return n / m;
        else
            return -(( n - m - 1) / -m);
    else
        if (m >= 0)
            return -((-n + m - 1) /  m);
        else
            return -n / -m;
}
/* prim.c S152d */
Value binary(Exp e, int tag, Valuelist args) {
    checkargc(e, 2, lengthVL(args));
    Value v = nthVL(args, 0);
    Value w = nthVL(args, 1);

    switch (tag) {
    case CONS: 
        return cons(v, w);
    case EQ:   
        return equalatoms(v, w);
    default:
        assert(0);
    }
}
/* prim.c S153a */
Value equalatoms(Value v, Value w) {
    if (v.alt != w.alt)
        return falsev;

    switch (v.alt) {
    case NUM:
        return mkBoolv(v.u.num   == w.u.num);
    case BOOLV:
        return mkBoolv(v.u.boolv == w.u.boolv);
    case SYM:
        return mkBoolv(v.u.sym   == w.u.sym);
    case NIL:
        return truev;
    default:
        return falsev;
    }
}
