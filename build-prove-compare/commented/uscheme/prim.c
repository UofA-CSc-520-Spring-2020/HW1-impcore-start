#include "all.h"
/*
 * Arithmetic primitives
 * 
 * Each arithmetic primitive expects two integer
 * arguments, so we need to project micro-Scheme values
 * into C integers. The projection function
 * [[projectint32]] takes not only a value but also an
 * expression, so if the argument is not an integer,
 * [[projectint32]] can issue an informative error
 * message.
 * <prim.c ((elided))>=
 */
static int32_t divide(int32_t n, int32_t m);
/*
 * <prim.c>=
 */
static int32_t projectint32(Exp e, Value v) {
    if (v.alt != NUM)
        runerror("in %e, expected an integer, but got %v", e, v);
    return v.u.num;
}
/*
 * Function [[arith]] first converts its arguments to
 * integers, then does a [[switch]] to determine what to
 * do with those integers. The result is converted back
 * to a micro-Scheme value by either [[mkNum]] or
 * [[mkBool]], both of which are generated automatically
 * from the definition of [[Value]] in code chunk [->]. 
 * [*]
 * <prim.c>=
 */
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
/*
 * Other binary primitives
 * 
 * micro-Scheme has two binary primitives that do not
 * require integer arguments: [[cons]] and [[=]].
 * The implementation of [[=]] is relegated to the
 * Supplement, but the implementation of [[cons]] is
 * here. Because S-expressions are a recursive type, the
 * representation of a cons cell must contain pointers
 * to S-expressions, not S-expressions themselves. Every
 * [[cons]] must therefore allocate fresh locations for
 * the pointers. This behavior makes [[cons]] a major
 * source of allocation in micro-Scheme programs. [
 * In~full \scheme, a cons cell is typically represented
 * by a pointer to an object allocated on the heap, so
 * [[cons]] requires only one allocation, not two.] [*]
 * <prim.c>=
 */
Value cons(Value v, Value w) {
    return mkPair(allocate(v), allocate(w));
}
/*
 * Unary primitives
 * 
 * Unary primitives are implemented here. Most of the
 * cases are relegated to the Supplement.[*]
 * <prim.c>=
 */
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
    /*
     * <other cases for unary primitives>=
     */
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
/*
 * We need special support for division, because while
 * micro-Scheme requires that division round toward
 * minus infinity, C guarantees only that dividing
 * positive operands rounds toward zero.
 * <prim.c>=
 */
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
/*
 * <prim.c>=
 */
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
/*
 * The implementation of equality is not completely
 * trivial. Two values are [[=]] only if they are the
 * same number, the same boolean, the same symbol, or
 * both the empty list. Because all these values are
 * atoms, I call the C function [[equalatoms]].
 * A different function, [[equalpairs]], is used in \
 * crefschemea.equalpairs to implement [[check-expect]].
 * [*]
 * <prim.c>=
 */
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
