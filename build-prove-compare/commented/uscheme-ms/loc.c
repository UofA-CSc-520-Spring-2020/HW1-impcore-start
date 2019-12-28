#include "all.h"
/*
 * Using the heap interface: micro-Scheme allocation
 * 
 * Here's how I use the heap interface to implement the
 * allocation interface defined in Chapter [->]. The
 * copying and mark-and-sweep collectors use different
 * implementations of [[allocloc]], but they share this
 * implementation of [[allocate]]. [*]
 * <loc.c>=
 */
Value* allocate(Value v) {
    Value *loc;

    pushreg(&v);
    loc = allocloc();
    popreg(&v);
    assert(loc != NULL);
    *loc = v;
    return loc;
}
/*
 * The interesting part is the [[pushreg]] and
 * [[popreg]]. Because if [[v]] happens to be a [[cons]]
 * cell, and if [[allocloc]] happens to call the garbage
 * collector, we have to prevent the garbage collector
 * from reclaiming the locations pointed to by
 * [[v.u.pair.car]] and [[v.u.pair.cdr]]. The call to
 * [[pushreg]] makes [[v]] a ``machine register'' and
 * ensures that the collector treats it as a root. And
 * if the collector happens to move [[v]]'s [[car]] and
 * [[cdr]], it updates [[v]]'s internal pointers to
 * point to the new locations.
 */

/*
 * Access to the desired size of the heap
 * 
 * To control the size of the heap, we might want to use
 * the micro-Scheme variable [[ --- gamma-desired]], as
 * described in Exercises [->] and [->]. This routine
 * gets the value of that variable. [*]
 * <loc.c>=
 */
int gammadesired(int defaultval, int minimum) {
    assert(roots.globals.user != NULL);
    Value *gammaloc = find(strtoname("&gamma-desired"), *roots.globals.user);
    if (gammaloc && gammaloc->alt == NUM)
        return gammaloc->u.num > minimum ? gammaloc->u.num : minimum;
    else
        return defaultval;
}
/*
 * Collector initialization uses the ANSI C function
 * [[atexit]] to make sure that before the program
 * exits, final garbage-collection statistics are
 * printed.
 * <loc.c>=
 */
extern void printfinalstats(void);
void initallocate(Env *globals) {
    gc_debug_init();
    roots.globals.user                   = globals;
    roots.globals.internal.pending_tests = NULL;
    roots.stack     = emptystack();
    roots.registers = NULL;
    atexit(printfinalstats);
}
