#include "all.h"
/* loc.c 304f */
Value* allocate(Value v) {
    Value *loc;

    pushreg(&v);
    loc = allocloc();
    popreg(&v);
    assert(loc != NULL);
    *loc = v;
    return loc;
}
/* loc.c S207a */
int gammadesired(int defaultval, int minimum) {
    assert(roots.globals.user != NULL);
    Value *gammaloc = find(strtoname("&gamma-desired"), *roots.globals.user);
    if (gammaloc && gammaloc->alt == NUM)
        return gammaloc->u.num > minimum ? gammaloc->u.num : minimum;
    else
        return defaultval;
}
/* loc.c S210d */
extern void printfinalstats(void);
void initallocate(Env *globals) {
    gc_debug_init();
    roots.globals.user                   = globals;
    roots.globals.internal.pending_tests = NULL;
    roots.stack     = emptystack();
    roots.registers = NULL;
    atexit(printfinalstats);
}
