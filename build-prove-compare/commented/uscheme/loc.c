#include "all.h"
/*
 * Implementation of memory allocation
 * 
 * To allocate a new location, I call [[malloc]]. [*]
 * <loc.c>=
 */
Value* allocate(Value v) {
    Value *loc = malloc(sizeof(*loc));
    assert(loc != NULL);
    *loc = v;
    return loc;
}
/*
 * Memory allocation
 * 
 * To use [[malloc]] requires no special initialization
 * or resetting.
 * <loc.c>=
 */
void initallocate(Env *globals) {
    (void)globals;
}
