#include "all.h"
/* loc.c 173b */
Value* allocate(Value v) {
    Value *loc = malloc(sizeof(*loc));
    assert(loc != NULL);
    *loc = v;
    return loc;
}
/* loc.c S155c */
void initallocate(Env *globals) {
    (void)globals;
}
