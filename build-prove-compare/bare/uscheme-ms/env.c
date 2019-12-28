#include "all.h"
/* env.c S165b */
Value* find(Name name, Env env) {
    for (; env; env = env->tl)
        if (env->name == name)
            return env->loc;
    return NULL;
}
/* env.c S165c */
void printenv(Printbuf output, va_list_box *box) {
    char *prefix = " ";

    bprint(output, "{");
    for (Env env = va_arg(box->ap, Env); env; env = env->tl) {
        bprint(output, "%s%n -> %v", prefix, env->name, *env->loc);
        prefix = ", ";
    }
    bprint(output, " }");
}
/* env.c S165d */
void dump_env_names(Env env) {
    for ( ; env; env = env->tl)
        fprint(stdout, "%n\n", env->name);
}
/* env.c S211b */
Env bindalloc(Name name, Value val, Env env) {
    Env newenv = malloc(sizeof(*newenv));
    assert(newenv != NULL);

    newenv->name = name;
    pushcontext(mkLetxenvStruct(env), roots.stack);
    newenv->loc  = allocate(val);
    popframe(roots.stack);
    newenv->tl   = env;
    return newenv;
}
/* env.c S212a */
Env bindalloclist(Namelist xs, Valuelist vs, Env env) {
    Valuelist oldvals = vs;
    pushregs(oldvals);
    for (; xs && vs; xs = xs->tl, vs = vs->tl)
        env = bindalloc(xs->hd, vs->hd, env);
    popregs(oldvals);
    return env;
}
