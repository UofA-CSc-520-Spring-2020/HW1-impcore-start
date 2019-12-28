#include "all.h"
/* env.c S165b */
struct Env {
    Name name;
    Value *loc;
    Env tl;
};
/* env.c S165c */
Value* find(Name name, Env env) {
    for (; env; env = env->tl)
        if (env->name == name)
            return env->loc;
    return NULL;
}
/* env.c S165d */
Env bindalloc(Name name, Value val, Env env) {
    Env newenv = malloc(sizeof(*newenv));
    assert(newenv != NULL);

    newenv->name = name;
    newenv->loc  = allocate(val);
    newenv->tl   = env;
    return newenv;
}
/* env.c S166a */
Env bindalloclist(Namelist xs, Valuelist vs, Env env) {
    for (; xs && vs; xs = xs->tl, vs = vs->tl)
        env = bindalloc(xs->hd, vs->hd, env);
    assert(xs == NULL && vs == NULL);
    return env;
}
/* env.c S166b */
void printenv(Printbuf output, va_list_box *box) {
    char *prefix = " ";

    bprint(output, "{");
    for (Env env = va_arg(box->ap, Env); env; env = env->tl) {
        bprint(output, "%s%n -> %v", prefix, env->name, *env->loc);
        prefix = ", ";
    }
    bprint(output, " }");
}
/* env.c S166c */
void dump_env_names(Env env) {
    for ( ; env; env = env->tl)
        fprint(stdout, "%n\n", env->name);
}
