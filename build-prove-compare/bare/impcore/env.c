#include "all.h"
/* env.c 57b */
struct Valenv {
    Namelist  xs;
    Valuelist vs;
    // invariant: lists have the same length
};
/* env.c 57c */
Valenv mkValenv(Namelist xs, Valuelist vs) {
    Valenv e = malloc(sizeof(*e));
    assert(e != NULL);
    assert(lengthNL(xs) == lengthVL(vs));
    e->xs = xs;
    e->vs = vs;
    return e;
}
/* env.c 58a */
static Value* findval(Name x, Valenv env) {
    Namelist  xs;
    Valuelist vs;

    for (xs=env->xs, vs=env->vs; xs && vs; xs=xs->tl, vs=vs->tl)
        if (x == xs->hd)
            return &vs->hd;
    return NULL;
}
/* env.c 58b */
bool isvalbound(Name name, Valenv env) {
    return findval(name, env) != NULL;
}
/* env.c 58c */
Value fetchval(Name name, Valenv env) {
    Value *vp = findval(name, env);
    assert(vp != NULL);
    return *vp;
}
/* env.c 58d */
void bindval(Name name, Value val, Valenv env) {
    Value *vp = findval(name, env);
    if (vp != NULL)
        *vp = val;              // safe optimization
    else {
        env->xs = mkNL(name, env->xs);
        env->vs = mkVL(val,  env->vs);
    }
}
/* env.c S143b */
struct Funenv {
    Namelist xs;
    Funlist funs;
    // invariant: both lists are the same length
};
/* env.c S143c */
Funenv mkFunenv(Namelist xs, Funlist funs) {
    Funenv env = malloc(sizeof *env);
    assert(env != NULL);
    assert(lengthNL(xs) == lengthFL(funs));
    env->xs = xs;
    env->funs = funs;
    return env;
}
/* env.c S143d */
static Fun* findfun(Name name, Funenv env) {
    Namelist xs  = env->xs;
    Funlist funs = env->funs;

    for ( ; xs && funs; xs = xs->tl, funs = funs->tl)
        if (name == xs->hd)
            return &funs->hd;
    return NULL;
}
/* env.c S143e */
bool isfunbound(Name name, Funenv env) {
    return findfun(name, env) != NULL;
}
/* env.c S143f */
Fun fetchfun(Name name, Funenv env) {
    Fun *fp = findfun(name, env);
    assert(fp != NULL);
    return *fp;
}
/* env.c S144a */
void bindfun(Name name, Fun fun, Funenv env) {
    Fun *fp = findfun(name, env);
    if (fp != NULL)
        *fp = fun;              // safe optimization
    else {
        env->xs   = mkNL(name, env->xs);
        env->funs = mkFL(fun,  env->funs);
    }
}
/* env.c S144b */
void dump_fenv_names(Funenv env) {
    Namelist xs;
    if (env)
        for (xs = env->xs; xs; xs = xs->tl)
            print("%n\n", xs->hd);
}
