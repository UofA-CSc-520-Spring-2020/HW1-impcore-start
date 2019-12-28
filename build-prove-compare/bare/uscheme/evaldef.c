#include "all.h"
/* evaldef.c 170b */
Env evaldef(Def d, Env env, Echo echo) {
    switch (d->alt) {
    case VAL:
        /* evaluate [[val]] binding and return new environment 170c */
        {
            if (find(d->u.val.name, env) == NULL)
                env = bindalloc(d->u.val.name, unspecified(), env);
            Value v = eval(d->u.val.exp, env);
            *find(d->u.val.name, env) = v;

/* if [[echo]] calls for printing, print either [[v]] or the bound name S149e */
            if (echo == ECHOES) {
                if (d->u.val.exp->alt == LAMBDAX)
                    print("%n\n", d->u.val.name);
                else
                    print("%v\n", v);
            }
            return env;
        }
    case EXP:

/* evaluate expression, store the result in [[it]], and return new environment 171a */
        {
            Value v = eval(d->u.exp, env);
            Value *itloc = find(strtoname("it"), env);
            /* if [[echo]] calls for printing, print [[v]] S149f */
            if (echo == ECHOES)
                print("%v\n", v);
            if (itloc == NULL) {
                return bindalloc(strtoname("it"), v, env);
            } else {
                *itloc = v;
                return env;
            }
        }
    case DEFINE:
        /* evaluate function definition and return new environment 171b */
        return evaldef(mkVal(d->u.define.name, mkLambdax(d->u.define.lambda)),
                       env, echo);
    case DEFS:                                                     /*OMIT*/
        for (Deflist ds = d->u.defs; ds != NULL; ds = ds->tl)      /*OMIT*/
            env = evaldef(ds->hd, env, echo);                      /*OMIT*/
        return env;                                                /*OMIT*/
    }
    assert(0);
    return NULL;
}
/* evaldef.c S150a */
void readevalprint(XDefstream xdefs, Env *envp, Echo echo) {
    UnitTestlist pending_unit_tests = NULL;

    for (XDef d = getxdef(xdefs); d; d = getxdef(xdefs))
        switch (d->alt) {
        case DEF:
            *envp = evaldef(d->u.def, *envp, echo);
            break;
        case USE:
            /* read in a file and update [[*envp]] S150b */
            {
                const char *filename = nametostr(d->u.use);
                FILE *fin = fopen(filename, "r");
                if (fin == NULL)
                    runerror("cannot open file \"%s\"", filename);
                readevalprint(filexdefs(filename, fin, NO_PROMPTS), envp, echo);
                fclose(fin);
            }
            break;
        case TEST:
            pending_unit_tests = mkUL(d->u.test, pending_unit_tests);
            break;
        default:
            assert(0);
        }

    process_tests(pending_unit_tests, *envp);
}
