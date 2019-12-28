#include "all.h"
/* eval.c ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) */
/* eval.c declarations S149d */
static Valuelist evallist(Explist es, Env env);
/* eval.c 165a */
Value eval(Exp e, Env env) {
    checkoverflow(1000000 * sizeof(char *)); // OMIT
    switch (e->alt) {
    case LITERAL:
        /* evaluate [[e->u.literal]] and return the result 165b */
        return e->u.literal;
    case VAR:   
        /* evaluate [[e->u.var]] and return the result 165c */
        if (find(e->u.var, env) == NULL)
            runerror("name %n not found", e->u.var);
        return *find(e->u.var, env);
    case SET:
        /* evaluate [[e->u.set]] and return the result 166a */
        if (find(e->u.set.name, env) == NULL)
            runerror("set unbound variable %n in %e", e->u.set.name, e);
        return *find(e->u.set.name, env) = eval(e->u.set.exp, env);
    case IFX:
        /* evaluate [[e->u.ifx]] and return the result 169c */
        if (istrue(eval(e->u.ifx.cond, env)))
            return eval(e->u.ifx.truex, env);
        else
            return eval(e->u.ifx.falsex, env);
    case WHILEX:
        /* evaluate [[e->u.whilex]] and return the result 169d */
        while (istrue(eval(e->u.whilex.cond, env)))
            eval(e->u.whilex.body, env);
        return falsev;
    case BEGIN:
        /* evaluate [[e->u.begin]] and return the result 170a */
        {
            Value lastval = falsev;
            for (Explist es = e->u.begin; es; es = es->tl)
                lastval = eval(es->hd, env);
            return lastval;
        }
    case APPLY:
        /* evaluate [[e->u.apply]] and return the result 166c */
        {
            Value     f  = eval    (e->u.apply.fn,      env);
            Valuelist vs = evallist(e->u.apply.actuals, env);

            switch (f.alt) {
            case PRIMITIVE:

              /* apply [[f.u.primitive]] to [[vs]] and return the result 167a */
                return f.u.primitive.function(e, f.u.primitive.tag, vs);
            case CLOSURE:
                /* apply [[f.u.closure]] to [[vs]] and return the result 167b */
                {
                    Namelist xs = f.u.closure.lambda.formals;
                    checkargc(e, lengthNL(xs), lengthVL(vs));
                    return eval(f.u.closure.lambda.body,
                                bindalloclist(xs, vs, f.u.closure.env));
                }
            default:
                runerror("%e evaluates to non-function %v in %e", e->u.apply.fn,
                                                                          f, e);
            }
        }
    case LETX:
        /* evaluate [[e->u.letx]] and return the result 167d */
        switch (e->u.letx.let) {
        case LET:
            /* extend [[env]] by simultaneously binding [[es]] to [[xs]] 168a */
            env = bindalloclist(e->u.letx.xs, evallist(e->u.letx.es, env), env);
            break;
        case LETSTAR:
            /* extend [[env]] by sequentially binding [[es]] to [[xs]] 168b */
            {
                Namelist xs;
                Explist es;

                for (xs = e->u.letx.xs, es = e->u.letx.es;
                     xs && es;
                     xs = xs->tl, es = es->tl)
                    env = bindalloc(xs->hd, eval(es->hd, env), env);
                assert(xs == NULL && es == NULL);
            }
            break;
        case LETREC:
            /* extend [[env]] by recursively binding [[es]] to [[xs]] 169a */
            {
                Namelist xs;

                for (xs = e->u.letx.xs; xs; xs = xs->tl)    
                    env = bindalloc(xs->hd, unspecified(), env);

/* if any expression in [[es]] is not a [[lambda]], reject the [[letrec]] 169b */
                for (Explist es = e->u.letx.es; es; es = es->tl)
                    if (es->hd->alt != LAMBDAX)
                        runerror("letrec tries to bind non-lambda expression %e"
                                                                      , es->hd);
                Valuelist vs = evallist(e->u.letx.es, env);
                for (xs = e->u.letx.xs;
                     xs && vs;
                     xs = xs->tl, vs = vs->tl)
                    *find(xs->hd, env) = vs->hd;
                assert(xs == NULL && vs == NULL);
            }
            break;
        default:
            assert(0);
        }
        return eval(e->u.letx.body, env);
    case LAMBDAX:
        /* evaluate [[e->u.lambdax]] and return the result 166b */
        return mkClosure(e->u.lambdax, env);
    }
    assert(0);
}
/* eval.c 167c */
static Valuelist evallist(Explist es, Env env) {
    if (es == NULL) {
        return NULL;
    } else {
        Value v = eval(es->hd, env);   // enforce uScheme's order of evaluation
        return mkVL(v, evallist(es->tl, env));
    }
}
