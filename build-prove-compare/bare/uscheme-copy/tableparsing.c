#include "all.h"
/* tableparsing.c S36 */
/* private function prototypes for parsing S42b */
static Namelist parsenamelist(Parlist ps, ParsingContext context);
/* private function prototypes for parsing S44g */
static bool rowmatches(struct ParserRow *row, Name first);
/* private function prototypes for parsing S51b */
void *name_error(Par bad, struct ParsingContext *context); 
                     /* expected a name, but got something else */
/* tableparsing.c S39c */
struct ParserState mkParserState(Par p, Sourceloc source) {
    assert(p->alt == LIST);
    assert(source != NULL && source->sourcename != NULL);
    struct ParserState s;
    s.input          = p->u.list;
    s.context.par    = p;
    s.context.source = source;
    s.context.name   = NULL;
    s.nparsed        = 0;
    return s;
}
/* tableparsing.c S40d */
void halfshift(ParserState s) {
    assert(s->input);
    s->input = s->input->tl;
    assert(s->nparsed < MAXCOMPS);
}
/* tableparsing.c S41a */
ParserResult sExp(ParserState s) {
    if (s->input == NULL) {
        return INPUT_EXHAUSTED;
    } else {
        Par p = s->input->hd;
        halfshift(s);
        s->components[s->nparsed++].exp = parseexp(p, s->context.source);
        return PARSED;
    }
}
/* tableparsing.c S41b */
ParserResult sExps(ParserState s) {
    Explist es = parseexplist(s->input, s->context.source);
    assert(s->nparsed < MAXCOMPS);
    s->input = NULL;
    s->components[s->nparsed++].exps = es;
    return PARSED;
}
/* tableparsing.c S41d */
ParserResult sName(ParserState s) {
    if (s->input == NULL) {
        return INPUT_EXHAUSTED;
    } else {
        Par p = s->input->hd;
        halfshift(s);
        s->components[s->nparsed++].name = parsename(p, &s->context);
        return PARSED;
    }
}
/* tableparsing.c S42a */
ParserResult sNamelist(ParserState s) {
    if (s->input == NULL) {
        return INPUT_EXHAUSTED;
    } else {
        Par p = s->input->hd;
        switch (p->alt) {
        case ATOM:
            synerror(s->context.source, "%p: usage: (define fun (formals) body)"
                                                                               ,
                     s->context.par);
        case LIST:
            halfshift(s);
            s->components[s->nparsed++].names = parsenamelist(p->u.list, &s->
                                                                       context);
            return PARSED;
        }
        assert(0);
    }
}
/* tableparsing.c S42c */
ParserResult stop(ParserState state) {
    if (state->input == NULL)
        return STOP_PARSING;
    else
        return INPUT_LEFTOVER;
}    
/* tableparsing.c S42e */
ParserResult setcontextname(ParserState s) {
    assert(s->nparsed > 0);
    s->context.name = s->components[s->nparsed-1].name;
    return PARSED;
}
/* tableparsing.c S43a */
ParserResult sLocals(ParserState s) {
    Par p = s->input ? s->input->hd : NULL;  // useful abbreviation
    if (/* [[Par p]] represents a list beginning with keyword [[locals]] S43b */
        p != NULL && p->alt == LIST && p->u.list != NULL &&
        p->u.list->hd->alt == ATOM && p->u.list->hd->u.atom == strtoname(
                                                                    "locals")) {
        struct ParsingContext context;
        context.name = strtoname("locals");
        context.par = p;
        halfshift(s);
        s->components[s->nparsed++].names = parsenamelist(p->u.list->tl, &
                                                                       context);
        return PARSED;
    } else {        
        s->components[s->nparsed++].names = NULL;
        return PARSED;
    }
}
/* tableparsing.c S44a */
void rowparse(struct ParserRow *row, ParserState s) {
    ShiftFun *f = &row->shifts[0];

    for (;;) {
        ParserResult r = (*f)(s);
        switch (r) {
        case PARSED:          f++; break;
        case STOP_PARSING:    return;
        case INPUT_EXHAUSTED: 
        case INPUT_LEFTOVER:  
        case BAD_INPUT:       usage_error(row->code, r, &s->context);
        }
    }
}
/* tableparsing.c S44d */
struct ParserRow *tableparse(ParserState s, ParserTable t) {
    if (s->input == NULL)
        synerror(s->context.source, "%p: unquoted empty parentheses", s->
                                                                   context.par);

    Name first = s->input->hd->alt == ATOM ? s->input->hd->u.atom : NULL;

                          // first Par in s->input, if it is present and an atom

    unsigned i;  // to become the index of the matching row in ParserTable t
    for (i = 0; !rowmatches(&t[i], first); i++) 
        ;

/* adjust the state [[s]] so it's ready to start parsing using row [[t[i]]] S45a */
    if (t[i].keyword) {
        assert(first != NULL);
        s->input = s->input->tl;
        s->context.name = first;
    }
    rowparse(&t[i], s);
    return &t[i];
}
/* tableparsing.c S44f */
static bool rowmatches(struct ParserRow *row, Name first) {
    return row->keyword == NULL || strtoname(row->keyword) == first;
}
/* tableparsing.c S46a */
Exp parseexp(Par p, Sourceloc source) {
    switch (p->alt) {
    case ATOM:

/* if [[p->u.atom]] is a reserved word, call [[synerror]] with [[source]] S49a */
        for (struct ParserRow *entry = exptable; entry->keyword != NULL; entry++
                                                                               )
            if (p->u.atom == strtoname(entry->keyword))
                synerror(source, "%n is a reserved word and may not be used "
                         "to name a variable or function", p->u.atom);
        for (struct ParserRow *entry = xdeftable; entry->keyword != NULL; entry
                                                                             ++)
            if (p->u.atom == strtoname(entry->keyword))
                synerror(source, "%n is a reserved word and may not be used "
                         "to name a variable or function", p->u.atom);
        return exp_of_atom(source, p->u.atom);
    case LIST: 
        {   struct ParserState s = mkParserState(p, source);
            struct ParserRow *row = tableparse(&s, exptable);
            if (row->code == EXERCISE) {
                synerror(source, "implementation of %n is left as an exercise",
                         s.context.name);
            } else {
                Exp e = reduce_to_exp(row->code, s.components);
                check_exp_duplicates(source, e);
                return e;
            }
        }
    }
    assert(0);
}
/* tableparsing.c S47a */
static ShiftFun valshifts[]      = { sName, sExp,
                                                                         stop };
static ShiftFun defineshifts[]   = { sName, setcontextname, sNamelist, sExp,
                                                                         stop };
static ShiftFun useshifts[]      = { sName,
                                                                         stop };
static ShiftFun checkexpshifts[] = { sExp, sExp,
                                                                         stop };
static ShiftFun checkassshifts[] = { sExp,
                                                                         stop };
static ShiftFun checkerrshifts[] = { sExp,
                                                                         stop };
static ShiftFun expshifts[]      = { use_exp_parser };

struct ParserRow xdeftable[] = { 
    { "val",          ADEF(VAL),           valshifts },
    { "define",       ADEF(DEFINE),        defineshifts },
    { "use",          ANXDEF(USE),         useshifts },
    { "check-expect", ATEST(CHECK_EXPECT), checkexpshifts },
    { "check-assert", ATEST(CHECK_ASSERT), checkassshifts },
    { "check-error",  ATEST(CHECK_ERROR),  checkerrshifts },
    /* rows added to [[xdeftable]] in exercises S53d */
    /* add new forms for extended definitions here */
    { NULL,           ADEF(EXP),           expshifts }  /* must come last */
};
/* tableparsing.c S47b */
XDef parsexdef(Par p, Sourceloc source) {
    switch (p->alt) {
    case ATOM:
        return mkDef(mkExp(parseexp(p, source)));
    case LIST:;
        struct ParserState s  = mkParserState(p, source);
        struct ParserRow *row = tableparse(&s, xdeftable);
        XDef d = reduce_to_xdef(row->code, s.components);
        if (d->alt == DEF)
            check_def_duplicates(source, d->u.def);
        return d;
    }
    assert(0);
}
/* tableparsing.c S47c */
ParserResult use_exp_parser(ParserState s) {
    Exp e = parseexp(s->context.par, s->context.source);
    halfshift(s);
    s->components[s->nparsed++].exp = e;
    return STOP_PARSING;
}
/* tableparsing.c S48a */
Name parsename(Par p, ParsingContext context) {
    Exp e = parseexp(p, context->source);
    if (e->alt != VAR)
        return name_error(p, context);
    else
        return e->u.var;
}
/* tableparsing.c S48b */
Explist parseexplist(Parlist input, Sourceloc source) {
    if (input == NULL) {
        return NULL;
    } else {
        Exp     e  = parseexp    (input->hd, source);
        Explist es = parseexplist(input->tl, source);
        return mkEL(e, es);
    }
}
/* tableparsing.c S48c */
static Namelist parsenamelist(Parlist ps, ParsingContext context) {
    if (ps == NULL) {
        return NULL;
    } else {
        Exp e = parseexp(ps->hd, context->source);
        if (e->alt != VAR)
            synerror(context->source,
                     "in %p, formal parameters of %n must be names, "
                     "but %p is not a name", context->par, context->name, ps->hd
                                                                              );
        return mkNL(e->u.var, parsenamelist(ps->tl, context));
    }
}
/* tableparsing.c S50a */
void usage_error(int code, ParserResult why_bad, ParsingContext context) {
    for (struct Usage *u = usage_table; u->expected != NULL; u++)
        if (code == u->code) {
            const char *message;
            switch (why_bad) {
            case INPUT_EXHAUSTED:
                message = "too few components in %p; expected %s";
                break;
            case INPUT_LEFTOVER:
                message = "too many components in %p; expected %s";
                break;
            default:
                message = "badly formed input %p; expected %s";
                break;
            }
            synerror(context->source, message, context->par, u->expected);
        }
    synerror(context->source, "something went wrong parsing %p", context->par);
}
/* tableparsing.c S50b */
void *name_error(Par bad, struct ParsingContext *c) {
    switch (code_of_name(c->name)) {
    case ADEF(VAL):
        synerror(c->source, "in %p, expected (val x e), but %p is not a name",
                 c->par, bad);
    case ADEF(DEFINE):
        synerror(c->source,
                   "in %p, expected (define f (x ...) e), but %p is not a name",
                 c->par, bad);
    case ANXDEF(USE):
        synerror(c->source,
                     "in %p, expected (use filename), but %p is not a filename",
                 c->par, bad);
    case SET:
        synerror(c->source, "in %p, expected (set x e), but %p is not a name",
                                                                                
                 c->par, bad);
    case APPLY:
        synerror(c->source,
                    "in %p, expected (function-name ...), but %p is not a name",
                 c->par, bad);
    default:
        synerror(c->source, "in %p, expected a name, but %p is not a name", 
                 c->par, bad);
    }
    return NULL; // not reached
}
/* tableparsing.c S51a */
int code_of_name(Name n) {
    struct ParserRow *entry;
    for (entry = exptable; entry->keyword != NULL; entry++)
        if (n == strtoname(entry->keyword))
            return entry->code;
    if (n == NULL)
        return entry->code;
    for (entry = xdeftable; entry->keyword != NULL; entry++)
        if (n == strtoname(entry->keyword))
            return entry->code;
    assert(0);
}
