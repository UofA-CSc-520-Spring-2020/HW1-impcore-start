#include "all.h"
/*
 * In Impcore, a tick mark is not read as [[(quote
 * ...)]], so [[read_tick_as_quote]] is false.
 * <impcore.c>=
 */
bool read_tick_as_quote = false;
/*
 * Implementation of [[main]]
 * 
 * [*] The [[main]] function coordinates all the pieces
 * and forms a working interpreter. Such an interpreter
 * can operate in two modes:
 * 
 *   • In interactive mode, the interpreter prompts for
 *  every input, and when it detects a syntax error,
 *  it does not print the source-code location.
 *   • In non-interactive mode, the interpreter does not
 *  prompt for any input, and when it detects a
 *  syntax error, it prints the source-code
 *  locations.
 * 
 * Interactive mode is meant for interactive use, and
 * non-interactive mode is meant for redirecting
 * standard input from a file. The interpreter is in
 * interactive mode by default, but if its given the
 * option -q, for ``quiet,'' it operates in
 * non-interactive mode. [*] [*] \iimplabelmain
 * <impcore.c>=
 */
int main(int argc, char *argv[]) {
    bool interactive  = (argc <= 1) || (strcmp(argv[1], "-q") != 0);
    Prompts prompts  = interactive ? STD_PROMPTS : NO_PROMPTS;
    set_toplevel_error_format(interactive ? WITHOUT_LOCATIONS : WITH_LOCATIONS);
    if (getenv("NOERRORLOC")) set_toplevel_error_format(WITHOUT_LOCATIONS);
                                                            /*testing*/ /*OMIT*/

    /*
     * Printing functions
     * 
     * [*] \crefpageimpcore.conversion-specifiers lists all
     * the types of values that [[print]], [[fprint]],
     * [[runerror]], and [[synerror]] know how to print.
     * Each of the conversion specifiers mentioned in that
     * table has to be installed. That work is done here:
     * <install conversion specifications for [[print]] and [[fprint]]>=
     */
    installprinter('c', printchar);
    installprinter('d', printdecimal);
    installprinter('e', printexp);
    installprinter('E', printexplist);
    installprinter('f', printfun);
    installprinter('n', printname);
    installprinter('N', printnamelist);
    installprinter('p', printpar);
    installprinter('P', printparlist);
    installprinter('s', printstring);
    installprinter('t', printdef);
    installprinter('v', printvalue);
    installprinter('V', printvaluelist);
    installprinter('%', printpercent);

    Valenv globals   = mkValenv(NULL, NULL);
    Funenv functions = mkFunenv(NULL, NULL);
    /*
     * The initial basis includes both primitives and
     * user-defined functions. We install the primitives
     * first.
     * <install the initial basis in [[functions]]>=
     */
    {
        static const char *prims[] = 
           { "+", "-", "*", "/", "<", ">", "=", "println", "print", "printu", 0
                                                                              };
        for (const char **p = prims; *p; p++) {
            Name x = strtoname(*p);
            bindfun(x, mkPrimitive(x), functions);
        }
    }
    /*
     * [*]
     */

    /*
     * <install the initial basis in [[functions]]>=
     */
    {
        const char *fundefs = 
           
             ";;\n"

";;   ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
             ";;   \\advance\\linewidthby -2 \\advance\\nwdefspaceby 2\n"

";;   ┌───────────────────────────────────────────────────┐\n"
             ";;   │We write Boolean connectives using [[if]]          │\n"
             ";;   │expressions. [*]                                   │\n"

";;   └───────────────────────────────────────────────────┘\n"
             ";;   <predefined Impcore functions>=\n"
             ";;\n"
             "(define and (b c) (if b c b))\n"
             "(define or  (b c) (if b b c))\n"
             "(define not (b)   (if b 0 1))\n"
             ";;\n"
             ";;   Unlike the similar constructs built into the syntax\n"
             ";;   of many languages, these versions of [[and]] and\n"
             ";;   [[or]] always evaluate both of their arguments.\n"
             ";;   Section [->] shows how you can use syntactic sugar to\n"
             ";;   define short-circuit variations that evaluate a\n"
             ";;   second expression only when necessary.\n"
             ";;\n"
             "\n"
             ";;\n"
             ";;   We add new arithmetic comparisons.\n"
             ";;   <predefined Impcore functions>=\n"
             ";;\n"
             "(define <= (x y) (not (> x y)))\n"
             "(define >= (x y) (not (< x y)))\n"
             "(define != (x y) (not (= x y)))\n"
             ";;\n"
             ";;   Finally, we use primitive arithmetic to define\n"
             ";;   modulus and negation.\n"
             ";;\n"
             "\n"
             ";;\n"
             ";;   <predefined Impcore functions>=\n"
             ";;\n"
             "(define mod (m n) (- m (* n (/ m n))))\n"
             "(define negated (n) (- 0 n))\n"
             ";;\n"
             ";;   The C code to install the initial basis is shown in\n"
             ";;   chunk [[<<install the initial basis in\n"
             ";;   [[functions]]>>]], which is continued in chunk [->].\n"

";;   ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
             ";;   \n"
             ";;   Predefined functions in Impcore's initial basis [*]\n"

";;   ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
             ";;   \n"
             ";;   Just like any other function, a primitive or\n"
             ";;   predefined function can be redefined using\n"
             ";;   [[define]]. This trick can be useful---for example,\n"
             ";;   to count the number of times a function is called.\n"
             ";;   But if you redefine an initial-basis function, take\n"
             ";;   care not to change the results it returns! Such bugs\n"
             ";;   are too hard to find.\n"
             ";;   \n"
             ";;   Before going on to the next sections, work some of\n"
             ";;   the problems in \\crefimpcore.ex.learning-lang of the\n"
             ";;   exercises (``\\implangextitle''), which starts on\n"
             ";;   page [->].\n"
             ";;\n"
             "\n";
        if (setjmp(errorjmp))
            assert(0); // if error in predefined function, die horribly
        readevalprint(stringxdefs("predefined functions", fundefs), globals,
                                                          functions, NO_ECHOES);
    }

    XDefstream xdefs = filexdefs("standard input", stdin, prompts);
    extern void dump_fenv_names(Funenv); /*OMIT*/
    if (argv[1] && !strcmp(argv[1], "-names")) { dump_fenv_names(functions);
                                                             exit(0); } /*OMIT*/

    while (setjmp(errorjmp))
        ;
    readevalprint(xdefs, globals, functions, ECHOES);
    return 0;
}
