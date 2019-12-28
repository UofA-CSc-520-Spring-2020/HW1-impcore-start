#include "all.h"
/* scheme.c S154b */
int main(int argc, char *argv[]) {
    bool interactive = (argc <= 1) || (strcmp(argv[1], "-q") != 0);
    Prompts prompts = interactive ? STD_PROMPTS : NO_PROMPTS;
    set_toplevel_error_format(interactive ? WITHOUT_LOCATIONS : WITH_LOCATIONS);
    if (getenv("NOERRORLOC")) set_toplevel_error_format(WITHOUT_LOCATIONS);
                                                            /*testing*/ /*OMIT*/

    initvalue();
    
    /* install printers S155a */
    installprinter('c', printchar);
    installprinter('d', printdecimal);
    installprinter('e', printexp);
    installprinter('E', printexplist);
    installprinter('\\', printlambda);
    installprinter('n', printname);
    installprinter('N', printnamelist);
    installprinter('p', printpar);
    installprinter('P', printparlist);
    installprinter('r', printenv);
    installprinter('s', printstring);
    installprinter('t', printdef);
    installprinter('v', printvalue);
    installprinter('V', printvaluelist);
    installprinter('%', printpercent);

    Env env = NULL;
    initallocate(&env);
    /* install primitive functions into [[env]] S151b */
    #define xx(NAME, TAG, FUNCTION) \
        env = bindalloc(strtoname(NAME), mkPrimitive(TAG, FUNCTION), env);
    #include "prim.h"
    #undef xx
    /* install predefined functions into [[env]] S155b */
    const char *fundefs = 
                            ";  predefined uScheme functions 101 \n"
                            "(define caar (xs) (car (car xs)))\n"
                            "(define cadr (xs) (car (cdr xs)))\n"
                            "(define cdar (xs) (cdr (car xs)))\n"

";  predefined uScheme functions ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) \n"

               ";  more predefined combinations of [[car]] and [[cdr]] S164d \n"
                            "(define cddr  (sx) (cdr (cdr  sx)))\n"
                            "(define caaar (sx) (car (caar sx)))\n"
                            "(define caadr (sx) (car (cadr sx)))\n"
                            "(define cadar (sx) (car (cdar sx)))\n"
                            "(define caddr (sx) (car (cddr sx)))\n"
                            "(define cdaar (sx) (cdr (caar sx)))\n"
                            "(define cdadr (sx) (cdr (cadr sx)))\n"
                            "(define cddar (sx) (cdr (cdar sx)))\n"
                            "(define cdddr (sx) (cdr (cddr sx)))\n"

               ";  more predefined combinations of [[car]] and [[cdr]] S164e \n"
                            "(define caaaar (sx) (car (caaar sx)))\n"
                            "(define caaadr (sx) (car (caadr sx)))\n"
                            "(define caadar (sx) (car (cadar sx)))\n"
                            "(define caaddr (sx) (car (caddr sx)))\n"
                            "(define cadaar (sx) (car (cdaar sx)))\n"
                            "(define cadadr (sx) (car (cdadr sx)))\n"
                            "(define caddar (sx) (car (cddar sx)))\n"
                            "(define cadddr (sx) (car (cdddr sx)))\n"

               ";  more predefined combinations of [[car]] and [[cdr]] S164f \n"
                            "(define cdaaar (sx) (cdr (caaar sx)))\n"
                            "(define cdaadr (sx) (cdr (caadr sx)))\n"
                            "(define cdadar (sx) (cdr (cadar sx)))\n"
                            "(define cdaddr (sx) (cdr (caddr sx)))\n"
                            "(define cddaar (sx) (cdr (cdaar sx)))\n"
                            "(define cddadr (sx) (cdr (cdadr sx)))\n"
                            "(define cdddar (sx) (cdr (cddar sx)))\n"
                            "(define cddddr (sx) (cdr (cdddr sx)))\n"
                            ";  predefined uScheme functions 102a \n"
                            "(define list1 (x)     (cons x '()))\n"
                            "(define list2 (x y)   (cons x (list1 y)))\n"
                            "(define list3 (x y z) (cons x (list2 y z)))\n"
                            ";  predefined uScheme functions 103b \n"
                            "(define append (xs ys)\n"
                            "  (if (null? xs)\n"
                            "     ys\n"
                            "     (cons (car xs) (append (cdr xs) ys))))\n"
                            ";  predefined uScheme functions 105a \n"

                        "(define revapp (xs ys) ; (reverse xs) followed by ys\n"
                            "  (if (null? xs)\n"
                            "     ys\n"
                            "     (revapp (cdr xs) (cons (car xs) ys))))\n"
                            ";  predefined uScheme functions 105b \n"
                            "(define reverse (xs) (revapp xs '()))\n"

";  predefined uScheme functions ((elided)) (THIS CAN'T HAPPEN -- claimed code was not used) \n"

";  definitions of predefined uScheme functions [[and]], [[or]], and [[not]] 160 \n"
                            "(define and (b c) (if b  c  b))\n"
                            "(define or  (b c) (if b  b  c))\n"
                            "(define not (b)   (if b #f #t))\n"
                            ";  predefined uScheme functions 106c \n"

"(define atom? (x) (or (symbol? x) (or (number? x) (or (boolean? x) (null? x)))))\n"
                            ";  predefined uScheme functions 108a \n"
                            "(define equal? (sx1 sx2)\n"
                            "  (if (atom? sx1)\n"
                            "    (= sx1 sx2)\n"
                            "    (if (atom? sx2)\n"
                            "        #f\n"
                            "        (and (equal? (car sx1) (car sx2))\n"
                            "             (equal? (cdr sx1) (cdr sx2))))))\n"
                            ";  predefined uScheme functions 110b \n"
                            "(define make-alist-pair (k a) (list2 k a))\n"

                          "(define alist-pair-key        (pair)  (car  pair))\n"

                          "(define alist-pair-attribute  (pair)  (cadr pair))\n"
                            ";  predefined uScheme functions 110c \n"

   "(define alist-first-key       (alist) (alist-pair-key       (car alist)))\n"

   "(define alist-first-attribute (alist) (alist-pair-attribute (car alist)))\n"
                            ";  predefined uScheme functions 111a \n"
                            "(define bind (k a alist)\n"
                            "  (if (null? alist)\n"
                            "    (list1 (make-alist-pair k a))\n"
                            "    (if (equal? k (alist-first-key alist))\n"
                            "      (cons (make-alist-pair k a) (cdr alist))\n"

                          "      (cons (car alist) (bind k a (cdr alist))))))\n"
                            "(define find (k alist)\n"
                            "  (if (null? alist)\n"
                            "    '()\n"
                            "    (if (equal? k (alist-first-key alist))\n"
                            "      (alist-first-attribute alist)\n"
                            "      (find k (cdr alist)))))\n"
                            ";  predefined uScheme functions 131a \n"

  "(define o (f g) (lambda (x) (f (g x))))          ; ((o f g) x) = (f (g x))\n"
                            ";  predefined uScheme functions 132b \n"

                      "(define curry   (f) (lambda (x) (lambda (y) (f x y))))\n"
                            "(define uncurry (f) (lambda (x y) ((f x) y)))\n"
                            ";  predefined uScheme functions 136a \n"
                            "(define filter (p? xs)\n"
                            "  (if (null? xs)\n"
                            "    '()\n"
                            "    (if (p? (car xs))\n"
                            "      (cons (car xs) (filter p? (cdr xs)))\n"
                            "      (filter p? (cdr xs)))))\n"
                            ";  predefined uScheme functions 136b \n"
                            "(define map (f xs)\n"
                            "  (if (null? xs)\n"
                            "    '()\n"
                            "    (cons (f (car xs)) (map f (cdr xs)))))\n"
                            ";  predefined uScheme functions 136c \n"
                            "(define app (f xs)\n"
                            "  (if (null? xs)\n"
                            "    #f\n"
                            "    (begin (f (car xs)) (app f (cdr xs)))))\n"
                            ";  predefined uScheme functions 136d \n"
                            "(define exists? (p? xs)\n"
                            "  (if (null? xs)\n"
                            "    #f\n"
                            "    (if (p? (car xs)) \n"
                            "      #t\n"
                            "      (exists? p? (cdr xs)))))\n"
                            "(define all? (p? xs)\n"
                            "  (if (null? xs)\n"
                            "    #t\n"
                            "    (if (p? (car xs))\n"
                            "      (all? p? (cdr xs))\n"
                            "      #f)))\n"
                            ";  predefined uScheme functions 137b \n"
                            "(define foldr (op zero xs)\n"
                            "  (if (null? xs)\n"
                            "    zero\n"
                            "    (op (car xs) (foldr op zero (cdr xs)))))\n"
                            "(define foldl (op zero xs)\n"
                            "  (if (null? xs)\n"
                            "    zero\n"
                            "    (foldl op (op (car xs) zero) (cdr xs))))\n"
                            ";  predefined uScheme functions S164a \n"
                            "(define <= (x y) (not (> x y)))\n"
                            "(define >= (x y) (not (< x y)))\n"
                            "(define != (x y) (not (= x y)))\n"
                            ";  predefined uScheme functions S164b \n"
                            "(define max (x y) (if (> x y) x y))\n"
                            "(define min (x y) (if (< x y) x y))\n"
                            ";  predefined uScheme functions S164c \n"
                            "(define negated (n) (- 0 n))\n"
                            "(define mod (m n) (- m (* n (/ m n))))\n"

                         "(define gcd (m n) (if (= n 0) m (gcd n (mod m n))))\n"

                     "(define lcm (m n) (if (= m 0) 0 (* m (/ n (gcd m n)))))\n"
                            ";  predefined uScheme functions S165a \n"

                     "(define list4 (x y z a)         (cons x (list3 y z a)))\n"

                   "(define list5 (x y z a b)       (cons x (list4 y z a b)))\n"

                 "(define list6 (x y z a b c)     (cons x (list5 y z a b c)))\n"

               "(define list7 (x y z a b c d)   (cons x (list6 y z a b c d)))\n"

            "(define list8 (x y z a b c d e) (cons x (list7 y z a b c d e)))\n";
    if (setjmp(errorjmp))
        assert(0);  // fail if error occurs in predefined functions
    readevalprint(stringxdefs("predefined functions", fundefs), &env, NO_ECHOES)
                                                                               ;
    extern void dump_env_names(Env); /*OMIT*/
    if (argv[1] && !strcmp(argv[1], "-names")) { dump_env_names(env); exit(0); }
                                                                        /*OMIT*/

    XDefstream xdefs = filexdefs("standard input", stdin, prompts);

    while (setjmp(errorjmp))
        ;
    readevalprint(xdefs, &env, ECHOES);
    return 0;
}
