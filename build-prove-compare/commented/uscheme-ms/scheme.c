#include "all.h"
/*
 * Implementation of the interpreter's [[main]]
 * procedure
 * 
 * As in the Impcore interpreter, [[main]] processes
 * arguments, initializes the interpreter, and runs the
 * read-eval-print loop. \scmflabelmain
 * <scheme.c>=
 */
int main(int argc, char *argv[]) {
    bool interactive = (argc <= 1) || (strcmp(argv[1], "-q") != 0);
    Prompts prompts = interactive ? STD_PROMPTS : NO_PROMPTS;
    set_toplevel_error_format(interactive ? WITHOUT_LOCATIONS : WITH_LOCATIONS);
    if (getenv("NOERRORLOC")) set_toplevel_error_format(WITHOUT_LOCATIONS);
                                                            /*testing*/ /*OMIT*/

    initvalue();
    
    /*
     * We have many printers.
     * <install printers>=
     */
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
    /*
     * In [[addprimitives]], the [[xx]] macro extends the
     * initial environment.
     * <install primitive functions into [[env]]>=
     */
    #define xx(NAME, TAG, FUNCTION) \
        env = bindalloc(strtoname(NAME), mkPrimitive(TAG, FUNCTION), env);
    #include "prim.h"
    #undef xx
    /*
     * As in the Impcore interpreter, the C representation
     * of the initial basis is generated automatically from
     * code in [[]]. \
     * makenowebnotdef(from \LApredefined micro-Scheme
     * functions \upshape[->]\RA)
     * <install predefined functions into [[env]]>=
     */
    const char *fundefs = 
                            ";;\n"

                   ";;   When all complex data structures are built from cons\n"

                       ";;   cells, we may find ourselves applying [[car]] or\n"

                     ";;   [[cdr]] several times in succession. In old-school\n"

                     ";;   Scheme, such applications were so common that they\n"
                            ";;   have traditional abbreviations: [*]\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define caar (xs) (car (car xs)))\n"
                            "(define cadr (xs) (car (cdr xs)))\n"
                            "(define cdar (xs) (cdr (car xs)))\n"
                            ";;\n"
                            ";;   <predefined uScheme functions ((elided))>=\n"
                            ";;\n"
                            ";;\n"
                            ";;   List operations\n"
                            ";;   \n"

                 ";;   <more predefined combinations of [[car]] and [[cdr]]>=\n"
                            ";;\n"
                            "(define cddr  (sx) (cdr (cdr  sx)))\n"
                            "(define caaar (sx) (car (caar sx)))\n"
                            "(define caadr (sx) (car (cadr sx)))\n"
                            "(define cadar (sx) (car (cdar sx)))\n"
                            "(define caddr (sx) (car (cddr sx)))\n"
                            "(define cdaar (sx) (cdr (caar sx)))\n"
                            "(define cdadr (sx) (cdr (cadr sx)))\n"
                            "(define cddar (sx) (cdr (cdar sx)))\n"
                            "(define cdddr (sx) (cdr (cddr sx)))\n"
                            ";;\n"

                 ";;   <more predefined combinations of [[car]] and [[cdr]]>=\n"
                            ";;\n"
                            "(define caaaar (sx) (car (caaar sx)))\n"
                            "(define caaadr (sx) (car (caadr sx)))\n"
                            "(define caadar (sx) (car (cadar sx)))\n"
                            "(define caaddr (sx) (car (caddr sx)))\n"
                            "(define cadaar (sx) (car (cdaar sx)))\n"
                            "(define cadadr (sx) (car (cdadr sx)))\n"
                            "(define caddar (sx) (car (cddar sx)))\n"
                            "(define cadddr (sx) (car (cdddr sx)))\n"
                            ";;\n"

                 ";;   <more predefined combinations of [[car]] and [[cdr]]>=\n"
                            ";;\n"
                            "(define cdaaar (sx) (cdr (caaar sx)))\n"
                            "(define cdaadr (sx) (cdr (caadr sx)))\n"
                            "(define cdadar (sx) (cdr (cadar sx)))\n"
                            "(define cdaddr (sx) (cdr (caddr sx)))\n"
                            "(define cddaar (sx) (cdr (cdaar sx)))\n"
                            "(define cddadr (sx) (cdr (cdadr sx)))\n"
                            "(define cdddar (sx) (cdr (cddar sx)))\n"
                            "(define cddddr (sx) (cdr (cdddr sx)))\n"
                            ";;\n"
                            ";;   The chunk [[]]\n"

                           ";;   contains definitions that are built into the\n"

                      ";;   micro-Scheme interpreter itself and are evaluated\n"

                         ";;   when the interpreter starts. Like full Scheme,\n"

                      ";;   micro-Scheme provides combinations of [[car]] and\n"

                     ";;   [[cdr]] up to depth five, ending with [[cdddddr]].\n"

                     ";;   These definitions are relegated to the Supplement.\n"
                            ";;\n"
                            "\n"
                            ";;\n"

                        ";;   If applying [[car]] or [[cdr]] several times in\n"

                        ";;   succession is tiresome, so is applying [[cons]]\n"

                     ";;   several times in succession. micro-Scheme provides\n"
                            ";;   functions that handle common cases:\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define list1 (x)     (cons x '()))\n"
                            "(define list2 (x y)   (cons x (list1 y)))\n"
                            "(define list3 (x y z) (cons x (list2 y z)))\n"
                            ";;\n"
                            ";;   Functions [[list4]] to [[list8]] are in the\n"
                            ";;   Supplement.\n"
                            ";;\n"
                            "\n"
                            ";;\n"

                   ";;   Another basic operation, [[append]], takes two lists\n"

               ";;   \\xs and \\ys, and returns the list that represents ``\\\n"

                         ";;   xs followed by \\ys.'' The [[append]] function\n"

                    ";;   consumes only \\xs, leaving \\ys uninspected. As in\n"

                   ";;   [[length]], the list \\xs is formed using either [['\n"

                      ";;   ()]] or [[cons]], and there are exactly those two\n"

                 ";;   cases to consider. If \\xs is empty, then appending \\\n"

              ";;   ys to \\xs simply produces \\ys. Otherwise, if \\xs is \\\n"

                         ";;   monobox(cons \\metaz \\zs), then the result of\n"

               ";;   [[append]] is \\metaz followed by \\zs followed by \\ys.\n"

                     ";;   Translating this specification into algebraic laws\n"

                   ";;   tells us just what [[append]] must do in each case: \n"

                   ";;   [*] {llaws} \\monolaw(append '() \\ys)\\ys \\monolaw\n"

              ";;   (append (cons \\metaz \\zs) \\ys)(cons \\metaz (append \\\n"

                ";;   zs \\ys)) {llaws} In the code, argument [[xs]] holds \\\n"

               ";;   xs, argument [[ys]] holds \\ys, \\metaz is \\monobox(car\n"
                            ";;   xs), and \\zs is \\monobox(cdr xs):\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define append (xs ys)\n"
                            "  (if (null? xs)\n"
                            "     ys\n"
                            "     (cons (car xs) (append (cdr xs) ys))))\n"
                            ";;\n"
                            ";;   The code looks like this:\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"

                        "(define revapp (xs ys) ; (reverse xs) followed by ys\n"
                            "  (if (null? xs)\n"
                            "     ys\n"
                            "     (revapp (cdr xs) (cons (car xs) ys))))\n"
                            ";;\n"

                         ";;   The trick used to make reversal efficient also\n"

                  ";;   applies to other problems. It is called the method of\n"

                  ";;   accumulating parameters, because the parameter [[ys]]\n"

                  ";;   is used to accumulate the eventual result. A compiler\n"

                       ";;   for full Scheme translates this code into a very\n"
                            ";;   tight loop.\n"
                            ";;\n"
                            "\n"
                            ";;\n"

                      ";;   In the initial basis of micro-Scheme, I define an\n"

                    ";;   efficient [[reverse]] by reversing and appending to\n"
                            ";;   the empty list.\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define reverse (xs) (revapp xs '()))\n"
                            ";;\n"

                     ";;   Every ordinary S-expression is either an atom or a\n"

                    ";;   list of ordinary S-expressions. [The empty list [['\n"

                     ";;   ()]] is \\emph{both} an atom \\emph{and} a list of\n"

                    ";;   ordinary S-expressions.] To help you identify atoms\n"

                           ";;   quickly and easily, micro-Scheme defines the\n"
                            ";;   predicate [[atom?]].[*]\n"
                            ";;   <predefined uScheme functions ((elided))>=\n"
                            ";;\n"
                            ";;\n"
                            ";;   The initial basis\n"
                            ";;   \n"
                            ";;   [*]\n"
                            ";;   \n"

                    ";;   \\Vrefscheme.basis.table lists all the functions in\n"

                  ";;   the initial basis of micro-Scheme. A handful of these\n"

                  ";;   functions are primitives. The remaining functions are\n"

                  ";;   predefined, and many of the definitions appear above,\n"
                            ";;   in chunks named [[<<predefined micro-Scheme\n"

                     ";;   functions>>]]. Most of the remaining functions are\n"

                   ";;   defined exactly as in Impcore, and their definitions\n"

                   ";;   are relegated to the Supplement. But unlike Impcore,\n"

                   ";;   micro-Scheme has true Boolean values, which are used\n"

                   ";;   in the definitions of functions [[and]], [[or]], and\n"
                            ";;   [[not]]:\n"

";;   <definitions of predefined uScheme functions [[and]], [[or]], and [[not]]>=\n"
                            ";;\n"
                            "(define and (b c) (if b  c  b))\n"
                            "(define or  (b c) (if b  b  c))\n"
                            "(define not (b)   (if b #f #t))\n"
                            ";;\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"

"(define atom? (x) (or (symbol? x) (or (number? x) (or (boolean? x) (null? x)))))\n"
                            ";;\n"
                            ";;   Equality on S-expressions\n"
                            ";;   \n"

                   ";;   An ordinary S-expression is either an atom or a list\n"

                      ";;   of ordinary S-expressions. Two atoms are equal if\n"

                  ";;   they are the same, as tested with primitive [[=]]. \\\n"

                     ";;   stdbreak Two lists are equal if they contain equal\n"

                      ";;   elements in equal positions: equality on lists is\n"

                     ";;   defined recursively. As with [[has?]], we are best\n"

                  ";;   off defining equality on fully general S-expressions.\n"

               ";;   When there are two S-expressions \\meta\\sx_1 and \\meta\n"

                      ";;   \\sx_2, and they have two forms each, there are a\n"

               ";;   total of four cases: {llaws} \\monolaw[, if \\meta\\sx_1\n"

               ";;   is an atom and \\meta\\sx_2 is an atom] (equal? \\meta\\\n"

            ";;   sx_1 \\meta\\sx_2)(= \\meta\\sx_1 \\meta\\sx_2) \\monolaw[,\n"

              ";;   if \\meta\\sx_1 is an atom] (equal? \\meta\\sx_1 (cons \\\n"

               ";;   metaw \\metaz)))[[#f]] \\monolaw[, if \\meta\\sx_2 is an\n"

             ";;   atom] (equal (cons \\metax \\metay) \\meta\\sx_2)[[#f]] \\\n"

                 ";;   monolaw(equal? (cons \\metax \\metay) (cons \\metaw \\\n"

               ";;   metaz)) (and (equal? \\metax \\metaw) (equal? \\metay \\\n"

                      ";;   metaz)) {llaws} \\vfilbreak[2000]3in To implement\n"

                 ";;   these laws, I take a shortcut: when \\meta\\sx_1 is an\n"

              ";;   atom and \\meta\\sx_2 is \\monobox(cons \\metaw \\metaz),\n"

               ";;   I am guaranteed that \\monobox(= \\meta\\sx_1 \\meta\\sx\n"

                   ";;   _2) is [[#f]]. So I can combine the right-hand sides\n"
                            ";;   of the first two laws: [*]\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define equal? (sx1 sx2)\n"
                            "  (if (atom? sx1)\n"
                            "    (= sx1 sx2)\n"
                            "    (if (atom? sx2)\n"
                            "        #f\n"
                            "        (and (equal? (car sx1) (car sx2))\n"
                            "             (equal? (cdr sx1) (cdr sx2))))))\n"
                            ";;\n"

                          ";;   These examples show mostly interesting cases,\n"

                    ";;   involving lists. My (private) test suite tests both\n"

                         ";;   [[#t]] and [[#f]] outcomes for all four cases.\n"
                            ";;\n"
                            "\n"
                            ";;\n"

                     ";;   A small map is often represented as an association\n"

                  ";;   list. An association list has the form \\monobox((k_1\n"

                           ";;   a_1) ... (k_m a_m)),\\notation k a key in an\n"

                        ";;   association list\\notation a an attribute in an\n"

                    ";;   association list where each k_i is a symbol, called\n"

                  ";;   a key, and each a_i is an arbitrary value, called an \n"

                  ";;   attribute. I treat each key-attribute pair \\monobox(\n"

                      ";;   k_i a_i) like an abstraction that satisfies these\n"
                            ";;   laws: {llaws} \\monolaw(alist-pair-key\n"

                    ";;   (make-alist-pair \\metak \\metaa))\\metak \\monolaw\n"

                  ";;   (alist-pair-attribute (make-alist-pair \\metak \\meta\n"

                   ";;   a))\\metaa {llaws} The laws are implemented by these\n"
                            ";;   functions:\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define make-alist-pair (k a) (list2 k a))\n"

                          "(define alist-pair-key        (pair)  (car  pair))\n"

                          "(define alist-pair-attribute  (pair)  (cadr pair))\n"
                            ";;\n"

                    ";;   Because a lot of code operates on the first pair in\n"

                        ";;   an association list, micro-Scheme also includes\n"

                  ";;   auxiliary functions that provide direct access to the\n"
                            ";;   first key and attribute:\n"
                            ";;\n"
                            "\n"
                            ";;\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"

   "(define alist-first-key       (alist) (alist-pair-key       (car alist)))\n"

   "(define alist-first-attribute (alist) (alist-pair-attribute (car alist)))\n"
                            ";;\n"

                   ";;   The association list itself is operated on primarily\n"

                       ";;   by [[bind]] and [[find]], which add bindings and\n"

                ";;   retrieve attributes. [*] {llaws*} \\monolaw(bind \\meta\n"

                ";;   k \\metaa '())(cons (make-alist-pair \\metak' \\metaa')\n"
                            ";;   '()) \\monolaw(bind \\metak \\metaa (cons\n"

                       ";;   (make-alist-pair \\metak \\metaa') pairs)) (cons\n"

                ";;   (make-alist-pair \\metak \\metaa) pairs) \\monolaw(bind\n"

              ";;   \\metak \\metaa (cons (make-alist-pair \\metak' \\metaa')\n"

                ";;   pairs)) (cons (make-alist-pair \\metak' \\metaa') (bind\n"

               ";;   \\metak \\metaa pairs)), --- --- \\qquadwhen \\metak and\n"
                            ";;   \\metak' are different\n"

                  ";;   \\monolaw(find \\metak '())'() \\monolaw(find \\metak\n"

              ";;   (cons (make-alist-pair \\metak \\metaa) pairs))\\metaa \\\n"

                ";;   monolaw(find \\metak (cons (make-alist-pair \\metak' \\\n"

                 ";;   metaa) pairs))(find \\metak pairs) --- --- \\qquadwhen\n"
                            ";;   \\metak and \\metak' are different\n"
                            ";;   {llaws*} \\stdbreak\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
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
                            ";;\n"
                            ";;   Composition\n"
                            ";;   \n"

                    ";;   One of the simplest higher-order functions is [[o]]\n"

                     ";;   (pronounced ``circle'' or even ``compose''), which\n"
                            ";;   returns the composition of two one-argument\n"

                    ";;   functions, often written f og.\\stdbreak \\notation\n"

                        ";;   [composed with]ofunction composition The law of\n"

                   ";;   function composition is (f og)(x) = f(g(x)), and its\n"

                         ";;   implementation in Scheme returns a [[lambda]]:\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"

  "(define o (f g) (lambda (x) (f (g x))))          ; ((o f g) x) = (f (g x))\n"
                            ";;\n"

                  ";;   In large programs, function composition is often used\n"

                      ";;   to improve modularity: an algorithm can be broken\n"

                     ";;   down into pieces that are connected using function\n"

                     ";;   composition. Even as you're starting out, however,\n"

                  ";;   you can find simple ways to use function composition.\n"

                     ";;   A common one is to negate a predicate by composing\n"
                            ";;   [[not]] with it:\n"
                            ";;\n"
                            "\n"
                            ";;\n"

                        ";;   Because curried binary functions are so useful,\n"

                          ";;   micro-Scheme provides a way to convert binary\n"

                   ";;   functions between their curried and uncurried forms.\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"

                      "(define curry   (f) (lambda (x) (lambda (y) (f x y))))\n"
                            "(define uncurry (f) (lambda (x y) ((f x) y)))\n"
                            ";;\n"

";;   ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"

                  ";;   {llaws*} \\monolaw(filter p? '())'() \\monolaw(filter\n"

                       ";;   p? (cons y ys)) (cons y (filter p? ys)), when \\\n"

                 ";;   monobox(p? y) \\monolaw(filter p? (cons y ys)) (filter\n"

                 ";;   p? ys), when \\monobox(not (p? y)) [2pt] \\monolaw(map\n"

                 ";;   f '())'() \\monolaw(map f (cons y ys))(cons (f y) (map\n"

                 ";;   f ys)) [2pt] \\monolaw(exists? p? '())[[#f]] \\monolaw\n"

                  ";;   (exists? p? (cons y ys)) [[#t]], when \\monobox(p? y)\n"

                     ";;   \\monolaw(exists? p? (cons y ys)) (exists? p? ys),\n"

                ";;   when \\monobox(not (p? y)) [2pt] \\monolaw(all? p? '())\n"

                    ";;   [[#t]] \\monolaw(all? p? (cons y ys)) (all? p? ys),\n"

                ";;   when \\monobox(p? y) \\monolaw(all? p? (cons y ys)) [[#\n"

                  ";;   f]], when \\monobox(not (p? y)) [2pt] \\monolaw(foldr\n"

                  ";;   op zero '())zero \\monolaw(foldr op zero (cons y ys))\n"

                     ";;   (op y (foldr op zero ys)) [2pt] \\monolaw(foldl op\n"

                     ";;   zero '())zero \\monolaw(foldl op zero (cons y ys))\n"
                            ";;   (foldl op (op y zero) ys) {llaws*}\n"
                            ";;   \n"

                       ";;   Algebraic laws of pure higher-order functions on\n"
                            ";;   lists [*]\n"

";;   ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n"
                            ";;   \n"

                         ";;   The structure of [[filter]] is the same as the\n"

                   ";;   structure of [[remove-multiples]] in chunk [->]; the\n"

                    ";;   only difference is in the test. Filtering the empty\n"

                  ";;   list produces the empty list. For the induction step,\n"

                  ";;   I either cons or don't cons, depending on whether the\n"
                            ";;   [[car]] satisfies [[p?]].\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define filter (p? xs)\n"
                            "  (if (null? xs)\n"
                            "    '()\n"
                            "    (if (p? (car xs))\n"
                            "      (cons (car xs) (filter p? (cdr xs)))\n"
                            "      (filter p? (cdr xs)))))\n"
                            ";;\n"

                     ";;   The implementation of [[map]] is even simpler than\n"

                    ";;   that of [[filter]]. I don't need a conditional test\n"

                       ";;   in the induction step; I just apply [[f]] to the\n"
                            ";;   [[car]] before consing.\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define map (f xs)\n"
                            "  (if (null? xs)\n"
                            "    '()\n"
                            "    (cons (f (car xs)) (map f (cdr xs)))))\n"
                            ";;\n"

                  ";;   Function [[app]] is like [[map]], except its argument\n"

                  ";;   is applied only for side effect. It is typically used\n"

                  ";;   with [[printu]]. Because [[app]] is executed for side\n"

                        ";;   effects, its behavior cannot by expressed using\n"
                            ";;   simple algebraic laws.\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define app (f xs)\n"
                            "  (if (null? xs)\n"
                            "    #f\n"
                            "    (begin (f (car xs)) (app f (cdr xs)))))\n"
                            ";;\n"

                        ";;   Each of the preceding functions processes every\n"

                      ";;   element of its list argument. But [[exists?]] and\n"

                     ";;   [[all?]] needn't always inspect every element. In \n"

                        ";;   [[exists?]], I cut off the recursion the moment\n"

                    ";;   I find a satisfying element; in [[all?]], I cut off\n"

                       ";;   the recursion the moment I find a non-satisfying\n"
                            ";;   element.\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
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
                            ";;\n"

                          ";;   Finally, the implementations of [[foldr]] and\n"

                   ";;   [[foldl]], although simple, are not necessarily easy\n"

                    ";;   to understand. It may help to look at the algebraic\n"

                 ";;   laws, and to remember that \\monobox(car xs) is always\n"

                   ";;   a first argument to [[op]], and [[zero]] is always a\n"
                            ";;   second argument to [[op]].\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define foldr (op zero xs)\n"
                            "  (if (null? xs)\n"
                            "    zero\n"
                            "    (op (car xs) (foldr op zero (cdr xs)))))\n"
                            "(define foldl (op zero xs)\n"
                            "  (if (null? xs)\n"
                            "    zero\n"
                            "    (foldl op (op (car xs) zero) (cdr xs))))\n"
                            ";;\n"

                    ";;   {sidebar}[t]Three kinds of polymorphism Programmers\n"

                     ";;   love reusing code. And if they can call reuse by a\n"

                  ";;   fancy Greek name, they sound smart. What's less smart\n"

                           ";;   is that at least three different programming\n"
                            ";;   techniques are all called ``polymorphism.''\n"
                            ";;   \n"

                 ";;     • The sort of polymorphism we find in the standard\n"

                     ";;    list functions is called parametric polymorphism.\n"

                      ";;    [It's easy to think that the word ``parametric''\n"

                     ";;    comes from a function's parameter or from passing\n"

                      ";;    functions as parameters. The word actually comes\n"

                      ";;    from the idea of a \\emph{type parameter}, which\n"

                         ";;    I~define formally, as part of the language \\\n"

                           ";;    tuscheme, in Chapter~\\ref{tuscheme.chap}.]\n"

                      ";;    In parametric polymorphism, the polymorphic code\n"

                          ";;    executes the same algorithm in the same way,\n"

                       ";;    regardless of the types of the arguments. It is\n"

                       ";;    the simplest kind of polymorphism, and although\n"

                     ";;    it is most useful when combined with higher-order\n"

                       ";;    functions, implementing parametric polymorphism\n"

                      ";;    requires no special mechanisms at run time. Some\n"

                     ";;    form of parametric polymorphism is found in every\n"
                            ";;    functional language.\n"
                            ";;\n"
                            "\n"
                            ";;\n"
                            ";;   Integer functions\n"
                            ";;   \n"

                   ";;   \\highlightWe add additional integer operations, all\n"

                       ";;   of which are defined exactly as they would be in\n"

                         ";;   Impcore. \\highlightWe begin with comparisons.\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define <= (x y) (not (> x y)))\n"
                            "(define >= (x y) (not (< x y)))\n"
                            "(define != (x y) (not (= x y)))\n"
                            ";;\n"

                       ";;   \\highlightWe continue with [[min]] and [[max]].\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define max (x y) (if (> x y) x y))\n"
                            "(define min (x y) (if (< x y) x y))\n"
                            ";;\n"

                 ";;   Finally, \\highlightwe add negation, modulus, greatest\n"
                            ";;   common divisor, and least common multiple.\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"
                            "(define negated (n) (- 0 n))\n"
                            "(define mod (m n) (- m (* n (/ m n))))\n"

                         "(define gcd (m n) (if (= n 0) m (gcd n (mod m n))))\n"

                     "(define lcm (m n) (if (= m 0) 0 (* m (/ n (gcd m n)))))\n"
                            ";;\n"
                            ";;   <predefined uScheme functions>=\n"
                            ";;\n"

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
