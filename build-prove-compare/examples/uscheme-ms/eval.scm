;;;schemea.nw:559
(val emptystore '((next 0)))
;;;scheme.nw:4211
(define find-c (key alist success-cont failure-cont)
   (letrec
       ([search (lambda (alist)
                   (if (null? alist)
                       (failure-cont)
                       (if (equal? key (alist-first-key alist))
                           (success-cont (alist-first-attribute alist))
                           (search (cdr alist)))))])
     (search alist)))
;;;schemea.nw:564
(val sigma emptystore)
(define load  (l)   (find-c l sigma (lambda (x) x)
                            (lambda () (error (list2 'unbound-location: l)))))
(define store (l v) (begin (set sigma (bind l v sigma)) v))
;;;schemea.nw:573
(define allocate (value)
  (let*
    ([loc (load 'next)])
    (begin
       (store 'next (+ loc 1))
       (store loc value)
       loc)))
;;;schemea.nw:587
(define bindalloc (name v env)
  (bind name (allocate v) env))
(define bindalloclist (xs vs env)
  (if (and (null? xs) (null? vs))
    env
    (bindalloclist (cdr xs) (cdr vs) (bindalloc (car xs) (car vs) env))))
;;;schemea.nw:615
(define apply-prim (prim)
  (lambda (args)
    (if (null? args)
      (error 'missing-arguments-to-primitive)
      (if (null? (cdr args))
        (prim (car args))
        (if (null? (cddr args))
          (prim (car args) (cadr args))
          (error (list2 'all-primitives-expect-one-or-two-arguments---got args)))))))
;;;schemea.nw:638
(define primenv ()
  (let*
      ([env '()]
       [env (bindalloc '+ (apply-prim +) env)]
       [env (bindalloc '- (apply-prim -) env)]
       [env (bindalloc '* (apply-prim *) env)]
       [env (bindalloc '/ (apply-prim /) env)]
       [env (bindalloc '< (apply-prim <) env)]
       [env (bindalloc '> (apply-prim >) env)]
       [env (bindalloc '= (apply-prim =) env)]
       [env (bindalloc 'car        (apply-prim car)        env)]
       [env (bindalloc 'cdr        (apply-prim cdr)        env)]
       [env (bindalloc 'cons       (apply-prim cons)       env)]
       [env (bindalloc 'println    (apply-prim println)    env)]
       [env (bindalloc 'print      (apply-prim print)      env)]
       [env (bindalloc 'printu     (apply-prim printu)     env)]
       [env (bindalloc 'error      (apply-prim error)      env)]
       [env (bindalloc 'boolean?   (apply-prim boolean?)   env)]
       [env (bindalloc 'null?      (apply-prim null?)      env)]
       [env (bindalloc 'number?    (apply-prim number?)    env)]
       [env (bindalloc 'symbol?    (apply-prim symbol?)    env)]
       [env (bindalloc 'procedure? (apply-prim procedure?) env)]
       [env (bindalloc 'pair?      (apply-prim pair?)      env)])
    env))
;;;schemea.nw:702
(define find-variable (x env)
  (find-c x env (lambda (x) x) (lambda () (error (list2 'unbound-variable: x)))))
;;;schemea.nw:731
(define holds-exactly? (xs n)
  (if (= n 0)
    (null? xs)
    (if (null? xs)
      #f
      (holds-exactly? (cdr xs) (- n 1)))))
   (check-assert (holds-exactly? '(a b c) 3))
   (check-assert (not (holds-exactly? '(a b) 3)))
   (check-assert (not (holds-exactly? '(a b c d) 3)))
;;;schemea.nw:741
(define unary (name f rest)
  (if (holds-exactly? rest 1)
    (f (car rest))
    (error (list3 name 'expression-needs-one-argument,-got rest))))
;;;schemea.nw:746
(define binary (name f rest)
  (if (holds-exactly? rest 2)
    (f (car rest) (cadr rest))
    (error (list3 name 'expression-needs-two-arguments,-got rest))))
;;;schemea.nw:751
(define trinary (name f rest)
  (if (holds-exactly? rest 3)
    (f (car rest) (cadr rest) (caddr rest))
    (error (list3 name 'expression-needs-three-arguments,-got rest))))
;;;schemea.nw:674
(define eval (env)
   (letrec
       ([ev (lambda (e) 
;;;schemea.nw:689
(if (symbol? e)
  (load (find-variable e env))
  (if (atom? e)
    e
    (let ([first (car e)]
          [rest  (cdr e)])
      (if (exists? ((curry =) first) '(set if while lambda quote begin))
          
;;;schemea.nw:718
(if (= first 'set)    (binary  'set    meta-set    rest)
(if (= first 'if)     (trinary 'if     meta-if     rest)
(if (= first 'while)  (binary  'while  meta-while  rest)
(if (= first 'lambda) (binary  'lambda meta-lambda rest)
(if (= first 'quote)  (unary   'quote  meta-quote  rest)
(if (= first 'begin)  (meta-begin rest)
(error (list2 'this-cannot-happen---bad-ast first))))))))
;;;schemea.nw:697
          
;;;schemea.nw:710
((ev first) (map ev rest))
;;;schemea.nw:697
                                                                                       ))))
;;;schemea.nw:676
                                                                                        )]
        
;;;schemea.nw:759
(meta-quote (lambda (e) e))
(meta-if    (lambda (e1 e2 e3) (if (ev e1) (ev e2) (ev e3))))
(meta-while (lambda (condition body) (while (ev condition) (ev body))))
;;;schemea.nw:765
(meta-set   (lambda (v e)
              (let ([loc (find-variable v env)])
                 (if (null? loc)
                    (error (list2 'set-unbound-variable v))
                    (store loc (ev e))))))
;;;schemea.nw:774
(meta-begin (lambda (es) (foldl (lambda (e result) (ev e)) '() es)))
;;;schemea.nw:780
(meta-lambda (lambda (formals body)
               (if (all? symbol? formals)
                 (lambda (actuals)
                   ((eval (bindalloclist formals actuals env)) body))
                 (error (list2 'lambda-with-bad-formals: formals)))))
;;;schemea.nw:677
                                                                             )
     ev))

;;;schemea.nw:818
(define meta-val (env) 
  (lambda (x e)
    (if (symbol? x)
        (let* ([env (find-c x env (lambda (_) env) (lambda () (bindalloc x '() env)))])
          (begin
            ((eval env) (list3 'set x e))
            env))
        (error (list2 'val-tried-to-bind-non-symbol x)))))
;;;schemea.nw:829
(define meta-define (env) 
  (lambda (name formals body)
    ((meta-val env) name (list3 'lambda formals body))))
;;;schemea.nw:838
(define meta-exp (e env)
  (begin
    (println ((eval env) e))
    env))
;;;schemea.nw:791
(define evaldef (e env)
  (if (pair? e)
    (let ([first (car e)]
          [rest  (cdr e)])
      (if (= first 'val)
        (binary 'val (meta-val env) rest)
        (if (= first 'define)
            (trinary 'define (meta-define env) rest)
            (meta-exp e env))))
    (meta-exp e env)))
;;;schemea.nw:849
(define read-eval-print (env es)
    (foldl evaldef env es))
;;;schemea.nw:858
(define run (es)
  (begin (read-eval-print (primenv) es) 0))
