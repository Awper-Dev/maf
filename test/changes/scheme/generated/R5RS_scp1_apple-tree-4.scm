; Changes:
; * removed: 0
; * added: 1
; * swaps: 0
; * negated predicates: 1
; * swapped branches: 2
; * calls to id fun: 2
(letrec ((boom (__toplevel_cons
                 (__toplevel_cons 'blad (__toplevel_cons (__toplevel_cons 'appel 'golden) ()))
                 (__toplevel_cons
                    (__toplevel_cons 'blad (__toplevel_cons (__toplevel_cons 'appel 'granny) ()))
                    (__toplevel_cons
                       (__toplevel_cons
                          (__toplevel_cons (__toplevel_cons 'appel 'golden) (__toplevel_cons 'blad ()))
                          (__toplevel_cons 'blad (__toplevel_cons (__toplevel_cons 'appel 'cox) ())))
                       ()))))
         (blad? (lambda (boom)
                  (eq? boom 'blad)))
         (appel? (lambda (boom)
                   (if (pair? boom)
                      (<change>
                         (eq? (car boom) 'appel)
                         #f)
                      (<change>
                         #f
                         (eq? (car boom) 'appel)))))
         (type (lambda (appel)
                 (cdr appel)))
         (leafs (lambda (boom)
                  (if (null? boom)
                     0
                     (if (blad? boom)
                        1
                        (if (appel? boom)
                           0
                           (+ (leafs (car boom)) (leafs (cdr boom))))))))
         (all-apples (lambda (boom)
                       (if (null? boom)
                          ()
                          (if (blad? boom)
                             ()
                             (if (appel? boom)
                                (list (type boom))
                                (append (all-apples (car boom)) (all-apples (cdr boom))))))))
         (conditional-append (lambda (l1 l2)
                               (if (null? l1)
                                  l2
                                  (if (member (car l1) l2)
                                     (conditional-append (cdr l1) l2)
                                     (cons (car l1) (conditional-append (cdr l1) l2))))))
         (apple-types (lambda (boom)
                        (if (null? boom)
                           ()
                           (if (<change> (blad? boom) (not (blad? boom)))
                              ()
                              (if (appel? boom)
                                 (list (type boom))
                                 (conditional-append (apple-types (car boom)) (apple-types (cdr boom))))))))
         (bewerk-boom (lambda (boom doe-blad doe-appel combiner init)
                        (<change>
                           ()
                           car)
                        (if (null? boom)
                           init
                           (if (blad? boom)
                              (doe-blad boom)
                              (if (appel? boom)
                                 (doe-appel boom)
                                 (combiner
                                    (bewerk-boom (car boom) doe-blad doe-appel combiner init)
                                    (bewerk-boom (cdr boom) doe-blad doe-appel combiner init)))))))
         (leafs-dmv-bewerk (lambda (boom)
                             (bewerk-boom boom (lambda (blad) (<change> 1 ((lambda (x) x) 1))) (lambda (appel) 0) + 0)))
         (all-apples-dmv-bewerk (lambda (boom)
                                  (bewerk-boom boom (lambda (blad) ()) (lambda (appel) (list (type appel))) append ())))
         (apple-types-dmv-bewerk (lambda (boom)
                                   (bewerk-boom
                                      boom
                                      (lambda (blad)
                                         (<change>
                                            ()
                                            ((lambda (x) x) ())))
                                      (lambda (appel)
                                         (list (type appel)))
                                      conditional-append
                                      ()))))
   (if (= (leafs boom) 4)
      (<change>
         (if (equal? (all-apples boom) (__toplevel_cons 'golden (__toplevel_cons 'granny (__toplevel_cons 'golden (__toplevel_cons 'cox ())))))
            (if (equal? (apple-types boom) (__toplevel_cons 'granny (__toplevel_cons 'golden (__toplevel_cons 'cox ()))))
               (if (= (leafs-dmv-bewerk boom) 4)
                  (if (equal? (all-apples-dmv-bewerk boom) (__toplevel_cons 'golden (__toplevel_cons 'granny (__toplevel_cons 'golden (__toplevel_cons 'cox ())))))
                     (equal?
                        (apple-types-dmv-bewerk boom)
                        (__toplevel_cons 'granny (__toplevel_cons 'golden (__toplevel_cons 'cox ()))))
                     #f)
                  #f)
               #f)
            #f)
         #f)
      (<change>
         #f
         (if (equal? (all-apples boom) (__toplevel_cons 'golden (__toplevel_cons 'granny (__toplevel_cons 'golden (__toplevel_cons 'cox ())))))
            (if (equal? (apple-types boom) (__toplevel_cons 'granny (__toplevel_cons 'golden (__toplevel_cons 'cox ()))))
               (if (= (leafs-dmv-bewerk boom) 4)
                  (if (equal? (all-apples-dmv-bewerk boom) (__toplevel_cons 'golden (__toplevel_cons 'granny (__toplevel_cons 'golden (__toplevel_cons 'cox ())))))
                     (equal?
                        (apple-types-dmv-bewerk boom)
                        (__toplevel_cons 'granny (__toplevel_cons 'golden (__toplevel_cons 'cox ()))))
                     #f)
                  #f)
               #f)
            #f))))