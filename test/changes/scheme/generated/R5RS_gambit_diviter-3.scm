; Changes:
; * removed: 0
; * added: 1
; * swaps: 0
; * negated predicates: 1
; * swapped branches: 0
; * calls to id fun: 1
(letrec ((create-n (lambda (n)
                     (<change>
                        (letrec ((__do_loop (lambda (n a)
                                              (if (= n 0) a (__do_loop (- n 1) (cons () a))))))
                           (__do_loop n ()))
                        ((lambda (x) x)
                           (letrec ((__do_loop (lambda (n a)
                                                 (if (= n 0) a (__do_loop (- n 1) (cons () a))))))
                              (__do_loop n ()))))))
         (*ll* (create-n 200))
         (iterative-div2 (lambda (l)
                           (letrec ((__do_loop (lambda (l a)
                                                 (if (<change> (null? l) (not (null? l)))
                                                    a
                                                    (__do_loop (cddr l) (cons (car l) a))))))
                              (__do_loop l ())))))
   (<change>
      ()
      (display ()))
   (equal?
      (iterative-div2 *ll*)
      (__toplevel_cons
         ()
         (__toplevel_cons
            ()
            (__toplevel_cons
               ()
               (__toplevel_cons
                  ()
                  (__toplevel_cons
                     ()
                     (__toplevel_cons
                        ()
                        (__toplevel_cons
                           ()
                           (__toplevel_cons
                              ()
                              (__toplevel_cons
                                 ()
                                 (__toplevel_cons
                                    ()
                                    (__toplevel_cons
                                       ()
                                       (__toplevel_cons
                                          ()
                                          (__toplevel_cons
                                             ()
                                             (__toplevel_cons
                                                ()
                                                (__toplevel_cons
                                                   ()
                                                   (__toplevel_cons
                                                      ()
                                                      (__toplevel_cons
                                                         ()
                                                         (__toplevel_cons
                                                            ()
                                                            (__toplevel_cons
                                                               ()
                                                               (__toplevel_cons
                                                                  ()
                                                                  (__toplevel_cons
                                                                     ()
                                                                     (__toplevel_cons
                                                                        ()
                                                                        (__toplevel_cons
                                                                           ()
                                                                           (__toplevel_cons
                                                                              ()
                                                                              (__toplevel_cons
                                                                                 ()
                                                                                 (__toplevel_cons
                                                                                    ()
                                                                                    (__toplevel_cons
                                                                                       ()
                                                                                       (__toplevel_cons
                                                                                          ()
                                                                                          (__toplevel_cons
                                                                                             ()
                                                                                             (__toplevel_cons
                                                                                                ()
                                                                                                (__toplevel_cons
                                                                                                   ()
                                                                                                   (__toplevel_cons
                                                                                                      ()
                                                                                                      (__toplevel_cons
                                                                                                         ()
                                                                                                         (__toplevel_cons
                                                                                                            ()
                                                                                                            (__toplevel_cons
                                                                                                               ()
                                                                                                               (__toplevel_cons
                                                                                                                  ()
                                                                                                                  (__toplevel_cons
                                                                                                                     ()
                                                                                                                     (__toplevel_cons
                                                                                                                        ()
                                                                                                                        (__toplevel_cons
                                                                                                                           ()
                                                                                                                           (__toplevel_cons
                                                                                                                              ()
                                                                                                                              (__toplevel_cons
                                                                                                                                 ()
                                                                                                                                 (__toplevel_cons
                                                                                                                                    ()
                                                                                                                                    (__toplevel_cons
                                                                                                                                       ()
                                                                                                                                       (__toplevel_cons
                                                                                                                                          ()
                                                                                                                                          (__toplevel_cons
                                                                                                                                             ()
                                                                                                                                             (__toplevel_cons
                                                                                                                                                ()
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   ()
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      ()
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         ()
                                                                                                                                                         (__toplevel_cons
                                                                                                                                                            ()
                                                                                                                                                            (__toplevel_cons
                                                                                                                                                               ()
                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                  ()
                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                     ()
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        ()
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           ()
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              ()
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 ()
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    ()
                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                       ()
                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                          ()
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             ()
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                ()
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   ()
                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                      ()
                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                         ()
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            ()
                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                               ()
                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                  ()
                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                     ()
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        ()
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           ()
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              ()
                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                 ()
                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                    ()
                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                       ()
                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                          ()
                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                             ()
                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                ()
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   ()
                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                      ()
                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                         ()
                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                            ()
                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                               ()
                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                  ()
                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                     ()
                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                        ()
                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                           ()
                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                              ()
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 ()
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    ()
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       ()
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          ()
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             ()
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                ()
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   ()
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      ()
                                                                                                                                                                                                                                                                                                      (__toplevel_cons () (__toplevel_cons () (__toplevel_cons () (__toplevel_cons () ()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))