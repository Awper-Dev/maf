; Changes:
; * removed: 0
; * added: 1
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((create-n (lambda (n)
                     (letrec ((__do_loop (lambda (n a)
                                           (if (= n 0) a (__do_loop (- n 1) (cons () a))))))
                        (__do_loop n ()))))
         (*ll* (create-n 200))
         (iterative-div2 (lambda (l)
                           (letrec ((__do_loop (lambda (l a)
                                                 (if (null? l)
                                                    a
                                                    (__do_loop (cddr l) (cons (car l) a))))))
                              (<change>
                                 ()
                                 (display __do_loop))
                              (__do_loop l ())))))
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