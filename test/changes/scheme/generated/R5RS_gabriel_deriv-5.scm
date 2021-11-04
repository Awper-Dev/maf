; Changes:
; * removed: 0
; * added: 1
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 1
; * calls to id fun: 2
(letrec ((deriv (lambda (a)
                  (<change>
                     ()
                     '+)
                  (<change>
                     @sensitivity:FA
                     ((lambda (x) x) @sensitivity:FA))
                  (<change>
                     (if (not (pair? a))
                        (if (eq? a 'x) 1 0)
                        (if (eq? (car a) '+)
                           (cons '+ (map deriv (cdr a)))
                           (if (eq? (car a) '-)
                              (cons '- (map deriv (cdr a)))
                              (if (eq? (car a) '*)
                                 (list '* a (cons '+ (map (lambda (a) @sensitivity:FA (list '/ (deriv a) a)) (cdr a))))
                                 (if (eq? (car a) '/)
                                    (list
                                       '-
                                       (list '/ (deriv (cadr a)) (caddr a))
                                       (list '/ (cadr a) (list '* (caddr a) (caddr a) (deriv (caddr a)))))
                                    (error "No derivation method available"))))))
                     ((lambda (x) x)
                        (if (not (pair? a))
                           (if (eq? a 'x) 1 0)
                           (if (eq? (car a) '+)
                              (cons '+ (map deriv (cdr a)))
                              (if (eq? (car a) '-)
                                 (cons '- (map deriv (cdr a)))
                                 (if (eq? (car a) '*)
                                    (<change>
                                       (list '* a (cons '+ (map (lambda (a) @sensitivity:FA (list '/ (deriv a) a)) (cdr a))))
                                       (if (eq? (car a) '/)
                                          (list
                                             '-
                                             (list '/ (deriv (cadr a)) (caddr a))
                                             (list '/ (cadr a) (list '* (caddr a) (caddr a) (deriv (caddr a)))))
                                          (error "No derivation method available")))
                                    (<change>
                                       (if (eq? (car a) '/)
                                          (list
                                             '-
                                             (list '/ (deriv (cadr a)) (caddr a))
                                             (list '/ (cadr a) (list '* (caddr a) (caddr a) (deriv (caddr a)))))
                                          (error "No derivation method available"))
                                       (list '* a (cons '+ (map (lambda (a) @sensitivity:FA (list '/ (deriv a) a)) (cdr a)))))))))))))
         (result (deriv
                   (__toplevel_cons
                      '+
                      (__toplevel_cons
                         (__toplevel_cons '* (__toplevel_cons 3 (__toplevel_cons 'x (__toplevel_cons 'x ()))))
                         (__toplevel_cons
                            (__toplevel_cons '* (__toplevel_cons 'a (__toplevel_cons 'x (__toplevel_cons 'x ()))))
                            (__toplevel_cons
                               (__toplevel_cons '* (__toplevel_cons 'b (__toplevel_cons 'x ())))
                               (__toplevel_cons 5 ()))))))))
   (equal?
      result
      (__toplevel_cons
         '+
         (__toplevel_cons
            (__toplevel_cons
               '*
               (__toplevel_cons
                  (__toplevel_cons '* (__toplevel_cons 3 (__toplevel_cons 'x (__toplevel_cons 'x ()))))
                  (__toplevel_cons
                     (__toplevel_cons
                        '+
                        (__toplevel_cons
                           (__toplevel_cons '/ (__toplevel_cons 0 (__toplevel_cons 3 ())))
                           (__toplevel_cons
                              (__toplevel_cons '/ (__toplevel_cons 1 (__toplevel_cons 'x ())))
                              (__toplevel_cons (__toplevel_cons '/ (__toplevel_cons 1 (__toplevel_cons 'x ()))) ()))))
                     ())))
            (__toplevel_cons
               (__toplevel_cons
                  '*
                  (__toplevel_cons
                     (__toplevel_cons '* (__toplevel_cons 'a (__toplevel_cons 'x (__toplevel_cons 'x ()))))
                     (__toplevel_cons
                        (__toplevel_cons
                           '+
                           (__toplevel_cons
                              (__toplevel_cons '/ (__toplevel_cons 0 (__toplevel_cons 'a ())))
                              (__toplevel_cons
                                 (__toplevel_cons '/ (__toplevel_cons 1 (__toplevel_cons 'x ())))
                                 (__toplevel_cons (__toplevel_cons '/ (__toplevel_cons 1 (__toplevel_cons 'x ()))) ()))))
                        ())))
               (__toplevel_cons
                  (__toplevel_cons
                     '*
                     (__toplevel_cons
                        (__toplevel_cons '* (__toplevel_cons 'b (__toplevel_cons 'x ())))
                        (__toplevel_cons
                           (__toplevel_cons
                              '+
                              (__toplevel_cons
                                 (__toplevel_cons '/ (__toplevel_cons 0 (__toplevel_cons 'b ())))
                                 (__toplevel_cons (__toplevel_cons '/ (__toplevel_cons 1 (__toplevel_cons 'x ()))) ())))
                           ())))
                  (__toplevel_cons 0 ())))))))