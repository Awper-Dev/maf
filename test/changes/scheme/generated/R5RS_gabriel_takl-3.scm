; Changes:
; * removed: 1
; * added: 0
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 1
(letrec ((listn (lambda (n)
                  (<change>
                     @sensitivity:FA
                     ())
                  (if (= n 0) () (cons n (listn (- n 1))))))
         (shorterp (lambda (x y)
                     (<change>
                        @sensitivity:FA
                        ((lambda (x) x) @sensitivity:FA))
                     (if (not (null? y))
                        (let ((__or_res (null? x)))
                           (if __or_res __or_res (shorterp (cdr x) (cdr y))))
                        #f)))
         (mas (lambda (x y z)
                @sensitivity:FA
                (if (not (shorterp y x))
                   z
                   (mas (mas (cdr x) y z) (mas (cdr y) z x) (mas (cdr z) x y))))))
   (let ((result (__toplevel_cons
                   7
                   (__toplevel_cons
                      6
                      (__toplevel_cons
                         5
                         (__toplevel_cons 4 (__toplevel_cons 3 (__toplevel_cons 2 (__toplevel_cons 1 ())))))))))
      (equal? (mas (listn 18) (listn 12) (listn 6)) result)))