; Changes:
; * removed: 1
; * added: 0
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((tak (lambda (x y z k)
                @sensitivity:FA
                (if (not (< y x))
                   (k z)
                   (tak
                      (- x 1)
                      y
                      z
                      (lambda (v1)
                         (<change>
                            @sensitivity:FA
                            ())
                         (tak
                            (- y 1)
                            z
                            x
                            (lambda (v2)
                               @sensitivity:FA
                               (tak (- z 1) x y (lambda (v3) @sensitivity:FA (tak v1 v2 v3 k))))))))))
         (res (tak 20 10 5 (lambda (a) @sensitivity:FA a))))
   res)