; Changes:
; * removed: 0
; * added: 2
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 1
(letrec ((h (lambda (b)
              (letrec ((g (lambda (z)
                            z))
                       (f (lambda (k)
                            (if b (k 1) (k 2))))
                       (y (f (lambda (x) (<change> () x) (<change> x ((lambda (x) x) x))))))
                 (<change>
                    ()
                    y)
                 (g y))))
         (x (h #t))
         (y (h #f)))
   y)