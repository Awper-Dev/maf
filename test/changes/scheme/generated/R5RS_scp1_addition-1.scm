; Changes:
; * removed: 0
; * added: 0
; * swaps: 0
; * negated predicates: 1
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((1- (lambda (x)
               (- x 1)))
         (1+ (lambda (x)
               (+ 1 x)))
         (rec-add (lambda (a b)
                    (if (= b 0) a (1+ (rec-add a (1- b))))))
         (iter-add (lambda (a b)
                     (if (<change> (= a 0) (not (= a 0)))
                        b
                        (if (< a 0)
                           (iter-add (1+ a) (1- b))
                           (if (> a 0) (iter-add (1- a) (1+ b)) #f))))))
   (= 9 (rec-add 4 5) (iter-add 4 5)))