; Changes:
; * removed: 0
; * added: 1
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((t (lambda (x)
              (t (+ x 1)))))
   (<change>
      ()
      (t 0))
   (t 0))