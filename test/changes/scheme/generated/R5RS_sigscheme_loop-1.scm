; Changes:
; * removed: 0
; * added: 1
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((loop (lambda (i l)
                 (if (< i l) (loop (+ 1 i) l) l))))
   (<change>
      ()
      loop)
   (loop 0 8000))