(define *global* 1)
(define (special-fac n)
  (if (= n 0)
      (begin (set! *global* (random 1))
             1)
      (* n (special-fac (- n 1)))))

(special-fac 5)
*global*
