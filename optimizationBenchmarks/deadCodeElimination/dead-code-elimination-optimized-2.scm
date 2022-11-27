(define (repeat n f)
  (define (iter ctr)
    (cond ((not (= ctr n))
           (f)
           (iter (+ ctr 1)))))
  (iter 0))

(define (dead-code-optimized-2)
  (* 2 3 4))

(repeat 10000 dead-code-optimized-2)