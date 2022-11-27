(define (repeat n f)
  (define (iter ctr)
    (cond ((not (= ctr n))
           (f)
           (iter (+ ctr 1)))))
  (iter 0))

(define (dead-code-2)
  (if #t
      (* 2 3 4)
      (display "I will never be evaluated")))

(repeat 10000 dead-code-2)