(define (repeat n f)
  (define (iter ctr)
    (cond ((not (= ctr n))
           (f)
           (iter (+ ctr 1)))))
  (iter 0))

(define (dead-code)
  0)

(repeat 10000 dead-code)