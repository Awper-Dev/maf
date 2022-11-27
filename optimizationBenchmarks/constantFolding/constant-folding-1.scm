(define (repeat n f)
  (define (iter ctr)
    (cond ((not (= ctr n))
           (f)
           (iter (+ ctr 1)))))
  (iter 0))

(define (constant-folding)
  (define x (* 5 3 2 4))
  x)

(repeat 10000 constant-folding)