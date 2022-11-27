(define (repeat n f)
  (define (iter ctr)
    (cond ((not (= ctr n))
           (f)
           (iter (+ ctr 1)))))
  (iter 0))

(define (optimized-constant-folding)
  (define x 120)
  x)

(repeat 10000 optimized-constant-folding)
