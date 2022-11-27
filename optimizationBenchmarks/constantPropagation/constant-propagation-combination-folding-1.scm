(define (repeat n f)
  (define (iter ctr)
    (cond ((not (= ctr n))
           (f)
           (iter (+ ctr 1)))))
  (iter 0))

(define (second-constant-folding-after-propagation)
  (define x 14)
  (define y 0)
  0)

(repeat 10000 second-constant-folding-after-propagation)