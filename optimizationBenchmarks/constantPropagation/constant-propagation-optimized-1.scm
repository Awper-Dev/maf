(define (repeat n f)
  (define (iter ctr)
    (cond ((not (= ctr n))
           (f)
           (iter (+ ctr 1)))))
  (iter 0))

(define (constant-propagation-x-propagated)
  (define x 14)
  (define y (- 7 (/ 14 2)))
  (* y (+ (/ 28 14) 2)))

(repeat 10000 constant-propagation-x-propagated)