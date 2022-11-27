(define (repeat n f)
  (define (iter ctr)
    (cond ((not (= ctr n))
           (f)
           (iter (+ ctr 1)))))
  (iter 0))

(define (constant-propagation-start)
  (define x 14)
  (define y (- 7 (/ x 2)))
  (* y (+ (/ 28 x) 2)))

(repeat 10000 constant-propagation-start)