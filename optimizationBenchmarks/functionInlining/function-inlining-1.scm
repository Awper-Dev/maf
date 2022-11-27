(define (repeat n f)
  (define (iter ctr)
    (cond ((not (= ctr n))
           (f)
           (iter (+ ctr 1)))))
  (iter 0))

(define (function a b)
  (define x (+ a b))
  (define y (+ x 2))
  (+ a y x))

(define (function-inlining)
  (define result (function 2 3))
  (define z (* result 2))
  (+ z 3))

(repeat 10000 function-inlining)