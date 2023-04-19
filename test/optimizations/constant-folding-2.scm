(define *global* (random 5))

(define (fac n)
  (if (= n 0)
      (begin (set! *global* (random 2)) 1)
      (* n (fac (- n 1)))))
(define (fib n)
    (if (< n 2)
        n
        (+ (fib (- n 2)) (fib (- n 1)))))

(fac 5)
(fib 100)

*global*