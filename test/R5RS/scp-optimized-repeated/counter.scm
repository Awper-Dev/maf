(define (repeat n l)
  (if (not (= n 5000)) (begin (l) (repeat (+ n 1) l))))

(repeat 0 (lambda ()
            #f
            ))