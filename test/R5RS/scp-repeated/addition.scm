(define (repeat n l)
  (if (not (= n 5000)) (begin (l) (repeat (+ n 1) l))))
(define (1- x) (- x 1))
(define (1+ x) (+ 1 x))

(define (rec-add a b)
  (if (= b 0)
      a
      (1+ (rec-add a (1- b)))))

(define (iter-add a b)
  (cond
    ((= a 0) b)
    ((< a 0) (iter-add (1+ a) (1- b)))
    ((> a 0) (iter-add (1- a) (1+ b)))))
(repeat 0 (lambda ()
(= 9
   (rec-add 0 9)
   (iter-add 4 5))))
