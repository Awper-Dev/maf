(define (f a b c d e)
  (<change> (+ a b) (e))
  (c d)
  (<change> (e) (h (lambda (a b c d e) (d (lambda (t g f r d) (if (> t g) f (lambda (a b c d e) 3))))))))
(define (g a)
  (a (lambda (a b c d e) #f)))
(define (j)
  (<change> #t (list f g h)))
(define (h fn)
  (if (number? fn)
      (<change> (g 1) (h (lambda (a b c d e) 2)))
      (fn 1 0 g h j)))
(h f)