(define (repeat n l)
  (if (not (= n 5000)) (begin (l) (repeat (+ n 1) l))))
(define (show namen punten test?)
  (if (null? namen)
      '()
      (let ((res (show (cdr namen) (cdr punten) test?)))
        (if (test? (car punten))
            (cons (car namen) res)
            res))))

(define (one namen punten)
  (define (één-buis? punten)
    (if (null? punten)
        #f
        (let ((punt (car punten))
              (rest (cdr punten)))
          (if (< punt 10)
              (geen-buis? rest)
              (één-buis? rest)))))


  (define (geen-buis? punten)
    (if (null? punten)
        #t
        (let ((punt (car punten))
              (rest (cdr punten)))
          (if (< punt 10)
              #f
              (geen-buis? rest)))))

  (show namen punten één-buis?))
(repeat 0 (lambda ()
(equal? (one '(wendy dirk kris jan eef)
       '((12 13 15 18) (7 10 14 17) (13 8 7 11)
                       (9 12 11 10) (18 14 17 19)))
        '(dirk jan))))