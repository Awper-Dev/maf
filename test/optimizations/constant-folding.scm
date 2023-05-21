(let ((z 5))
  (let ((x (begin (set! z 3) 2)))
    (let ((y (begin (set! x 4) (+ x 3))))
        (set! y 30)
      z))

  (let ((x (begin (set! z 3) 2)))
      (let ((y (begin (+ x 3))))
          (set! y 30)
          y
        z))

  (let ((x (begin (set! z 3) 2)))
        (let ((y (begin (+ x 3))))
            (set! y 30)
          z))

  (let ((q 3))
    (let ((f 2))
        q)))

  (let ((f '()))
    f)