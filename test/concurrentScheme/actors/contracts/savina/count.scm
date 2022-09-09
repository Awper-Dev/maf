;; Adapted from Savina benchmarks ("Counting Actor" benchmarks, coming from Theron)
(define N (int-top))
(define producer-actor
  (actor "producer" (counter)
           (increment ()
                      (letrec ((loop (lambda (n)
                                       (if (> n 0)
                                           (begin
                                             (send counter increment)
                                             (loop (- n 1)))
                                           'done))))
                        (loop N)
                        (send counter retrieve a/self)
                        (become producer-actor counter)))
           (result (count)
                   (if (= count N)
                       (display "Success!")
                       (error "Error!"))
                   (terminate))))
(define counting-actor
 (actor "counting" (count)
          (increment ()
                     (become counting-actor (+ count 1)))
          (retrieve (to)
                    (send to result count)
                    (terminate))))
(define counter (create counting-actor 0))
(define producer (create producer-actor counter))
(send producer increment)
