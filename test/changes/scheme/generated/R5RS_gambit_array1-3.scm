; Changes:
; * removed: 0
; * added: 2
; * swaps: 1
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 0
(letrec ((create-x (lambda (n)
                     (letrec ((result (make-vector n 0)))
                        (letrec ((__do_loop (lambda (i)
                                              (if (>= i n)
                                                 result
                                                 (begin
                                                    (vector-set! result i i)
                                                    (__do_loop (+ i 1)))))))
                           (__do_loop 0)))))
         (create-y (lambda (x)
                     (let* ((n (vector-length x))
                            (result (make-vector n 0)))
                        (letrec ((__do_loop (lambda (i)
                                              (if (< i 0)
                                                 result
                                                 (begin
                                                    (<change>
                                                       ()
                                                       (display __do_loop))
                                                    (<change>
                                                       (vector-set! result i (vector-ref x i))
                                                       (__do_loop (- i 1)))
                                                    (<change>
                                                       (__do_loop (- i 1))
                                                       (vector-set! result i (vector-ref x i))))))))
                           (__do_loop (- n 1))))))
         (my-try (lambda (n)
                   (vector-length (create-y (create-x n)))))
         (go (lambda (n)
               (<change>
                  ()
                  (letrec ((loop (lambda (repeat result)
                                   (if (> repeat 0)
                                      (loop (- repeat 1) (my-try n))
                                      result))))
                     loop))
               ((letrec ((loop (lambda (repeat result)
                                (if (> repeat 0)
                                   (loop (- repeat 1) (my-try n))
                                   result))))
                  loop)
                  100
                  ()))))
   (= 200 (go 200)))