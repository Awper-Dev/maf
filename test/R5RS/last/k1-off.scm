(define (repeat n l)
  (if (not (= n 5000)) (begin (l) (repeat (+ n 1) l))))


(repeat 0 (lambda ()
            (letrec ((_string=?0 (lambda (_s10 _s20)
                                   (assert (string? _s10))
                                   (assert (string? _s20))
                                   (if (= (string-length _s10) (string-length _s20))
                                     ((letrec ((_loop0 (lambda (_i0)
                                                         (if (< _i0 0)
                                                           #t
                                                           (if (char=? (string-ref _s10 _i0) (string-ref _s20 _i0))
                                                             (_loop0 (- _i0 1))
                                                             #f)))))
                                        _loop0)
                                       (- (string-length _s10) 1))
                                     #f)))
                      (___toplevel_cons0 cons)
                      (_equal?0 (lambda (_a0 _b0)
                                  (let ((___or_res0 (eq? _a0 _b0)))
                                    (if ___or_res0
                                      ___or_res0
                                      (let ((___or_res1 (if (null? _a0) (null? _b0) #f)))
                                        (if ___or_res1
                                          ___or_res1
                                          (let ((___or_res2 #f))
                                            (if #f
                                              #f
                                              (let ((___or_res3 (if (pair? _a0)
                                                                  (if (pair? _b0)
                                                                    (if (_equal?0 (car _a0) (car _b0))
                                                                      (_equal?0 (cdr _a0) ())
                                                                      #f)
                                                                    #f)
                                                                  #f)))
                                                (if ___or_res3 ___or_res3 #f))))))))))
                      (___toplevel_set-cdr!0 set-cdr!)
                      (___toplevel_cdr0 cdr)
                      (_show0 (lambda (_namen0 _punten0 _test?0)
                                ()))
                      (_one0 (lambda (_namen1 _punten1)
                               ()))
                      (__00 (_equal?0 () (___toplevel_cons0 'dirk (___toplevel_cons0 'jan ())))))
              __00)
            ))