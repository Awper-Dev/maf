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
                                      (let ((___or_res1 (if (null? _a0) (null? ()) #f)))
                                        (if ___or_res1
                                          ___or_res1
                                          (let ((___or_res2 #f))
                                            (if #f
                                              #f
                                              (let ((___or_res3 (if (pair? _a0)
                                                                  (if (pair? ())
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
                               (letrec ((_één-buis?0 (lambda (_punten2)
                                                       (if (null? ())
                                                         #f
                                                         (let ((_punt0 (car _punten2))
                                                                (_rest0 ()))
                                                           (if (< _punt0 10) (_geen-buis?0 _rest0) #f)))))
                                         (_geen-buis?0 (lambda (_punten3)
                                                         (if (null? ())
                                                           #t
                                                           (let ((_punt1 (car _punten3))
                                                                  (_rest1 ()))
                                                             (if (< _punt1 10) #f #t))))))
                                 (_show0 _namen1 _punten1 _één-buis?0))))
                      (__00 (_equal?0
                              (_one0
                                (___toplevel_cons0
                                  'wendy
                                  (___toplevel_cons0
                                    'dirk
                                    (___toplevel_cons0 'kris (___toplevel_cons0 'jan (___toplevel_cons0 'eef ())))))
                                (___toplevel_cons0
                                  (___toplevel_cons0 12 (___toplevel_cons0 13 (___toplevel_cons0 15 (___toplevel_cons0 18 ()))))
                                  (___toplevel_cons0
                                    (___toplevel_cons0 7 (___toplevel_cons0 10 (___toplevel_cons0 14 (___toplevel_cons0 17 ()))))
                                    (___toplevel_cons0
                                      (___toplevel_cons0 13 (___toplevel_cons0 8 (___toplevel_cons0 7 (___toplevel_cons0 11 ()))))
                                      (___toplevel_cons0
                                        (___toplevel_cons0 9 (___toplevel_cons0 12 (___toplevel_cons0 11 (___toplevel_cons0 10 ()))))
                                        (___toplevel_cons0
                                          (___toplevel_cons0 18 (___toplevel_cons0 14 (___toplevel_cons0 17 (___toplevel_cons0 19 ()))))
                                          ()))))))
                              (___toplevel_cons0 'dirk (___toplevel_cons0 'jan ())))))
              __00)
            ))