; Changes:
; * removed: 0
; * added: 0
; * swaps: 1
; * negated predicates: 0
; * swapped branches: 1
; * calls to id fun: 0
(letrec ((MaakLampje (lambda (aantal)
                       (letrec ((state 'off)
                                (on! (lambda ()
                                       (set! state 'on)))
                                (off! (lambda ()
                                        (set! state 'off)))
                                (broken! (lambda ()
                                           (set! state 'broken)))
                                (on? (lambda ()
                                       (eq? state 'on)))
                                (off? (lambda ()
                                        (eq? state 'off)))
                                (broken? (lambda ()
                                           (eq? state 'broken)))
                                (switch! (lambda ()
                                           (set! aantal (- aantal 1))
                                           (if (< aantal 0)
                                              (broken!)
                                              (if (off?) (on!) (if (on?) (off!) #f)))
                                           (not (broken?))))
                                (change! (lambda (nieuw)
                                           (off!)
                                           (set! aantal nieuw)
                                           'changed))
                                (dispatch (lambda (msg)
                                            (if (eq? msg 'switch!)
                                               (switch!)
                                               (if (eq? msg 'on?)
                                                  (on?)
                                                  (if (eq? msg 'off?)
                                                     (off?)
                                                     (if (eq? msg 'test?)
                                                        (broken?)
                                                        (if (eq? msg 'change!)
                                                           change!
                                                           (error "Message not understood.")))))))))
                          dispatch)))
         (philips (MaakLampje 5)))
   (if (not (philips 'test?))
      (if (not (philips 'on?))
         (if (philips 'off?)
            (if (philips 'switch!)
               (if (philips 'switch!)
                  (if (philips 'switch!)
                     (<change>
                        (if (philips 'switch!)
                           (if (philips 'switch!)
                              (if (not (philips 'switch!))
                                 (if (philips 'test?)
                                    (if (begin ((philips 'change!) 10) (not (philips 'test?)))
                                       (philips 'off?)
                                       #f)
                                    #f)
                                 #f)
                              #f)
                           #f)
                        #f)
                     (<change>
                        #f
                        (if (philips 'switch!)
                           (if (philips 'switch!)
                              (if (not (philips 'switch!))
                                 (if (philips 'test?)
                                    (if (begin (not (philips 'test?)) ((philips 'change!) 10))
                                       (philips 'off?)
                                       #f)
                                    #f)
                                 #f)
                              #f)
                           #f)))
                  #f)
               #f)
            #f)
         #f)
      #f))