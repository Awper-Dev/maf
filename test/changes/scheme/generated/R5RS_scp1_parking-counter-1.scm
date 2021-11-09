; Changes:
; * removed: 1
; * added: 2
; * swaps: 2
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 4
(letrec ((create-counter (lambda (initial)
                           (letrec ((increase (lambda ()
                                                (set! initial (+ initial 1))))
                                    (decrease (lambda ()
                                                (set! initial (- initial 1))))
                                    (read (lambda ()
                                            initial))
                                    (dispatch (lambda (m)
                                                (if (eq? m 'increase)
                                                   (increase)
                                                   (if (eq? m 'decrease)
                                                      (decrease)
                                                      (if (eq? m 'read)
                                                         (read)
                                                         (display "wrong message")))))))
                              dispatch)))
         (create-parking (lambda capaciteiten
                           (let ((verdieping-ctrs (map create-counter capaciteiten))
                                 (nr-verdiepingen (length capaciteiten))
                                 (nbr-cars 0))
                              (letrec ((total-capacity (lambda ()
                                                         (apply + capaciteiten)))
                                       (full? (lambda ()
                                                (= nbr-cars (total-capacity))))
                                       (empty? (lambda ()
                                                 (= nbr-cars 0)))
                                       (max-reached-level (lambda (level idx)
                                                            (>= (level 'read) (list-ref capaciteiten (- idx 1)))))
                                       (level-current (lambda ()
                                                        (letrec ((loop (lambda (lst index)
                                                                         (if (null? lst)
                                                                            #f
                                                                            (let* ((level (car lst))
                                                                                   (capacity (level 'read)))
                                                                               (if (> capacity 0)
                                                                                  index
                                                                                  (loop (cdr lst) (+ index 1))))))))
                                                           (loop verdieping-ctrs 1))))
                                       (level-to-leave (lambda ()
                                                         (letrec ((loop (lambda (lst index)
                                                                          (if (null? lst)
                                                                             #f
                                                                             (let* ((level (car lst))
                                                                                    (capacity (level 'read)))
                                                                                (if (if (not (max-reached-level level index)) (>= capacity 0) #f)
                                                                                   index
                                                                                   (loop (cdr lst) (- index 1))))))))
                                                            (loop (reverse verdieping-ctrs) nr-verdiepingen))))
                                       (car-enters (lambda ()
                                                     (let ((level (level-current)))
                                                        (if level
                                                           (let ((verdieping-ctr (list-ref verdieping-ctrs (- level 1))))
                                                              (<change>
                                                                 (set! nbr-cars (+ nbr-cars 1))
                                                                 ((lambda (x) x) (set! nbr-cars (+ nbr-cars 1))))
                                                              (<change>
                                                                 ()
                                                                 nbr-cars)
                                                              (verdieping-ctr 'decrease))
                                                           #f))))
                                       (car-leaves (lambda ()
                                                     (let ((level (level-to-leave)))
                                                        (<change>
                                                           (if level
                                                              (let ((verdieping-ctr (list-ref verdieping-ctrs (- level 1))))
                                                                 (set! nbr-cars (- nbr-cars 1))
                                                                 (verdieping-ctr 'increase))
                                                              (let ((verdieping-ctr (list-ref verdieping-ctrs (- nr-verdiepingen 1))))
                                                                 (set! nbr-cars (- nbr-cars 1))
                                                                 (verdieping-ctr 'increase)))
                                                           ((lambda (x) x)
                                                              (if level
                                                                 (let ((verdieping-ctr (list-ref verdieping-ctrs (- level 1))))
                                                                    (set! nbr-cars (- nbr-cars 1))
                                                                    (verdieping-ctr 'increase))
                                                                 (let ((verdieping-ctr (list-ref verdieping-ctrs (- nr-verdiepingen 1))))
                                                                    (<change>
                                                                       (set! nbr-cars (- nbr-cars 1))
                                                                       (verdieping-ctr 'increase))
                                                                    (<change>
                                                                       (verdieping-ctr 'increase)
                                                                       (set! nbr-cars (- nbr-cars 1))))))))))
                                       (dispatch (lambda (msg)
                                                   (if (eq? msg 'full?)
                                                      (full?)
                                                      (if (eq? msg 'empty?)
                                                         (empty?)
                                                         (if (eq? msg 'level)
                                                            (level-current)
                                                            (if (eq? msg 'car-enters)
                                                               (car-enters)
                                                               (if (eq? msg 'lst)
                                                                  verdieping-ctrs
                                                                  (if (eq? msg 'car-leaves)
                                                                     (car-leaves)
                                                                     (error "wrong message"))))))))))
                                 dispatch))))
         (parking (create-parking 3 5 2)))
   (if (= (parking 'level) 1)
      (if (not (parking 'full?))
         (if (= (begin (parking 'car-enters) (parking 'car-enters) (parking 'car-enters) (parking 'car-enters) (parking 'level)) 2)
            (if (not (parking 'empty?))
               (if (begin (parking 'car-enters) (parking 'car-enters) (parking 'car-enters) (<change> (parking 'car-enters) (parking 'car-enters)) (<change> (parking 'car-enters) (parking 'car-enters)) (parking 'car-enters) (parking 'full?))
                  (if (not (parking 'car-enters))
                     (=
                        (begin
                           (<change>
                              (parking 'car-leaves)
                              ((lambda (x) x) (parking 'car-leaves)))
                           (<change>
                              ()
                              parking)
                           (<change>
                              (parking 'car-leaves)
                              ())
                           (parking 'car-leaves)
                           (<change>
                              (parking 'level)
                              ((lambda (x) x) (parking 'level))))
                        2)
                     #f)
                  #f)
               #f)
            #f)
         #f)
      #f))