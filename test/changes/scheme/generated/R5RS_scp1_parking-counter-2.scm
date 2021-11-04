; Changes:
; * removed: 1
; * added: 2
; * swaps: 1
; * negated predicates: 4
; * swapped branches: 2
; * calls to id fun: 6
(letrec ((create-counter (lambda (initial)
                           (letrec ((increase (lambda ()
                                                (set! initial (+ initial 1))))
                                    (decrease (lambda ()
                                                (set! initial (- initial 1))))
                                    (read (lambda ()
                                            (<change>
                                               initial
                                               ((lambda (x) x) initial))))
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
                                                        (<change>
                                                           (letrec ((loop (lambda (lst index)
                                                                            (if (null? lst)
                                                                               #f
                                                                               (let* ((level (car lst))
                                                                                      (capacity (level 'read)))
                                                                                  (if (> capacity 0)
                                                                                     index
                                                                                     (loop (cdr lst) (+ index 1))))))))
                                                              (loop verdieping-ctrs 1))
                                                           ((lambda (x) x)
                                                              (letrec ((loop (lambda (lst index)
                                                                               (if (null? lst)
                                                                                  #f
                                                                                  (let* ((level (car lst))
                                                                                         (capacity (level 'read)))
                                                                                     (if (<change> (> capacity 0) (not (> capacity 0)))
                                                                                        index
                                                                                        (loop (cdr lst) (+ index 1))))))))
                                                                 (loop verdieping-ctrs 1))))))
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
                                                     (<change>
                                                        (let ((level (level-current)))
                                                           (if level
                                                              (let ((verdieping-ctr (list-ref verdieping-ctrs (- level 1))))
                                                                 (set! nbr-cars (+ nbr-cars 1))
                                                                 (verdieping-ctr 'decrease))
                                                              #f))
                                                        ((lambda (x) x)
                                                           (let ((level (level-current)))
                                                              (if (<change> level (not level))
                                                                 (let ((verdieping-ctr (list-ref verdieping-ctrs (- level 1))))
                                                                    (set! nbr-cars (+ nbr-cars 1))
                                                                    (verdieping-ctr 'decrease))
                                                                 #f))))))
                                       (car-leaves (lambda ()
                                                     (<change>
                                                        (let ((level (level-to-leave)))
                                                           (if level
                                                              (let ((verdieping-ctr (list-ref verdieping-ctrs (- level 1))))
                                                                 (set! nbr-cars (- nbr-cars 1))
                                                                 (verdieping-ctr 'increase))
                                                              (let ((verdieping-ctr (list-ref verdieping-ctrs (- nr-verdiepingen 1))))
                                                                 (set! nbr-cars (- nbr-cars 1))
                                                                 (verdieping-ctr 'increase))))
                                                        ((lambda (x) x)
                                                           (let ((level (level-to-leave)))
                                                              (if level
                                                                 (let ((verdieping-ctr (list-ref verdieping-ctrs (- level 1))))
                                                                    (set! nbr-cars (- nbr-cars 1))
                                                                    (verdieping-ctr 'increase))
                                                                 (let ((verdieping-ctr (list-ref verdieping-ctrs (- nr-verdiepingen 1))))
                                                                    (set! nbr-cars (- nbr-cars 1))
                                                                    (verdieping-ctr 'increase))))))))
                                       (dispatch (lambda (msg)
                                                   (if (<change> (eq? msg 'full?) (not (eq? msg 'full?)))
                                                      (full?)
                                                      (if (eq? msg 'empty?)
                                                         (<change>
                                                            (empty?)
                                                            (if (eq? msg 'level)
                                                               (level-current)
                                                               (if (eq? msg 'car-enters)
                                                                  (car-enters)
                                                                  (if (eq? msg 'lst)
                                                                     verdieping-ctrs
                                                                     (if (eq? msg 'car-leaves)
                                                                        (car-leaves)
                                                                        (error "wrong message"))))))
                                                         (<change>
                                                            (if (eq? msg 'level)
                                                               (level-current)
                                                               (if (eq? msg 'car-enters)
                                                                  (car-enters)
                                                                  (if (eq? msg 'lst)
                                                                     verdieping-ctrs
                                                                     (if (eq? msg 'car-leaves)
                                                                        (car-leaves)
                                                                        (error "wrong message")))))
                                                            (empty?)))))))
                                 (<change>
                                    ()
                                    dispatch)
                                 (<change>
                                    ()
                                    dispatch)
                                 (<change>
                                    dispatch
                                    ((lambda (x) x) dispatch))))))
         (parking (create-parking 3 5 2)))
   (if (<change> (= (parking 'level) 1) (not (= (parking 'level) 1)))
      (if (not (parking 'full?))
         (if (= (begin (parking 'car-enters) (<change> (parking 'car-enters) ((lambda (x) x) (parking 'car-enters))) (<change> (parking 'car-enters) (parking 'car-enters)) (<change> (parking 'car-enters) (parking 'car-enters)) (parking 'level)) 2)
            (if (not (parking 'empty?))
               (if (begin (<change> (parking 'car-enters) ()) (parking 'car-enters) (parking 'car-enters) (parking 'car-enters) (parking 'car-enters) (parking 'car-enters) (parking 'full?))
                  (if (not (parking 'car-enters))
                     (<change>
                        (= (begin (parking 'car-leaves) (parking 'car-leaves) (parking 'car-leaves) (parking 'level)) 2)
                        #f)
                     (<change>
                        #f
                        (= (begin (parking 'car-leaves) (parking 'car-leaves) (parking 'car-leaves) (parking 'level)) 2)))
                  #f)
               #f)
            #f)
         #f)
      #f))