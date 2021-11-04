; Changes:
; * removed: 0
; * added: 1
; * swaps: 1
; * negated predicates: 2
; * swapped branches: 0
; * calls to id fun: 5
(letrec ((debug-trace (lambda ()
                        'do-nothing))
         (cadr (lambda (p)
                 (<change>
                    (car (cdr p))
                    ((lambda (x) x) (car (cdr p))))))
         (caddr (lambda (p)
                  (<change>
                     (car (cdr (cdr p)))
                     ((lambda (x) x) (car (cdr (cdr p)))))))
         (regex-NULL #f)
         (regex-BLANK #t)
         (regex-alt? (lambda (re)
                       (if (pair? re) (eq? (car re) 'alt) #f)))
         (regex-seq? (lambda (re)
                       (<change>
                          (if (pair? re) (eq? (car re) 'seq) #f)
                          ((lambda (x) x) (if (<change> (pair? re) (not (pair? re))) (eq? (car re) 'seq) #f)))))
         (regex-rep? (lambda (re)
                       (if (<change> (pair? re) (not (pair? re)))
                          (eq? (car re) 'rep)
                          #f)))
         (regex-null? (lambda (re)
                        (eq? re #f)))
         (regex-empty? (lambda (re)
                         (eq? re #t)))
         (regex-atom? (lambda (re)
                        (let ((__or_res (char? re)))
                           (if __or_res __or_res (symbol? re)))))
         (match-seq (lambda (re f)
                      (if (regex-seq? re) (f (cadr re) (caddr re)) #f)))
         (match-alt (lambda (re f)
                      (if (regex-alt? re) (f (cadr re) (caddr re)) #f)))
         (match-rep (lambda (re f)
                      (if (regex-rep? re) (f (cadr re)) #f)))
         (seq (lambda (pat1 pat2)
                (if (regex-null? pat1)
                   regex-NULL
                   (if (regex-null? pat2)
                      regex-NULL
                      (if (regex-empty? pat1)
                         pat2
                         (if (regex-empty? pat2)
                            pat1
                            (cons 'seq (cons pat1 (cons pat2 ())))))))))
         (alt (lambda (pat1 pat2)
                (if (regex-null? pat1)
                   pat2
                   (if (regex-null? pat2)
                      pat1
                      (cons 'alt (cons pat1 (cons pat2 ())))))))
         (rep (lambda (pat)
                (<change>
                   (if (regex-null? pat)
                      regex-BLANK
                      (if (regex-empty? pat)
                         regex-BLANK
                         (cons 'rep (cons pat ()))))
                   ((lambda (x) x)
                      (if (regex-null? pat)
                         regex-BLANK
                         (if (regex-empty? pat)
                            regex-BLANK
                            (cons 'rep (cons pat ()))))))))
         (regex-empty (lambda (re)
                        (if (regex-empty? re)
                           #t
                           (if (regex-null? re)
                              #f
                              (if (regex-atom? re)
                                 #f
                                 (if (match-seq re (lambda (pat1 pat2) (seq (regex-empty pat1) (regex-empty pat2))))
                                    #f
                                    (if (match-alt re (lambda (pat1 pat2) (alt (regex-empty pat1) (regex-empty pat2))))
                                       #f
                                       (if (regex-rep? re) #t #f))))))))
         (d/dc (lambda (re c)
                 (<change>
                    (debug-trace)
                    (if (regex-empty? re)
                       regex-NULL
                       (if (regex-null? re)
                          regex-NULL
                          (if (eq? c re)
                             regex-BLANK
                             (if (regex-atom? re)
                                regex-NULL
                                (if (match-seq re (lambda (pat1 pat2) (alt (seq (d/dc pat1 c) pat2) (seq (regex-empty pat1) (d/dc pat2 c)))))
                                   #f
                                   (if (match-alt re (lambda (pat1 pat2) (alt (d/dc pat1 c) (d/dc pat2 c))))
                                      #f
                                      (if (match-rep re (lambda (pat) (seq (d/dc pat c) (rep pat))))
                                         #f
                                         regex-NULL))))))))
                 (<change>
                    (if (regex-empty? re)
                       regex-NULL
                       (if (regex-null? re)
                          regex-NULL
                          (if (eq? c re)
                             regex-BLANK
                             (if (regex-atom? re)
                                regex-NULL
                                (if (match-seq re (lambda (pat1 pat2) (alt (seq (d/dc pat1 c) pat2) (seq (regex-empty pat1) (d/dc pat2 c)))))
                                   #f
                                   (if (match-alt re (lambda (pat1 pat2) (alt (d/dc pat1 c) (d/dc pat2 c))))
                                      #f
                                      (if (match-rep re (lambda (pat) (seq (d/dc pat c) (rep pat))))
                                         #f
                                         regex-NULL)))))))
                    (debug-trace))))
         (regex-match (lambda (pattern data)
                        (if (null? data)
                           (regex-empty? (regex-empty pattern))
                           (regex-match (d/dc pattern (car data)) (cdr data)))))
         (check-expect (lambda (check expect)
                         (if (not (equal? check expect))
                            (begin
                               (display "check-expect failed; got: ")
                               (display check)
                               (display "; expected: ")
                               (display expect)
                               (<change>
                                  (newline)
                                  ((lambda (x) x) (newline))))
                            (void)))))
   (<change>
      ()
      check-expect)
   (check-expect (d/dc 'baz 'f) #f))