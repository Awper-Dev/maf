; Changes:
; * removed: 1
; * added: 1
; * swaps: 2
; * negated predicates: 0
; * swapped branches: 4
; * calls to id fun: 11
(letrec ((void (lambda ()
                 'void))
         (assq (lambda (k l)
                 (if (null? l)
                    #f
                    (if (eq? (caar l) k) (car l) (assq k (cdr l))))))
         (member (lambda (v l)
                   (if (null? l)
                      #f
                      (if (eq? v (car l)) l (member v (cdr l))))))
         (*namelist* ())
         (*lastlook* (__toplevel_cons 'xxx (__toplevel_cons () ())))
         (nameprop (lambda (name)
                     (<change>
                        (if (eq? name (car *lastlook*))
                           *lastlook*
                           (let ((pair (assq name *namelist*)))
                              (if pair (set! *lastlook* pair) (void))
                              pair))
                        ((lambda (x) x)
                           (if (eq? name (car *lastlook*))
                              *lastlook*
                              (let ((pair (assq name *namelist*)))
                                 (if pair
                                    (<change>
                                       (set! *lastlook* pair)
                                       (void))
                                    (<change>
                                       (void)
                                       (set! *lastlook* pair)))
                                 pair))))))
         (get (lambda (name prop)
                (let ((r (nameprop name)))
                   (<change>
                      (if (pair? r)
                         (let ((s (assq prop (cdr r))))
                            (if (pair? s) (cdr s) #f))
                         #f)
                      ((lambda (x) x) (if (pair? r) (let ((s (assq prop (cdr r)))) (if (pair? s) (cdr s) #f)) #f))))))
         (put (lambda (name prop valu)
                (let ((r (nameprop name)))
                   (if (pair? r)
                      (let ((s (assq prop (cdr r))))
                         (if (pair? s)
                            (set-cdr! s valu)
                            (let ((item (cons prop valu)))
                               (set-cdr! r (cons item (cdr r))))))
                      (let ((item (cons prop valu)))
                         (set! *namelist* (cons (cons name (list item)) *namelist*)))))
                valu))
         (reinit-prop! (lambda ()
                         (<change>
                            (set! *namelist* ())
                            (set! *lastlook* (__toplevel_cons 'xxx (__toplevel_cons () ()))))
                         (<change>
                            (set! *lastlook* (__toplevel_cons 'xxx (__toplevel_cons () ())))
                            (set! *namelist* ()))))
         (run-benchmark (lambda (benchmark-name benchmark-thunk)
                          (let ((ten (lambda ()
                                       (<change>
                                          (benchmark-thunk)
                                          ((lambda (x) x) (benchmark-thunk)))
                                       (benchmark-thunk)
                                       (benchmark-thunk)
                                       (benchmark-thunk)
                                       (<change>
                                          (benchmark-thunk)
                                          ((lambda (x) x) (benchmark-thunk)))
                                       (<change>
                                          (benchmark-thunk)
                                          ())
                                       (benchmark-thunk)
                                       (benchmark-thunk)
                                       (<change>
                                          (benchmark-thunk)
                                          ((lambda (x) x) (benchmark-thunk)))
                                       (<change>
                                          ()
                                          benchmark-thunk)
                                       (benchmark-thunk))))
                             (ten)
                             (<change>
                                (ten)
                                ((lambda (x) x) (ten)))
                             (ten)
                             (ten))))
         (get-null (lambda (name prop)
                     (let ((__or_res (get name prop)))
                        (if __or_res __or_res ()))))
         (unify-subst 0)
         (temp-temp 0)
         (add-lemma (lambda (term)
                      (if (if (pair? term) (if (eq? (car term) 'equal) (pair? (cadr term)) #f) #f)
                         (put (car (cadr term)) 'lemmas (cons term (get-null (car (cadr term)) 'lemmas)))
                         (error 'add-lemma "ADD-LEMMA did not like term:  " term))))
         (add-lemma-lst (lambda (lst)
                          (if (null? lst)
                             #t
                             (begin
                                (add-lemma (car lst))
                                (add-lemma-lst (cdr lst))))))
         (apply-subst (lambda (alist term)
                        (if (not (pair? term))
                           (if (begin (set! temp-temp (assq term alist)) temp-temp)
                              (cdr temp-temp)
                              term)
                           (cons (car term) (apply-subst-lst alist (cdr term))))))
         (apply-subst-lst (lambda (alist lst)
                            (if (null? lst)
                               ()
                               (cons (apply-subst alist (car lst)) (apply-subst-lst alist (cdr lst))))))
         (falsep (lambda (x lst)
                   (let ((__or_res (eq? x (__toplevel_cons 'f ()))))
                      (if __or_res __or_res (member x lst)))))
         (one-way-unify (lambda (term1 term2)
                          (<change>
                             (begin
                                (set! unify-subst ())
                                (one-way-unify1 term1 term2))
                             ((lambda (x) x) (begin (set! unify-subst ()) (one-way-unify1 term1 term2))))))
         (one-way-unify1 (lambda (term1 term2)
                           (if (not (pair? term2))
                              (if (begin (set! temp-temp (assq term2 unify-subst)) temp-temp)
                                 (eq? term1 (cdr temp-temp))
                                 (begin
                                    (set! unify-subst (cons (cons term2 term1) unify-subst))
                                    (<change>
                                       #t
                                       ((lambda (x) x) #t))))
                              (if (not (pair? term1))
                                 #f
                                 (if (eq? (car term1) (car term2))
                                    (one-way-unify1-lst (cdr term1) (cdr term2))
                                    #f)))))
         (one-way-unify1-lst (lambda (lst1 lst2)
                               (if (null? lst1)
                                  #t
                                  (if (one-way-unify1 (car lst1) (car lst2))
                                     (<change>
                                        (one-way-unify1-lst (cdr lst1) (cdr lst2))
                                        #f)
                                     (<change>
                                        #f
                                        (one-way-unify1-lst (cdr lst1) (cdr lst2)))))))
         (rewrite (lambda (term)
                    (if (not (pair? term))
                       term
                       (rewrite-with-lemmas (cons (car term) (rewrite-args (cdr term))) (get-null (car term) 'lemmas)))))
         (rewrite-args (lambda (lst)
                         (if (null? lst)
                            ()
                            (cons (rewrite (car lst)) (rewrite-args (cdr lst))))))
         (rewrite-with-lemmas (lambda (term lst)
                                (<change>
                                   (if (null? lst)
                                      term
                                      (if (one-way-unify term (cadr (car lst)))
                                         (rewrite (apply-subst unify-subst (caddr (car lst))))
                                         (rewrite-with-lemmas term (cdr lst))))
                                   ((lambda (x) x)
                                      (if (null? lst)
                                         (<change>
                                            term
                                            (if (one-way-unify term (cadr (car lst)))
                                               (rewrite (apply-subst unify-subst (caddr (car lst))))
                                               (rewrite-with-lemmas term (cdr lst))))
                                         (<change>
                                            (if (one-way-unify term (cadr (car lst)))
                                               (rewrite (apply-subst unify-subst (caddr (car lst))))
                                               (rewrite-with-lemmas term (cdr lst)))
                                            term))))))
         (setup (lambda ()
                  (add-lemma-lst
                     (__toplevel_cons
                        (__toplevel_cons
                           'equal
                           (__toplevel_cons
                              (__toplevel_cons 'compile (__toplevel_cons 'form ()))
                              (__toplevel_cons
                                 (__toplevel_cons
                                    'reverse
                                    (__toplevel_cons
                                       (__toplevel_cons
                                          'codegen
                                          (__toplevel_cons
                                             (__toplevel_cons 'optimize (__toplevel_cons 'form ()))
                                             (__toplevel_cons (__toplevel_cons 'nil ()) ())))
                                       ()))
                                 ())))
                        (__toplevel_cons
                           (__toplevel_cons
                              'equal
                              (__toplevel_cons
                                 (__toplevel_cons 'eqp (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                 (__toplevel_cons
                                    (__toplevel_cons
                                       'equal
                                       (__toplevel_cons
                                          (__toplevel_cons 'fix (__toplevel_cons 'x ()))
                                          (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'y ())) ())))
                                    ())))
                           (__toplevel_cons
                              (__toplevel_cons
                                 'equal
                                 (__toplevel_cons
                                    (__toplevel_cons 'greaterp (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                    (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'y (__toplevel_cons 'x ()))) ())))
                              (__toplevel_cons
                                 (__toplevel_cons
                                    'equal
                                    (__toplevel_cons
                                       (__toplevel_cons 'lesseqp (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                       (__toplevel_cons
                                          (__toplevel_cons
                                             'not
                                             (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'y (__toplevel_cons 'x ()))) ()))
                                          ())))
                                 (__toplevel_cons
                                    (__toplevel_cons
                                       'equal
                                       (__toplevel_cons
                                          (__toplevel_cons 'greatereqp (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                          (__toplevel_cons
                                             (__toplevel_cons
                                                'not
                                                (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))
                                             ())))
                                    (__toplevel_cons
                                       (__toplevel_cons
                                          'equal
                                          (__toplevel_cons
                                             (__toplevel_cons 'boolean (__toplevel_cons 'x ()))
                                             (__toplevel_cons
                                                (__toplevel_cons
                                                   'or
                                                   (__toplevel_cons
                                                      (__toplevel_cons 'equal (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 't ()) ())))
                                                      (__toplevel_cons
                                                         (__toplevel_cons 'equal (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'f ()) ())))
                                                         ())))
                                                ())))
                                       (__toplevel_cons
                                          (__toplevel_cons
                                             'equal
                                             (__toplevel_cons
                                                (__toplevel_cons 'iff (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                (__toplevel_cons
                                                   (__toplevel_cons
                                                      'and
                                                      (__toplevel_cons
                                                         (__toplevel_cons 'implies (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                         (__toplevel_cons (__toplevel_cons 'implies (__toplevel_cons 'y (__toplevel_cons 'x ()))) ())))
                                                   ())))
                                          (__toplevel_cons
                                             (__toplevel_cons
                                                'equal
                                                (__toplevel_cons
                                                   (__toplevel_cons 'even1 (__toplevel_cons 'x ()))
                                                   (__toplevel_cons
                                                      (__toplevel_cons
                                                         'if
                                                         (__toplevel_cons
                                                            (__toplevel_cons 'zerop (__toplevel_cons 'x ()))
                                                            (__toplevel_cons
                                                               (__toplevel_cons 't ())
                                                               (__toplevel_cons
                                                                  (__toplevel_cons 'odd (__toplevel_cons (__toplevel_cons '1- (__toplevel_cons 'x ())) ()))
                                                                  ()))))
                                                      ())))
                                             (__toplevel_cons
                                                (__toplevel_cons
                                                   'equal
                                                   (__toplevel_cons
                                                      (__toplevel_cons 'countps- (__toplevel_cons 'l (__toplevel_cons 'pred ())))
                                                      (__toplevel_cons
                                                         (__toplevel_cons
                                                            'countps-loop
                                                            (__toplevel_cons 'l (__toplevel_cons 'pred (__toplevel_cons (__toplevel_cons 'zero ()) ()))))
                                                         ())))
                                                (__toplevel_cons
                                                   (__toplevel_cons
                                                      'equal
                                                      (__toplevel_cons
                                                         (__toplevel_cons 'fact- (__toplevel_cons 'i ()))
                                                         (__toplevel_cons (__toplevel_cons 'fact-loop (__toplevel_cons 'i (__toplevel_cons 1 ()))) ())))
                                                   (__toplevel_cons
                                                      (__toplevel_cons
                                                         'equal
                                                         (__toplevel_cons
                                                            (__toplevel_cons 'reverse- (__toplevel_cons 'x ()))
                                                            (__toplevel_cons
                                                               (__toplevel_cons 'reverse-loop (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'nil ()) ())))
                                                               ())))
                                                      (__toplevel_cons
                                                         (__toplevel_cons
                                                            'equal
                                                            (__toplevel_cons
                                                               (__toplevel_cons 'divides (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                               (__toplevel_cons
                                                                  (__toplevel_cons
                                                                     'zerop
                                                                     (__toplevel_cons (__toplevel_cons 'remainder (__toplevel_cons 'y (__toplevel_cons 'x ()))) ()))
                                                                  ())))
                                                         (__toplevel_cons
                                                            (__toplevel_cons
                                                               'equal
                                                               (__toplevel_cons
                                                                  (__toplevel_cons 'assume-true (__toplevel_cons 'var (__toplevel_cons 'alist ())))
                                                                  (__toplevel_cons
                                                                     (__toplevel_cons
                                                                        'cons
                                                                        (__toplevel_cons
                                                                           (__toplevel_cons 'cons (__toplevel_cons 'var (__toplevel_cons (__toplevel_cons 't ()) ())))
                                                                           (__toplevel_cons 'alist ())))
                                                                     ())))
                                                            (__toplevel_cons
                                                               (__toplevel_cons
                                                                  'equal
                                                                  (__toplevel_cons
                                                                     (__toplevel_cons 'assume-false (__toplevel_cons 'var (__toplevel_cons 'alist ())))
                                                                     (__toplevel_cons
                                                                        (__toplevel_cons
                                                                           'cons
                                                                           (__toplevel_cons
                                                                              (__toplevel_cons 'cons (__toplevel_cons 'var (__toplevel_cons (__toplevel_cons 'f ()) ())))
                                                                              (__toplevel_cons 'alist ())))
                                                                        ())))
                                                               (__toplevel_cons
                                                                  (__toplevel_cons
                                                                     'equal
                                                                     (__toplevel_cons
                                                                        (__toplevel_cons 'tautology-checker (__toplevel_cons 'x ()))
                                                                        (__toplevel_cons
                                                                           (__toplevel_cons
                                                                              'tautologyp
                                                                              (__toplevel_cons
                                                                                 (__toplevel_cons 'normalize (__toplevel_cons 'x ()))
                                                                                 (__toplevel_cons (__toplevel_cons 'nil ()) ())))
                                                                           ())))
                                                                  (__toplevel_cons
                                                                     (__toplevel_cons
                                                                        'equal
                                                                        (__toplevel_cons
                                                                           (__toplevel_cons 'falsify (__toplevel_cons 'x ()))
                                                                           (__toplevel_cons
                                                                              (__toplevel_cons
                                                                                 'falsify1
                                                                                 (__toplevel_cons
                                                                                    (__toplevel_cons 'normalize (__toplevel_cons 'x ()))
                                                                                    (__toplevel_cons (__toplevel_cons 'nil ()) ())))
                                                                              ())))
                                                                     (__toplevel_cons
                                                                        (__toplevel_cons
                                                                           'equal
                                                                           (__toplevel_cons
                                                                              (__toplevel_cons 'prime (__toplevel_cons 'x ()))
                                                                              (__toplevel_cons
                                                                                 (__toplevel_cons
                                                                                    'and
                                                                                    (__toplevel_cons
                                                                                       (__toplevel_cons 'not (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'x ())) ()))
                                                                                       (__toplevel_cons
                                                                                          (__toplevel_cons
                                                                                             'not
                                                                                             (__toplevel_cons
                                                                                                (__toplevel_cons
                                                                                                   'equal
                                                                                                   (__toplevel_cons
                                                                                                      'x
                                                                                                      (__toplevel_cons (__toplevel_cons 'add1 (__toplevel_cons (__toplevel_cons 'zero ()) ())) ())))
                                                                                                ()))
                                                                                          (__toplevel_cons
                                                                                             (__toplevel_cons
                                                                                                'prime1
                                                                                                (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons '1- (__toplevel_cons 'x ())) ())))
                                                                                             ()))))
                                                                                 ())))
                                                                        (__toplevel_cons
                                                                           (__toplevel_cons
                                                                              'equal
                                                                              (__toplevel_cons
                                                                                 (__toplevel_cons 'and (__toplevel_cons 'p (__toplevel_cons 'q ())))
                                                                                 (__toplevel_cons
                                                                                    (__toplevel_cons
                                                                                       'if
                                                                                       (__toplevel_cons
                                                                                          'p
                                                                                          (__toplevel_cons
                                                                                             (__toplevel_cons
                                                                                                'if
                                                                                                (__toplevel_cons
                                                                                                   'q
                                                                                                   (__toplevel_cons (__toplevel_cons 't ()) (__toplevel_cons (__toplevel_cons 'f ()) ()))))
                                                                                             (__toplevel_cons (__toplevel_cons 'f ()) ()))))
                                                                                    ())))
                                                                           (__toplevel_cons
                                                                              (__toplevel_cons
                                                                                 'equal
                                                                                 (__toplevel_cons
                                                                                    (__toplevel_cons 'or (__toplevel_cons 'p (__toplevel_cons 'q ())))
                                                                                    (__toplevel_cons
                                                                                       (__toplevel_cons
                                                                                          'if
                                                                                          (__toplevel_cons
                                                                                             'p
                                                                                             (__toplevel_cons
                                                                                                (__toplevel_cons 't ())
                                                                                                (__toplevel_cons
                                                                                                   (__toplevel_cons
                                                                                                      'if
                                                                                                      (__toplevel_cons
                                                                                                         'q
                                                                                                         (__toplevel_cons (__toplevel_cons 't ()) (__toplevel_cons (__toplevel_cons 'f ()) ()))))
                                                                                                   (__toplevel_cons (__toplevel_cons 'f ()) ())))))
                                                                                       ())))
                                                                              (__toplevel_cons
                                                                                 (__toplevel_cons
                                                                                    'equal
                                                                                    (__toplevel_cons
                                                                                       (__toplevel_cons 'not (__toplevel_cons 'p ()))
                                                                                       (__toplevel_cons
                                                                                          (__toplevel_cons
                                                                                             'if
                                                                                             (__toplevel_cons
                                                                                                'p
                                                                                                (__toplevel_cons (__toplevel_cons 'f ()) (__toplevel_cons (__toplevel_cons 't ()) ()))))
                                                                                          ())))
                                                                                 (__toplevel_cons
                                                                                    (__toplevel_cons
                                                                                       'equal
                                                                                       (__toplevel_cons
                                                                                          (__toplevel_cons 'implies (__toplevel_cons 'p (__toplevel_cons 'q ())))
                                                                                          (__toplevel_cons
                                                                                             (__toplevel_cons
                                                                                                'if
                                                                                                (__toplevel_cons
                                                                                                   'p
                                                                                                   (__toplevel_cons
                                                                                                      (__toplevel_cons
                                                                                                         'if
                                                                                                         (__toplevel_cons
                                                                                                            'q
                                                                                                            (__toplevel_cons (__toplevel_cons 't ()) (__toplevel_cons (__toplevel_cons 'f ()) ()))))
                                                                                                      (__toplevel_cons (__toplevel_cons 't ()) ()))))
                                                                                             ())))
                                                                                    (__toplevel_cons
                                                                                       (__toplevel_cons
                                                                                          'equal
                                                                                          (__toplevel_cons
                                                                                             (__toplevel_cons 'fix (__toplevel_cons 'x ()))
                                                                                             (__toplevel_cons
                                                                                                (__toplevel_cons
                                                                                                   'if
                                                                                                   (__toplevel_cons
                                                                                                      (__toplevel_cons 'numberp (__toplevel_cons 'x ()))
                                                                                                      (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'zero ()) ()))))
                                                                                                ())))
                                                                                       (__toplevel_cons
                                                                                          (__toplevel_cons
                                                                                             'equal
                                                                                             (__toplevel_cons
                                                                                                (__toplevel_cons
                                                                                                   'if
                                                                                                   (__toplevel_cons
                                                                                                      (__toplevel_cons 'if (__toplevel_cons 'a (__toplevel_cons 'b (__toplevel_cons 'c ()))))
                                                                                                      (__toplevel_cons 'd (__toplevel_cons 'e ()))))
                                                                                                (__toplevel_cons
                                                                                                   (__toplevel_cons
                                                                                                      'if
                                                                                                      (__toplevel_cons
                                                                                                         'a
                                                                                                         (__toplevel_cons
                                                                                                            (__toplevel_cons 'if (__toplevel_cons 'b (__toplevel_cons 'd (__toplevel_cons 'e ()))))
                                                                                                            (__toplevel_cons
                                                                                                               (__toplevel_cons 'if (__toplevel_cons 'c (__toplevel_cons 'd (__toplevel_cons 'e ()))))
                                                                                                               ()))))
                                                                                                   ())))
                                                                                          (__toplevel_cons
                                                                                             (__toplevel_cons
                                                                                                'equal
                                                                                                (__toplevel_cons
                                                                                                   (__toplevel_cons 'zerop (__toplevel_cons 'x ()))
                                                                                                   (__toplevel_cons
                                                                                                      (__toplevel_cons
                                                                                                         'or
                                                                                                         (__toplevel_cons
                                                                                                            (__toplevel_cons 'equal (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                            (__toplevel_cons
                                                                                                               (__toplevel_cons 'not (__toplevel_cons (__toplevel_cons 'numberp (__toplevel_cons 'x ())) ()))
                                                                                                               ())))
                                                                                                      ())))
                                                                                             (__toplevel_cons
                                                                                                (__toplevel_cons
                                                                                                   'equal
                                                                                                   (__toplevel_cons
                                                                                                      (__toplevel_cons
                                                                                                         'plus
                                                                                                         (__toplevel_cons
                                                                                                            (__toplevel_cons 'plus (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                            (__toplevel_cons 'z ())))
                                                                                                      (__toplevel_cons
                                                                                                         (__toplevel_cons
                                                                                                            'plus
                                                                                                            (__toplevel_cons
                                                                                                               'x
                                                                                                               (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'y (__toplevel_cons 'z ()))) ())))
                                                                                                         ())))
                                                                                                (__toplevel_cons
                                                                                                   (__toplevel_cons
                                                                                                      'equal
                                                                                                      (__toplevel_cons
                                                                                                         (__toplevel_cons
                                                                                                            'equal
                                                                                                            (__toplevel_cons
                                                                                                               (__toplevel_cons 'plus (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                                                                               (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                         (__toplevel_cons
                                                                                                            (__toplevel_cons
                                                                                                               'and
                                                                                                               (__toplevel_cons
                                                                                                                  (__toplevel_cons 'zerop (__toplevel_cons 'a ()))
                                                                                                                  (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'b ())) ())))
                                                                                                            ())))
                                                                                                   (__toplevel_cons
                                                                                                      (__toplevel_cons
                                                                                                         'equal
                                                                                                         (__toplevel_cons
                                                                                                            (__toplevel_cons 'difference (__toplevel_cons 'x (__toplevel_cons 'x ())))
                                                                                                            (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                      (__toplevel_cons
                                                                                                         (__toplevel_cons
                                                                                                            'equal
                                                                                                            (__toplevel_cons
                                                                                                               (__toplevel_cons
                                                                                                                  'equal
                                                                                                                  (__toplevel_cons
                                                                                                                     (__toplevel_cons 'plus (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                                                                                     (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'a (__toplevel_cons 'c ()))) ())))
                                                                                                               (__toplevel_cons
                                                                                                                  (__toplevel_cons
                                                                                                                     'equal
                                                                                                                     (__toplevel_cons
                                                                                                                        (__toplevel_cons 'fix (__toplevel_cons 'b ()))
                                                                                                                        (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'c ())) ())))
                                                                                                                  ())))
                                                                                                         (__toplevel_cons
                                                                                                            (__toplevel_cons
                                                                                                               'equal
                                                                                                               (__toplevel_cons
                                                                                                                  (__toplevel_cons
                                                                                                                     'equal
                                                                                                                     (__toplevel_cons
                                                                                                                        (__toplevel_cons 'zero ())
                                                                                                                        (__toplevel_cons (__toplevel_cons 'difference (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                  (__toplevel_cons
                                                                                                                     (__toplevel_cons
                                                                                                                        'not
                                                                                                                        (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'y (__toplevel_cons 'x ()))) ()))
                                                                                                                     ())))
                                                                                                            (__toplevel_cons
                                                                                                               (__toplevel_cons
                                                                                                                  'equal
                                                                                                                  (__toplevel_cons
                                                                                                                     (__toplevel_cons
                                                                                                                        'equal
                                                                                                                        (__toplevel_cons
                                                                                                                           'x
                                                                                                                           (__toplevel_cons (__toplevel_cons 'difference (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                     (__toplevel_cons
                                                                                                                        (__toplevel_cons
                                                                                                                           'and
                                                                                                                           (__toplevel_cons
                                                                                                                              (__toplevel_cons 'numberp (__toplevel_cons 'x ()))
                                                                                                                              (__toplevel_cons
                                                                                                                                 (__toplevel_cons
                                                                                                                                    'or
                                                                                                                                    (__toplevel_cons
                                                                                                                                       (__toplevel_cons 'equal (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                       (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'y ())) ())))
                                                                                                                                 ())))
                                                                                                                        ())))
                                                                                                               (__toplevel_cons
                                                                                                                  (__toplevel_cons
                                                                                                                     'equal
                                                                                                                     (__toplevel_cons
                                                                                                                        (__toplevel_cons
                                                                                                                           'meaning
                                                                                                                           (__toplevel_cons
                                                                                                                              (__toplevel_cons
                                                                                                                                 'plus-tree
                                                                                                                                 (__toplevel_cons (__toplevel_cons 'append (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))
                                                                                                                              (__toplevel_cons 'a ())))
                                                                                                                        (__toplevel_cons
                                                                                                                           (__toplevel_cons
                                                                                                                              'plus
                                                                                                                              (__toplevel_cons
                                                                                                                                 (__toplevel_cons
                                                                                                                                    'meaning
                                                                                                                                    (__toplevel_cons (__toplevel_cons 'plus-tree (__toplevel_cons 'x ())) (__toplevel_cons 'a ())))
                                                                                                                                 (__toplevel_cons
                                                                                                                                    (__toplevel_cons
                                                                                                                                       'meaning
                                                                                                                                       (__toplevel_cons (__toplevel_cons 'plus-tree (__toplevel_cons 'y ())) (__toplevel_cons 'a ())))
                                                                                                                                    ())))
                                                                                                                           ())))
                                                                                                                  (__toplevel_cons
                                                                                                                     (__toplevel_cons
                                                                                                                        'equal
                                                                                                                        (__toplevel_cons
                                                                                                                           (__toplevel_cons
                                                                                                                              'meaning
                                                                                                                              (__toplevel_cons
                                                                                                                                 (__toplevel_cons
                                                                                                                                    'plus-tree
                                                                                                                                    (__toplevel_cons (__toplevel_cons 'plus-fringe (__toplevel_cons 'x ())) ()))
                                                                                                                                 (__toplevel_cons 'a ())))
                                                                                                                           (__toplevel_cons
                                                                                                                              (__toplevel_cons
                                                                                                                                 'fix
                                                                                                                                 (__toplevel_cons (__toplevel_cons 'meaning (__toplevel_cons 'x (__toplevel_cons 'a ()))) ()))
                                                                                                                              ())))
                                                                                                                     (__toplevel_cons
                                                                                                                        (__toplevel_cons
                                                                                                                           'equal
                                                                                                                           (__toplevel_cons
                                                                                                                              (__toplevel_cons
                                                                                                                                 'append
                                                                                                                                 (__toplevel_cons
                                                                                                                                    (__toplevel_cons 'append (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                    (__toplevel_cons 'z ())))
                                                                                                                              (__toplevel_cons
                                                                                                                                 (__toplevel_cons
                                                                                                                                    'append
                                                                                                                                    (__toplevel_cons
                                                                                                                                       'x
                                                                                                                                       (__toplevel_cons (__toplevel_cons 'append (__toplevel_cons 'y (__toplevel_cons 'z ()))) ())))
                                                                                                                                 ())))
                                                                                                                        (__toplevel_cons
                                                                                                                           (__toplevel_cons
                                                                                                                              'equal
                                                                                                                              (__toplevel_cons
                                                                                                                                 (__toplevel_cons
                                                                                                                                    'reverse
                                                                                                                                    (__toplevel_cons (__toplevel_cons 'append (__toplevel_cons 'a (__toplevel_cons 'b ()))) ()))
                                                                                                                                 (__toplevel_cons
                                                                                                                                    (__toplevel_cons
                                                                                                                                       'append
                                                                                                                                       (__toplevel_cons
                                                                                                                                          (__toplevel_cons 'reverse (__toplevel_cons 'b ()))
                                                                                                                                          (__toplevel_cons (__toplevel_cons 'reverse (__toplevel_cons 'a ())) ())))
                                                                                                                                    ())))
                                                                                                                           (__toplevel_cons
                                                                                                                              (__toplevel_cons
                                                                                                                                 'equal
                                                                                                                                 (__toplevel_cons
                                                                                                                                    (__toplevel_cons
                                                                                                                                       'times
                                                                                                                                       (__toplevel_cons
                                                                                                                                          'x
                                                                                                                                          (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'y (__toplevel_cons 'z ()))) ())))
                                                                                                                                    (__toplevel_cons
                                                                                                                                       (__toplevel_cons
                                                                                                                                          'plus
                                                                                                                                          (__toplevel_cons
                                                                                                                                             (__toplevel_cons 'times (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                             (__toplevel_cons (__toplevel_cons 'times (__toplevel_cons 'x (__toplevel_cons 'z ()))) ())))
                                                                                                                                       ())))
                                                                                                                              (__toplevel_cons
                                                                                                                                 (__toplevel_cons
                                                                                                                                    'equal
                                                                                                                                    (__toplevel_cons
                                                                                                                                       (__toplevel_cons
                                                                                                                                          'times
                                                                                                                                          (__toplevel_cons
                                                                                                                                             (__toplevel_cons 'times (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                             (__toplevel_cons 'z ())))
                                                                                                                                       (__toplevel_cons
                                                                                                                                          (__toplevel_cons
                                                                                                                                             'times
                                                                                                                                             (__toplevel_cons
                                                                                                                                                'x
                                                                                                                                                (__toplevel_cons (__toplevel_cons 'times (__toplevel_cons 'y (__toplevel_cons 'z ()))) ())))
                                                                                                                                          ())))
                                                                                                                                 (__toplevel_cons
                                                                                                                                    (__toplevel_cons
                                                                                                                                       'equal
                                                                                                                                       (__toplevel_cons
                                                                                                                                          (__toplevel_cons
                                                                                                                                             'equal
                                                                                                                                             (__toplevel_cons
                                                                                                                                                (__toplevel_cons 'times (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                          (__toplevel_cons
                                                                                                                                             (__toplevel_cons
                                                                                                                                                'or
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   (__toplevel_cons 'zerop (__toplevel_cons 'x ()))
                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'y ())) ())))
                                                                                                                                             ())))
                                                                                                                                    (__toplevel_cons
                                                                                                                                       (__toplevel_cons
                                                                                                                                          'equal
                                                                                                                                          (__toplevel_cons
                                                                                                                                             (__toplevel_cons
                                                                                                                                                'exec
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   (__toplevel_cons 'append (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                   (__toplevel_cons 'pds (__toplevel_cons 'envrn ()))))
                                                                                                                                             (__toplevel_cons
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   'exec
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      'y
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         (__toplevel_cons 'exec (__toplevel_cons 'x (__toplevel_cons 'pds (__toplevel_cons 'envrn ()))))
                                                                                                                                                         (__toplevel_cons 'envrn ()))))
                                                                                                                                                ())))
                                                                                                                                       (__toplevel_cons
                                                                                                                                          (__toplevel_cons
                                                                                                                                             'equal
                                                                                                                                             (__toplevel_cons
                                                                                                                                                (__toplevel_cons 'mc-flatten (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      'append
                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'flatten (__toplevel_cons 'x ())) (__toplevel_cons 'y ())))
                                                                                                                                                   ())))
                                                                                                                                          (__toplevel_cons
                                                                                                                                             (__toplevel_cons
                                                                                                                                                'equal
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      'member
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         'x
                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'append (__toplevel_cons 'a (__toplevel_cons 'b ()))) ())))
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         'or
                                                                                                                                                         (__toplevel_cons
                                                                                                                                                            (__toplevel_cons 'member (__toplevel_cons 'x (__toplevel_cons 'a ())))
                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'member (__toplevel_cons 'x (__toplevel_cons 'b ()))) ())))
                                                                                                                                                      ())))
                                                                                                                                             (__toplevel_cons
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   'equal
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         'member
                                                                                                                                                         (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'reverse (__toplevel_cons 'y ())) ())))
                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'member (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                (__toplevel_cons
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      'equal
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         (__toplevel_cons 'length (__toplevel_cons (__toplevel_cons 'reverse (__toplevel_cons 'x ())) ()))
                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'length (__toplevel_cons 'x ())) ())))
                                                                                                                                                   (__toplevel_cons
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         'equal
                                                                                                                                                         (__toplevel_cons
                                                                                                                                                            (__toplevel_cons
                                                                                                                                                               'member
                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                  'a
                                                                                                                                                                  (__toplevel_cons (__toplevel_cons 'intersect (__toplevel_cons 'b (__toplevel_cons 'c ()))) ())))
                                                                                                                                                            (__toplevel_cons
                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                  'and
                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                     (__toplevel_cons 'member (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                                                                                                                                     (__toplevel_cons (__toplevel_cons 'member (__toplevel_cons 'a (__toplevel_cons 'c ()))) ())))
                                                                                                                                                               ())))
                                                                                                                                                      (__toplevel_cons
                                                                                                                                                         (__toplevel_cons
                                                                                                                                                            'equal
                                                                                                                                                            (__toplevel_cons
                                                                                                                                                               (__toplevel_cons 'nth (__toplevel_cons (__toplevel_cons 'zero ()) (__toplevel_cons 'i ())))
                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                         (__toplevel_cons
                                                                                                                                                            (__toplevel_cons
                                                                                                                                                               'equal
                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                     'exp
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        'i
                                                                                                                                                                        (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'j (__toplevel_cons 'k ()))) ())))
                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        'times
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           (__toplevel_cons 'exp (__toplevel_cons 'i (__toplevel_cons 'j ())))
                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'exp (__toplevel_cons 'i (__toplevel_cons 'k ()))) ())))
                                                                                                                                                                     ())))
                                                                                                                                                            (__toplevel_cons
                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                  'equal
                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        'exp
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           'i
                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'times (__toplevel_cons 'j (__toplevel_cons 'k ()))) ())))
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           'exp
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              (__toplevel_cons 'exp (__toplevel_cons 'i (__toplevel_cons 'j ())))
                                                                                                                                                                              (__toplevel_cons 'k ())))
                                                                                                                                                                        ())))
                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                     'equal
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        (__toplevel_cons 'reverse-loop (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              'append
                                                                                                                                                                              (__toplevel_cons (__toplevel_cons 'reverse (__toplevel_cons 'x ())) (__toplevel_cons 'y ())))
                                                                                                                                                                           ())))
                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        'equal
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           (__toplevel_cons 'reverse-loop (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'nil ()) ())))
                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'reverse (__toplevel_cons 'x ())) ())))
                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           'equal
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 'count-list
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    'z
                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'sort-lp (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    'plus
                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                       (__toplevel_cons 'count-list (__toplevel_cons 'z (__toplevel_cons 'x ())))
                                                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'count-list (__toplevel_cons 'z (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                 ())))
                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              'equal
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    'equal
                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                       (__toplevel_cons 'append (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'append (__toplevel_cons 'a (__toplevel_cons 'c ()))) ())))
                                                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'equal (__toplevel_cons 'b (__toplevel_cons 'c ()))) ())))
                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 'equal
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                       'plus
                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                          (__toplevel_cons 'remainder (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                'times
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   'y
                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'quotient (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                             ())))
                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'x ())) ())))
                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    'equal
                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                          'power-eval
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             (__toplevel_cons 'big-plus1 (__toplevel_cons 'l (__toplevel_cons 'i (__toplevel_cons 'base ()))))
                                                                                                                                                                                             (__toplevel_cons 'base ())))
                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             'plus
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                (__toplevel_cons 'power-eval (__toplevel_cons 'l (__toplevel_cons 'base ())))
                                                                                                                                                                                                (__toplevel_cons 'i ())))
                                                                                                                                                                                          ())))
                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                       'equal
                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             'power-eval
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   'big-plus
                                                                                                                                                                                                   (__toplevel_cons 'x (__toplevel_cons 'y (__toplevel_cons 'i (__toplevel_cons 'base ())))))
                                                                                                                                                                                                (__toplevel_cons 'base ())))
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                'plus
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   'i
                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                         'plus
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            (__toplevel_cons 'power-eval (__toplevel_cons 'x (__toplevel_cons 'base ())))
                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'power-eval (__toplevel_cons 'y (__toplevel_cons 'base ()))) ())))
                                                                                                                                                                                                      ())))
                                                                                                                                                                                             ())))
                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                          'equal
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             (__toplevel_cons 'remainder (__toplevel_cons 'y (__toplevel_cons 1 ())))
                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             'equal
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   'lessp
                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                      (__toplevel_cons 'remainder (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                      (__toplevel_cons 'y ())))
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   (__toplevel_cons 'not (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'y ())) ()))
                                                                                                                                                                                                   ())))
                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                'equal
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   (__toplevel_cons 'remainder (__toplevel_cons 'x (__toplevel_cons 'x ())))
                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   'equal
                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                         'lessp
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            (__toplevel_cons 'quotient (__toplevel_cons 'i (__toplevel_cons 'j ())))
                                                                                                                                                                                                            (__toplevel_cons 'i ())))
                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            'and
                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                               (__toplevel_cons 'not (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'i ())) ()))
                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                     'or
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        (__toplevel_cons 'zerop (__toplevel_cons 'j ()))
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              'not
                                                                                                                                                                                                                              (__toplevel_cons (__toplevel_cons 'equal (__toplevel_cons 'j (__toplevel_cons 1 ()))) ()))
                                                                                                                                                                                                                           ())))
                                                                                                                                                                                                                  ())))
                                                                                                                                                                                                         ())))
                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                      'equal
                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            'lessp
                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                               (__toplevel_cons 'remainder (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                               (__toplevel_cons 'x ())))
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                               'and
                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                  (__toplevel_cons 'not (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'y ())) ()))
                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                     (__toplevel_cons 'not (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'x ())) ()))
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           'not
                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))
                                                                                                                                                                                                                        ()))))
                                                                                                                                                                                                            ())))
                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                         'equal
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                               'power-eval
                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                  (__toplevel_cons 'power-rep (__toplevel_cons 'i (__toplevel_cons 'base ())))
                                                                                                                                                                                                                  (__toplevel_cons 'base ())))
                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'i ())) ())))
                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            'equal
                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                  'power-eval
                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        'big-plus
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           (__toplevel_cons 'power-rep (__toplevel_cons 'i (__toplevel_cons 'base ())))
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              (__toplevel_cons 'power-rep (__toplevel_cons 'j (__toplevel_cons 'base ())))
                                                                                                                                                                                                                              (__toplevel_cons (__toplevel_cons 'zero ()) (__toplevel_cons 'base ())))))
                                                                                                                                                                                                                     (__toplevel_cons 'base ())))
                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'i (__toplevel_cons 'j ()))) ())))
                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                               'equal
                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                  (__toplevel_cons 'gcd (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                  (__toplevel_cons (__toplevel_cons 'gcd (__toplevel_cons 'y (__toplevel_cons 'x ()))) ())))
                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                  'equal
                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        'nth
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           (__toplevel_cons 'append (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                                                                                                                                                                                           (__toplevel_cons 'i ())))
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           'append
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              (__toplevel_cons 'nth (__toplevel_cons 'a (__toplevel_cons 'i ())))
                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                    'nth
                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                       'b
                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                             'difference
                                                                                                                                                                                                                                             (__toplevel_cons 'i (__toplevel_cons (__toplevel_cons 'length (__toplevel_cons 'a ())) ())))
                                                                                                                                                                                                                                          ())))
                                                                                                                                                                                                                                 ())))
                                                                                                                                                                                                                        ())))
                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                     'equal
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           'difference
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              (__toplevel_cons 'plus (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                              (__toplevel_cons 'x ())))
                                                                                                                                                                                                                        (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'y ())) ())))
                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        'equal
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              'difference
                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                 (__toplevel_cons 'plus (__toplevel_cons 'y (__toplevel_cons 'x ())))
                                                                                                                                                                                                                                 (__toplevel_cons 'x ())))
                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'y ())) ())))
                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           'equal
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                 'difference
                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                    (__toplevel_cons 'plus (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'x (__toplevel_cons 'z ()))) ())))
                                                                                                                                                                                                                              (__toplevel_cons (__toplevel_cons 'difference (__toplevel_cons 'y (__toplevel_cons 'z ()))) ())))
                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              'equal
                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                    'times
                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                       'x
                                                                                                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'difference (__toplevel_cons 'c (__toplevel_cons 'w ()))) ())))
                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                       'difference
                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                          (__toplevel_cons 'times (__toplevel_cons 'c (__toplevel_cons 'x ())))
                                                                                                                                                                                                                                          (__toplevel_cons (__toplevel_cons 'times (__toplevel_cons 'w (__toplevel_cons 'x ()))) ())))
                                                                                                                                                                                                                                    ())))
                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                 'equal
                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                       'remainder
                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                          (__toplevel_cons 'times (__toplevel_cons 'x (__toplevel_cons 'z ())))
                                                                                                                                                                                                                                          (__toplevel_cons 'z ())))
                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                    'equal
                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                          'difference
                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                'plus
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   'b
                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'a (__toplevel_cons 'c ()))) ())))
                                                                                                                                                                                                                                             (__toplevel_cons 'a ())))
                                                                                                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'b (__toplevel_cons 'c ()))) ())))
                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                       'equal
                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                             'difference
                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   'add1
                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'y (__toplevel_cons 'z ()))) ()))
                                                                                                                                                                                                                                                (__toplevel_cons 'z ())))
                                                                                                                                                                                                                                          (__toplevel_cons (__toplevel_cons 'add1 (__toplevel_cons 'y ())) ())))
                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                          'equal
                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                'lessp
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   (__toplevel_cons 'plus (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'x (__toplevel_cons 'z ()))) ())))
                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'y (__toplevel_cons 'z ()))) ())))
                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                             'equal
                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   'lessp
                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                      (__toplevel_cons 'times (__toplevel_cons 'x (__toplevel_cons 'z ())))
                                                                                                                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'times (__toplevel_cons 'y (__toplevel_cons 'z ()))) ())))
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                      'and
                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                         (__toplevel_cons 'not (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'z ())) ()))
                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                                                                                   ())))
                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                'equal
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                      'lessp
                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                         'y
                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                      (__toplevel_cons 'not (__toplevel_cons (__toplevel_cons 'zerop (__toplevel_cons 'x ())) ()))
                                                                                                                                                                                                                                                      ())))
                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   'equal
                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                         'gcd
                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                            (__toplevel_cons 'times (__toplevel_cons 'x (__toplevel_cons 'z ())))
                                                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'times (__toplevel_cons 'y (__toplevel_cons 'z ()))) ())))
                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                            'times
                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                               'z
                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'gcd (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                                                                                         ())))
                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                      'equal
                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                            'value
                                                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'normalize (__toplevel_cons 'x ())) (__toplevel_cons 'a ())))
                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'value (__toplevel_cons 'x (__toplevel_cons 'a ()))) ())))
                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                         'equal
                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                               'equal
                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                  (__toplevel_cons 'flatten (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                     (__toplevel_cons 'cons (__toplevel_cons 'y (__toplevel_cons (__toplevel_cons 'nil ()) ())))
                                                                                                                                                                                                                                                                     ())))
                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                  'and
                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                     (__toplevel_cons 'nlistp (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                     (__toplevel_cons (__toplevel_cons 'equal (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                                                                                               ())))
                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                            'equal
                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                               (__toplevel_cons 'listp (__toplevel_cons (__toplevel_cons 'gopher (__toplevel_cons 'x ())) ()))
                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'listp (__toplevel_cons 'x ())) ())))
                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                               'equal
                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                  (__toplevel_cons 'samefringe (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                        'equal
                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                           (__toplevel_cons 'flatten (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'flatten (__toplevel_cons 'y ())) ())))
                                                                                                                                                                                                                                                                     ())))
                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                  'equal
                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                        'equal
                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                           (__toplevel_cons 'greatest-factor (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                           'and
                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 'or
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    (__toplevel_cons 'zerop (__toplevel_cons 'y ()))
                                                                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'equal (__toplevel_cons 'y (__toplevel_cons 1 ()))) ())))
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 (__toplevel_cons 'equal (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                                                                                 ())))
                                                                                                                                                                                                                                                                        ())))
                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                     'equal
                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                           'equal
                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                              (__toplevel_cons 'greatest-factor (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                              (__toplevel_cons 1 ())))
                                                                                                                                                                                                                                                                        (__toplevel_cons (__toplevel_cons 'equal (__toplevel_cons 'x (__toplevel_cons 1 ()))) ())))
                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                        'equal
                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                              'numberp
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 (__toplevel_cons 'greatest-factor (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                 ()))
                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 'not
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       'and
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             'or
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                (__toplevel_cons 'zerop (__toplevel_cons 'y ()))
                                                                                                                                                                                                                                                                                                (__toplevel_cons (__toplevel_cons 'equal (__toplevel_cons 'y (__toplevel_cons 1 ()))) ())))
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             (__toplevel_cons 'not (__toplevel_cons (__toplevel_cons 'numberp (__toplevel_cons 'x ())) ()))
                                                                                                                                                                                                                                                                                             ())))
                                                                                                                                                                                                                                                                                    ()))
                                                                                                                                                                                                                                                                              ())))
                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                           'equal
                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 'times-list
                                                                                                                                                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'append (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    'times
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       (__toplevel_cons 'times-list (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'times-list (__toplevel_cons 'y ())) ())))
                                                                                                                                                                                                                                                                                 ())))
                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                              'equal
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    'prime-list
                                                                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'append (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       'and
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          (__toplevel_cons 'prime-list (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                                          (__toplevel_cons (__toplevel_cons 'prime-list (__toplevel_cons 'y ())) ())))
                                                                                                                                                                                                                                                                                    ())))
                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 'equal
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       'equal
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          'z
                                                                                                                                                                                                                                                                                          (__toplevel_cons (__toplevel_cons 'times (__toplevel_cons 'w (__toplevel_cons 'z ()))) ())))
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          'and
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             (__toplevel_cons 'numberp (__toplevel_cons 'z ()))
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   'or
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      (__toplevel_cons 'equal (__toplevel_cons 'z (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'equal (__toplevel_cons 'w (__toplevel_cons 1 ()))) ())))
                                                                                                                                                                                                                                                                                                ())))
                                                                                                                                                                                                                                                                                       ())))
                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    'equal
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       (__toplevel_cons 'greatereqpr (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             'not
                                                                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))
                                                                                                                                                                                                                                                                                          ())))
                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       'equal
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             'equal
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                'x
                                                                                                                                                                                                                                                                                                (__toplevel_cons (__toplevel_cons 'times (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                'or
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   (__toplevel_cons 'equal (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                         'and
                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'numberp (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'equal (__toplevel_cons 'y (__toplevel_cons 1 ()))) ())))
                                                                                                                                                                                                                                                                                                      ())))
                                                                                                                                                                                                                                                                                             ())))
                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          'equal
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                'remainder
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   (__toplevel_cons 'times (__toplevel_cons 'y (__toplevel_cons 'x ())))
                                                                                                                                                                                                                                                                                                   (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             'equal
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   'equal
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      (__toplevel_cons 'times (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                                                                                                                                                                                                                                                                      (__toplevel_cons 1 ())))
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      'and
                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                            'not
                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'equal (__toplevel_cons 'a (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                                                                                                               ()))
                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                               'not
                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'equal (__toplevel_cons 'b (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                                                                                                                  ()))
                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'numberp (__toplevel_cons 'a ()))
                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'numberp (__toplevel_cons 'b ()))
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                        'equal
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons '1- (__toplevel_cons 'a ()))
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           'equal
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons '1- (__toplevel_cons 'b ()))
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                                                                                                                                                                                                                                                                                        ())))))))
                                                                                                                                                                                                                                                                                                   ())))
                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                'equal
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      'lessp
                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                            'length
                                                                                                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'delete (__toplevel_cons 'x (__toplevel_cons 'l ()))) ()))
                                                                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'length (__toplevel_cons 'l ())) ())))
                                                                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'member (__toplevel_cons 'x (__toplevel_cons 'l ()))) ())))
                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   'equal
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                         'sort2
                                                                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'delete (__toplevel_cons 'x (__toplevel_cons 'l ()))) ()))
                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                            'delete
                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'sort2 (__toplevel_cons 'l ())) ())))
                                                                                                                                                                                                                                                                                                         ())))
                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      'equal
                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                         (__toplevel_cons 'dsort (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'sort2 (__toplevel_cons 'x ())) ())))
                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                         'equal
                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                               'length
                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                     'cons
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                        'x1
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              'cons
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 'x2
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       'cons
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          'x3
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                'cons
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   'x4
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         'cons
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                            'x5
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'cons (__toplevel_cons 'x6 (__toplevel_cons 'x7 ()))) ())))
                                                                                                                                                                                                                                                                                                                                                      ())))
                                                                                                                                                                                                                                                                                                                                             ())))
                                                                                                                                                                                                                                                                                                                                    ())))
                                                                                                                                                                                                                                                                                                                           ())))
                                                                                                                                                                                                                                                                                                                  ()))
                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                  'plus
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 6 (__toplevel_cons (__toplevel_cons 'length (__toplevel_cons 'x7 ())) ())))
                                                                                                                                                                                                                                                                                                               ())))
                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                            'equal
                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                  'difference
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons 'add1 (__toplevel_cons (__toplevel_cons 'add1 (__toplevel_cons 'x ())) ()))
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons 2 ())))
                                                                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'x ())) ())))
                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                               'equal
                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                     'quotient
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           'plus
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              'x
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons 2 ())))
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                        'plus
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           'x
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'quotient (__toplevel_cons 'y (__toplevel_cons 2 ()))) ())))
                                                                                                                                                                                                                                                                                                                     ())))
                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                  'equal
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons 'sigma (__toplevel_cons (__toplevel_cons 'zero ()) (__toplevel_cons 'i ())))
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           'quotient
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 'times
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons 'i (__toplevel_cons (__toplevel_cons 'add1 (__toplevel_cons 'i ())) ())))
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons 2 ())))
                                                                                                                                                                                                                                                                                                                        ())))
                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                     'equal
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           'plus
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'add1 (__toplevel_cons 'y ())) ())))
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              'if
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons 'numberp (__toplevel_cons 'y ()))
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       'add1
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'add1 (__toplevel_cons 'x ())) ()))))
                                                                                                                                                                                                                                                                                                                           ())))
                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                        'equal
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              'equal
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons 'difference (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'difference (__toplevel_cons 'z (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 'if
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'lessp (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          'not
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'y (__toplevel_cons 'z ()))) ()))
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             'if
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'lessp (__toplevel_cons 'z (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      'not
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'lessp (__toplevel_cons 'y (__toplevel_cons 'x ()))) ()))
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         'equal
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'fix (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'z ())) ())))
                                                                                                                                                                                                                                                                                                                                                      ()))))
                                                                                                                                                                                                                                                                                                                                          ()))))
                                                                                                                                                                                                                                                                                                                              ())))
                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           'equal
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 'meaning
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       'plus-tree
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'delete (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'a ())))
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    'if
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons 'member (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             'difference
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   'meaning
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'plus-tree (__toplevel_cons 'y ())) (__toplevel_cons 'a ())))
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons (__toplevel_cons 'meaning (__toplevel_cons 'x (__toplevel_cons 'a ()))) ())))
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                'meaning
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons (__toplevel_cons 'plus-tree (__toplevel_cons 'y ())) (__toplevel_cons 'a ())))
                                                                                                                                                                                                                                                                                                                                             ()))))
                                                                                                                                                                                                                                                                                                                                 ())))
                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              'equal
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    'times
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'x (__toplevel_cons (__toplevel_cons 'add1 (__toplevel_cons 'y ())) ())))
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       'if
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons 'numberp (__toplevel_cons 'y ()))
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                'plus
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   'x
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'times (__toplevel_cons 'x (__toplevel_cons 'y ()))) ())))
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'x ())) ()))))
                                                                                                                                                                                                                                                                                                                                    ())))
                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 'equal
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'nth (__toplevel_cons (__toplevel_cons 'nil ()) (__toplevel_cons 'i ())))
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          'if
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons 'zerop (__toplevel_cons 'i ()))
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'nil ()) (__toplevel_cons (__toplevel_cons 'zero ()) ()))))
                                                                                                                                                                                                                                                                                                                                       ())))
                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    'equal
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          'last
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons (__toplevel_cons 'append (__toplevel_cons 'a (__toplevel_cons 'b ()))) ()))
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             'if
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'listp (__toplevel_cons 'b ()))
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons 'last (__toplevel_cons 'b ()))
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         'if
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'listp (__toplevel_cons 'a ()))
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                  'cons
                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons 'car (__toplevel_cons (__toplevel_cons 'last (__toplevel_cons 'a ())) ()))
                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons 'b ())))
                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'b ()))))
                                                                                                                                                                                                                                                                                                                                                      ()))))
                                                                                                                                                                                                                                                                                                                                          ())))
                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       'equal
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             'equal
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'lessp (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'z ())))
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                'if
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons 'lessp (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons 'equal (__toplevel_cons 't (__toplevel_cons 'z ())))
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'equal (__toplevel_cons 'f (__toplevel_cons 'z ()))) ()))))
                                                                                                                                                                                                                                                                                                                                             ())))
                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          'equal
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                'assignment
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   'x
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'append (__toplevel_cons 'a (__toplevel_cons 'b ()))) ())))
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   'if
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons 'assignedp (__toplevel_cons 'x (__toplevel_cons 'a ())))
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons 'assignment (__toplevel_cons 'x (__toplevel_cons 'a ())))
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'assignment (__toplevel_cons 'x (__toplevel_cons 'b ()))) ()))))
                                                                                                                                                                                                                                                                                                                                                ())))
                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             'equal
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'car (__toplevel_cons (__toplevel_cons 'gopher (__toplevel_cons 'x ())) ()))
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      'if
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons 'listp (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'car (__toplevel_cons (__toplevel_cons 'flatten (__toplevel_cons 'x ())) ()))
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'zero ()) ()))))
                                                                                                                                                                                                                                                                                                                                                   ())))
                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                'equal
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      'flatten
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons 'cdr (__toplevel_cons (__toplevel_cons 'gopher (__toplevel_cons 'x ())) ()))
                                                                                                                                                                                                                                                                                                                                                         ()))
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         'if
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'listp (__toplevel_cons 'x ()))
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'cdr (__toplevel_cons (__toplevel_cons 'flatten (__toplevel_cons 'x ())) ()))
                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                     'cons
                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons (__toplevel_cons 'zero ()) (__toplevel_cons (__toplevel_cons 'nil ()) ())))
                                                                                                                                                                                                                                                                                                                                                                  ()))))
                                                                                                                                                                                                                                                                                                                                                      ())))
                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   'equal
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         'quotient
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'times (__toplevel_cons 'y (__toplevel_cons 'x ())))
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'y ())))
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                            'if
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'zerop (__toplevel_cons 'y ()))
                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'zero ())
                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons (__toplevel_cons 'fix (__toplevel_cons 'x ())) ()))))
                                                                                                                                                                                                                                                                                                                                                         ())))
                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                      'equal
                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                            'get
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                               'j
                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'set (__toplevel_cons 'i (__toplevel_cons 'val (__toplevel_cons 'mem ()))))
                                                                                                                                                                                                                                                                                                                                                                  ())))
                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                               'if
                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'eqp (__toplevel_cons 'j (__toplevel_cons 'i ())))
                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                     'val
                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons (__toplevel_cons 'get (__toplevel_cons 'j (__toplevel_cons 'mem ()))) ()))))
                                                                                                                                                                                                                                                                                                                                                            ())))
                                                                                                                                                                                                                                                                                                                                                   ())))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         (tautologyp (lambda (x true-lst false-lst)
                       (<change>
                          (if (truep x true-lst)
                             #t
                             (if (falsep x false-lst)
                                #f
                                (if (not (pair? x))
                                   #f
                                   (if (eq? (car x) 'if)
                                      (if (truep (cadr x) true-lst)
                                         (tautologyp (caddr x) true-lst false-lst)
                                         (if (falsep (cadr x) false-lst)
                                            (tautologyp (cadddr x) true-lst false-lst)
                                            (if (tautologyp (caddr x) (cons (cadr x) true-lst) false-lst)
                                               (tautologyp (cadddr x) true-lst (cons (cadr x) false-lst))
                                               #f)))
                                      #f))))
                          ((lambda (x) x)
                             (if (truep x true-lst)
                                #t
                                (if (falsep x false-lst)
                                   #f
                                   (if (not (pair? x))
                                      #f
                                      (if (eq? (car x) 'if)
                                         (<change>
                                            (if (truep (cadr x) true-lst)
                                               (tautologyp (caddr x) true-lst false-lst)
                                               (if (falsep (cadr x) false-lst)
                                                  (tautologyp (cadddr x) true-lst false-lst)
                                                  (if (tautologyp (caddr x) (cons (cadr x) true-lst) false-lst)
                                                     (tautologyp (cadddr x) true-lst (cons (cadr x) false-lst))
                                                     #f)))
                                            #f)
                                         (<change>
                                            #f
                                            (if (truep (cadr x) true-lst)
                                               (tautologyp (caddr x) true-lst false-lst)
                                               (if (falsep (cadr x) false-lst)
                                                  (tautologyp (cadddr x) true-lst false-lst)
                                                  (if (tautologyp (caddr x) (cons (cadr x) true-lst) false-lst)
                                                     (tautologyp (cadddr x) true-lst (cons (cadr x) false-lst))
                                                     #f))))))))))))
         (tautp (lambda (x)
                  (tautologyp (rewrite x) () ())))
         (test (lambda ()
                 (letrec ((ans #f)
                          (term #f))
                    (<change>
                       (set! term (apply-subst
                                  (__toplevel_cons
                                     (__toplevel_cons
                                        'x
                                        (__toplevel_cons
                                           'f
                                           (__toplevel_cons
                                              (__toplevel_cons
                                                 'plus
                                                 (__toplevel_cons
                                                    (__toplevel_cons 'plus (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                    (__toplevel_cons
                                                       (__toplevel_cons 'plus (__toplevel_cons 'c (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                       ())))
                                              ())))
                                     (__toplevel_cons
                                        (__toplevel_cons
                                           'y
                                           (__toplevel_cons
                                              'f
                                              (__toplevel_cons
                                                 (__toplevel_cons
                                                    'times
                                                    (__toplevel_cons
                                                       (__toplevel_cons 'times (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                       (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'c (__toplevel_cons 'd ()))) ())))
                                                 ())))
                                        (__toplevel_cons
                                           (__toplevel_cons
                                              'z
                                              (__toplevel_cons
                                                 'f
                                                 (__toplevel_cons
                                                    (__toplevel_cons
                                                       'reverse
                                                       (__toplevel_cons
                                                          (__toplevel_cons
                                                             'append
                                                             (__toplevel_cons
                                                                (__toplevel_cons 'append (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                                (__toplevel_cons (__toplevel_cons 'nil ()) ())))
                                                          ()))
                                                    ())))
                                           (__toplevel_cons
                                              (__toplevel_cons
                                                 'u
                                                 (__toplevel_cons
                                                    'equal
                                                    (__toplevel_cons
                                                       (__toplevel_cons 'plus (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                       (__toplevel_cons (__toplevel_cons 'difference (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))))
                                              (__toplevel_cons
                                                 (__toplevel_cons
                                                    'w
                                                    (__toplevel_cons
                                                       'lessp
                                                       (__toplevel_cons
                                                          (__toplevel_cons 'remainder (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                          (__toplevel_cons
                                                             (__toplevel_cons
                                                                'member
                                                                (__toplevel_cons 'a (__toplevel_cons (__toplevel_cons 'length (__toplevel_cons 'b ())) ())))
                                                             ()))))
                                                 ())))))
                                  (__toplevel_cons
                                     'implies
                                     (__toplevel_cons
                                        (__toplevel_cons
                                           'and
                                           (__toplevel_cons
                                              (__toplevel_cons 'implies (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                              (__toplevel_cons
                                                 (__toplevel_cons
                                                    'and
                                                    (__toplevel_cons
                                                       (__toplevel_cons 'implies (__toplevel_cons 'y (__toplevel_cons 'z ())))
                                                       (__toplevel_cons
                                                          (__toplevel_cons
                                                             'and
                                                             (__toplevel_cons
                                                                (__toplevel_cons 'implies (__toplevel_cons 'z (__toplevel_cons 'u ())))
                                                                (__toplevel_cons (__toplevel_cons 'implies (__toplevel_cons 'u (__toplevel_cons 'w ()))) ())))
                                                          ())))
                                                 ())))
                                        (__toplevel_cons (__toplevel_cons 'implies (__toplevel_cons 'x (__toplevel_cons 'w ()))) ())))))
                       (set! ans (tautp term)))
                    (<change>
                       (set! ans (tautp term))
                       (set! term (apply-subst
                                  (__toplevel_cons
                                     (__toplevel_cons
                                        'x
                                        (__toplevel_cons
                                           'f
                                           (__toplevel_cons
                                              (__toplevel_cons
                                                 'plus
                                                 (__toplevel_cons
                                                    (__toplevel_cons 'plus (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                    (__toplevel_cons
                                                       (__toplevel_cons 'plus (__toplevel_cons 'c (__toplevel_cons (__toplevel_cons 'zero ()) ())))
                                                       ())))
                                              ())))
                                     (__toplevel_cons
                                        (__toplevel_cons
                                           'y
                                           (__toplevel_cons
                                              'f
                                              (__toplevel_cons
                                                 (__toplevel_cons
                                                    'times
                                                    (__toplevel_cons
                                                       (__toplevel_cons 'times (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                       (__toplevel_cons (__toplevel_cons 'plus (__toplevel_cons 'c (__toplevel_cons 'd ()))) ())))
                                                 ())))
                                        (__toplevel_cons
                                           (__toplevel_cons
                                              'z
                                              (__toplevel_cons
                                                 'f
                                                 (__toplevel_cons
                                                    (__toplevel_cons
                                                       'reverse
                                                       (__toplevel_cons
                                                          (__toplevel_cons
                                                             'append
                                                             (__toplevel_cons
                                                                (__toplevel_cons 'append (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                                (__toplevel_cons (__toplevel_cons 'nil ()) ())))
                                                          ()))
                                                    ())))
                                           (__toplevel_cons
                                              (__toplevel_cons
                                                 'u
                                                 (__toplevel_cons
                                                    'equal
                                                    (__toplevel_cons
                                                       (__toplevel_cons 'plus (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                       (__toplevel_cons (__toplevel_cons 'difference (__toplevel_cons 'x (__toplevel_cons 'y ()))) ()))))
                                              (__toplevel_cons
                                                 (__toplevel_cons
                                                    'w
                                                    (__toplevel_cons
                                                       'lessp
                                                       (__toplevel_cons
                                                          (__toplevel_cons 'remainder (__toplevel_cons 'a (__toplevel_cons 'b ())))
                                                          (__toplevel_cons
                                                             (__toplevel_cons
                                                                'member
                                                                (__toplevel_cons 'a (__toplevel_cons (__toplevel_cons 'length (__toplevel_cons 'b ())) ())))
                                                             ()))))
                                                 ())))))
                                  (__toplevel_cons
                                     'implies
                                     (__toplevel_cons
                                        (__toplevel_cons
                                           'and
                                           (__toplevel_cons
                                              (__toplevel_cons 'implies (__toplevel_cons 'x (__toplevel_cons 'y ())))
                                              (__toplevel_cons
                                                 (__toplevel_cons
                                                    'and
                                                    (__toplevel_cons
                                                       (__toplevel_cons 'implies (__toplevel_cons 'y (__toplevel_cons 'z ())))
                                                       (__toplevel_cons
                                                          (__toplevel_cons
                                                             'and
                                                             (__toplevel_cons
                                                                (__toplevel_cons 'implies (__toplevel_cons 'z (__toplevel_cons 'u ())))
                                                                (__toplevel_cons (__toplevel_cons 'implies (__toplevel_cons 'u (__toplevel_cons 'w ()))) ())))
                                                          ())))
                                                 ())))
                                        (__toplevel_cons (__toplevel_cons 'implies (__toplevel_cons 'x (__toplevel_cons 'w ()))) ()))))))
                    ans)))
         (trans-of-implies (lambda (n)
                             (list 'implies (trans-of-implies1 n) (list 'implies 0 n))))
         (trans-of-implies1 (lambda (n)
                              (if (eq? n 1)
                                 (list 'implies 0 1)
                                 (list 'and (list 'implies (- n 1) n) (trans-of-implies1 (- n 1))))))
         (truep (lambda (x lst)
                  (let ((__or_res (eq? x (__toplevel_cons 't ()))))
                     (<change>
                        (if __or_res __or_res (member x lst))
                        ((lambda (x) x) (if __or_res __or_res (member x lst))))))))
   (run-benchmark "Boyer" (lambda () (setup) (test))))