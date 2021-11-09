; Changes:
; * removed: 1
; * added: 9
; * swaps: 2
; * negated predicates: 1
; * swapped branches: 4
; * calls to id fun: 8
(letrec ((true #t)
         (false #f)
         (apply-in-underlying-scheme (lambda (proc args)
                                       (if (null? args)
                                          (proc)
                                          (if (null? (cdr args))
                                             (proc (car args))
                                             (if (null? (cddr args))
                                                (proc (car args) (cadr args))
                                                (if (null? (cdddr args))
                                                   (<change>
                                                      (proc (car args) (cadr args) (caddr args))
                                                      (if (null? (cddddr args))
                                                         (proc (car args) (cadr args) (caddr args) (cadddr args))
                                                         (if (null? (cdr (cddddr args)))
                                                            (proc (car args) (cadr args) (caddr args) (cadddr args) (car (cddddr args)))
                                                            (error "Unsupported call."))))
                                                   (<change>
                                                      (if (null? (cddddr args))
                                                         (proc (car args) (cadr args) (caddr args) (cadddr args))
                                                         (if (null? (cdr (cddddr args)))
                                                            (proc (car args) (cadr args) (caddr args) (cadddr args) (car (cddddr args)))
                                                            (error "Unsupported call.")))
                                                      (proc (car args) (cadr args) (caddr args)))))))))
         (true? (lambda (x)
                  (not (eq? x false))))
         (false? (lambda (x)
                   (eq? x false)))
         (self-evaluating? (lambda (exp)
                             (if (number? exp)
                                true
                                (if (string? exp) true false))))
         (tagged-list? (lambda (exp tag)
                         (if (pair? exp) (eq? (car exp) tag) false)))
         (quoted? (lambda (exp)
                    (tagged-list? exp 'quote)))
         (text-of-quotation (lambda (exp)
                              (cadr exp)))
         (variable? (lambda (exp)
                      (symbol? exp)))
         (assignment? (lambda (exp)
                        (tagged-list? exp 'set!)))
         (assignment-variable (lambda (exp)
                                (cadr exp)))
         (assignment-value (lambda (exp)
                             (caddr exp)))
         (definition? (lambda (exp)
                        (tagged-list? exp 'define)))
         (definition-variable (lambda (exp)
                                (if (symbol? (cadr exp)) (cadr exp) (caadr exp))))
         (definition-value (lambda (exp)
                             (if (symbol? (cadr exp))
                                (caddr exp)
                                (make-lambda (cdadr exp) (cddr exp)))))
         (if? (lambda (exp)
                (tagged-list? exp 'if)))
         (if-predicate (lambda (exp)
                         (<change>
                            (cadr exp)
                            ((lambda (x) x) (cadr exp)))))
         (if-consequent (lambda (exp)
                          (caddr exp)))
         (if-alternative (lambda (exp)
                           (if (not (null? (cdddr exp)))
                              (cadddr exp)
                              'false)))
         (make-if (lambda (predicate consequent alternative)
                    (list 'if predicate consequent alternative)))
         (lambda? (lambda (exp)
                    (<change>
                       ()
                       exp)
                    (tagged-list? exp 'lambda)))
         (lambda-parameters (lambda (exp)
                              (cadr exp)))
         (lambda-body (lambda (exp)
                        (cddr exp)))
         (make-lambda (lambda (parameters body)
                        (cons 'lambda (cons parameters body))))
         (cond? (lambda (exp)
                  (<change>
                     ()
                     (display (tagged-list? exp 'cond)))
                  (tagged-list? exp 'cond)))
         (cond-clauses (lambda (exp)
                         (cdr exp)))
         (cond-else-clause? (lambda (clause)
                              (eq? (cond-predicate clause) 'else)))
         (cond-predicate (lambda (clause)
                           (car clause)))
         (cond-actions (lambda (clause)
                         (cdr clause)))
         (cond->if (lambda (exp)
                     (expand-clauses (cond-clauses exp))))
         (expand-clauses (lambda (clauses)
                           (if (null? clauses)
                              'false
                              (let ((first (car clauses))
                                    (rest (cdr clauses)))
                                 (if (cond-else-clause? first)
                                    (if (null? rest)
                                       (sequence->exp (cond-actions first))
                                       (error "ELSE clause isn't last -- COND->IF"))
                                    (make-if (cond-predicate first) (sequence->exp (cond-actions first)) (expand-clauses rest)))))))
         (begin? (lambda (exp)
                   (tagged-list? exp 'begin)))
         (begin-actions (lambda (exp)
                          (cdr exp)))
         (last-exp? (lambda (seq)
                      (null? (cdr seq))))
         (first-exp (lambda (seq)
                      (car seq)))
         (rest-exps (lambda (seq)
                      (cdr seq)))
         (sequence->exp (lambda (seq)
                          (if (null? seq)
                             seq
                             (if (last-exp? seq)
                                (first-exp seq)
                                (make-begin seq)))))
         (make-begin (lambda (seq)
                       (cons 'begin seq)))
         (application? (lambda (exp)
                         (pair? exp)))
         (operator (lambda (exp)
                     (car exp)))
         (operands (lambda (exp)
                     (cdr exp)))
         (no-operands? (lambda (ops)
                         (null? ops)))
         (first-operand (lambda (ops)
                          (car ops)))
         (rest-operands (lambda (ops)
                          (cdr ops)))
         (make-procedure (lambda (parameters body env)
                           (list 'procedure parameters body env)))
         (compound-procedure? (lambda (p)
                                (tagged-list? p 'procedure)))
         (procedure-parameters (lambda (p)
                                 (cadr p)))
         (procedure-body (lambda (p)
                           (caddr p)))
         (procedure-environment (lambda (p)
                                  (cadddr p)))
         (enclosing-environment (lambda (env)
                                  (cdr env)))
         (first-frame (lambda (env)
                        (car env)))
         (the-empty-environment ())
         (extend-environment (lambda (vars vals base-env)
                               (if (= (length vars) (length vals))
                                  (cons (make-frame vars vals) base-env)
                                  (if (< (length vars) (length vals))
                                     (<change>
                                        (error "Too many arguments supplied")
                                        (error "Too few arguments supplied"))
                                     (<change>
                                        (error "Too few arguments supplied")
                                        (error "Too many arguments supplied"))))))
         (make-frame (lambda (variables values)
                       (<change>
                          (cons variables values)
                          ((lambda (x) x) (cons variables values)))))
         (frame-variables (lambda (frame)
                            (car frame)))
         (frame-values (lambda (frame)
                         (cdr frame)))
         (add-binding-to-frame! (lambda (var val frame)
                                  (set-car! frame (cons var (car frame)))
                                  (set-cdr! frame (cons val (cdr frame)))))
         (lookup-variable-value (lambda (var env)
                                  (letrec ((env-loop (lambda (env)
                                                       (letrec ((scan (lambda (vars vals)
                                                                        (<change>
                                                                           ()
                                                                           null?)
                                                                        (if (null? vars)
                                                                           (env-loop (enclosing-environment env))
                                                                           (if (eq? var (car vars))
                                                                              (car vals)
                                                                              (scan (cdr vars) (cdr vals)))))))
                                                          (if (eq? env the-empty-environment)
                                                             (error "Unbound variable")
                                                             (let ((frame (first-frame env)))
                                                                (scan (frame-variables frame) (frame-values frame))))))))
                                     (env-loop env))))
         (set-variable-value! (lambda (var val env)
                                (letrec ((env-loop (lambda (env)
                                                     (letrec ((scan (lambda (vars vals)
                                                                      (if (null? vars)
                                                                         (env-loop (enclosing-environment env))
                                                                         (if (eq? var (car vars))
                                                                            (set-car! vals val)
                                                                            (scan (cdr vars) (cdr vals)))))))
                                                        (if (eq? env the-empty-environment)
                                                           (error "Unbound variable -- SET!")
                                                           (let ((frame (first-frame env)))
                                                              (scan (frame-variables frame) (frame-values frame))))))))
                                   (env-loop env))))
         (define-variable! (lambda (var val env)
                             (let ((frame (first-frame env)))
                                (letrec ((scan (lambda (vars vals)
                                                 (if (null? vars)
                                                    (add-binding-to-frame! var val frame)
                                                    (if (eq? var (car vars))
                                                       (set-car! vals val)
                                                       (scan (cdr vars) (cdr vals)))))))
                                   (scan (frame-variables frame) (frame-values frame))))))
         (setup-environment (lambda ()
                              (let ((initial-env (extend-environment
                                                   (primitive-procedure-names)
                                                   (primitive-procedure-objects)
                                                   the-empty-environment)))
                                 (<change>
                                    (define-variable! 'true true initial-env)
                                    (define-variable! 'false false initial-env))
                                 (<change>
                                    (define-variable! 'false false initial-env)
                                    (define-variable! 'true true initial-env))
                                 (<change>
                                    ()
                                    initial-env)
                                 initial-env)))
         (primitive-procedure? (lambda (proc)
                                 (tagged-list? proc 'primitive)))
         (primitive-implementation (lambda (proc)
                                     (cadr proc)))
         (primitive-procedures (list
                                 (list 'car car)
                                 (list 'cdr cdr)
                                 (list 'cons cons)
                                 (list 'null? null?)
                                 (list 'list list)
                                 (list 'memq memq)
                                 (list 'member member)
                                 (list 'not not)
                                 (list '+ +)
                                 (list '- -)
                                 (list '* *)
                                 (list '= =)
                                 (list '> >)
                                 (list '>= >=)
                                 (list 'abs abs)
                                 (list 'remainder remainder)
                                 (list 'integer? integer?)
                                 (list 'sqrt sqrt)
                                 (list 'eq? eq?)))
         (primitive-procedure-names (lambda ()
                                      (map car primitive-procedures)))
         (primitive-procedure-objects (lambda ()
                                        (map (lambda (proc) (list 'primitive (cadr proc))) primitive-procedures)))
         (apply-primitive-procedure (lambda (proc args)
                                      (apply-in-underlying-scheme (primitive-implementation proc) args)))
         (input-prompt ";;; Amb-Eval input:")
         (output-prompt ";;; Amb-Eval value:")
         (prompt-for-input (lambda (string)
                             (<change>
                                (newline)
                                (newline))
                             (<change>
                                (newline)
                                (newline))
                             (display string)
                             (newline)))
         (announce-output (lambda (string)
                            (<change>
                               (newline)
                               ())
                            (display string)
                            (<change>
                               ()
                               display)
                            (newline)))
         (user-print (lambda (object)
                       (<change>
                          (if (compound-procedure? object)
                             (display
                                (list 'compound-procedure (procedure-parameters object) (procedure-body object) '<procedure-env>))
                             (display object))
                          ((lambda (x) x)
                             (if (compound-procedure? object)
                                (display
                                   (list 'compound-procedure (procedure-parameters object) (procedure-body object) '<procedure-env>))
                                (display object))))))
         (amb? (lambda (exp)
                 (tagged-list? exp 'amb)))
         (amb-choices (lambda (exp)
                        (cdr exp)))
         (ambeval (lambda (exp env succeed fail)
                    ((analyze exp) env succeed fail)))
         (analyze (lambda (exp)
                    (if (self-evaluating? exp)
                       (analyze-self-evaluating exp)
                       (if (quoted? exp)
                          (analyze-quoted exp)
                          (if (variable? exp)
                             (analyze-variable exp)
                             (if (assignment? exp)
                                (analyze-assignment exp)
                                (if (<change> (definition? exp) (not (definition? exp)))
                                   (analyze-definition exp)
                                   (if (if? exp)
                                      (analyze-if exp)
                                      (if (lambda? exp)
                                         (analyze-lambda exp)
                                         (if (begin? exp)
                                            (analyze-sequence (begin-actions exp))
                                            (if (cond? exp)
                                               (analyze (cond->if exp))
                                               (if (let? exp)
                                                  (<change>
                                                     (analyze (let->combination exp))
                                                     (if (amb? exp)
                                                        (analyze-amb exp)
                                                        (if (application? exp)
                                                           (analyze-application exp)
                                                           (error "Unknown expression type -- ANALYZE"))))
                                                  (<change>
                                                     (if (amb? exp)
                                                        (analyze-amb exp)
                                                        (if (application? exp)
                                                           (analyze-application exp)
                                                           (error "Unknown expression type -- ANALYZE")))
                                                     (analyze (let->combination exp)))))))))))))))
         (analyze-self-evaluating (lambda (exp)
                                    (<change>
                                       ()
                                       (succeed exp fail))
                                    (lambda (env succeed fail)
                                       (<change>
                                          (succeed exp fail)
                                          ((lambda (x) x) (succeed exp fail))))))
         (analyze-quoted (lambda (exp)
                           (let ((qval (text-of-quotation exp)))
                              (lambda (env succeed fail)
                                 (<change>
                                    ()
                                    succeed)
                                 (<change>
                                    ()
                                    qval)
                                 (succeed qval fail)))))
         (analyze-variable (lambda (exp)
                             (<change>
                                ()
                                succeed)
                             (lambda (env succeed fail)
                                (succeed (lookup-variable-value exp env) fail))))
         (analyze-lambda (lambda (exp)
                           (let ((vars (lambda-parameters exp))
                                 (bproc (analyze-sequence (lambda-body exp))))
                              (<change>
                                 (lambda (env succeed fail)
                                    (succeed (make-procedure vars bproc env) fail))
                                 ((lambda (x) x) (lambda (env succeed fail) (succeed (make-procedure vars bproc env) fail)))))))
         (analyze-if (lambda (exp)
                       (let ((pproc (analyze (if-predicate exp)))
                             (cproc (analyze (if-consequent exp)))
                             (aproc (analyze (if-alternative exp))))
                          (lambda (env succeed fail)
                             (pproc
                                env
                                (lambda (pred-value fail2)
                                   (if (true? pred-value)
                                      (<change>
                                         (cproc env succeed fail2)
                                         (aproc env succeed fail2))
                                      (<change>
                                         (aproc env succeed fail2)
                                         (cproc env succeed fail2))))
                                fail)))))
         (analyze-sequence (lambda (exps)
                             (letrec ((sequentially (lambda (a b)
                                                      (lambda (env succeed fail)
                                                         (a env (lambda (a-value fail2) (b env succeed fail2)) fail))))
                                      (loop (lambda (first-proc rest-procs)
                                              (if (null? rest-procs)
                                                 first-proc
                                                 (loop (sequentially first-proc (car rest-procs)) (cdr rest-procs))))))
                                (let ((procs (map analyze exps)))
                                   (if (null? procs)
                                      (error "Empty sequence -- ANALYZE")
                                      #f)
                                   (loop (car procs) (cdr procs))))))
         (analyze-definition (lambda (exp)
                               (let ((var (definition-variable exp))
                                     (vproc (analyze (definition-value exp))))
                                  (lambda (env succeed fail)
                                     (vproc env (lambda (val fail2) (define-variable! var val env) (succeed 'ok fail2)) fail)))))
         (analyze-assignment (lambda (exp)
                               (let ((var (assignment-variable exp))
                                     (vproc (analyze (assignment-value exp))))
                                  (lambda (env succeed fail)
                                     (vproc
                                        env
                                        (lambda (val fail2)
                                           (<change>
                                              (let ((old-value (lookup-variable-value var env)))
                                                 (set-variable-value! var val env)
                                                 (succeed 'ok (lambda () (set-variable-value! var old-value env) (fail2))))
                                              ((lambda (x) x)
                                                 (let ((old-value (lookup-variable-value var env)))
                                                    (set-variable-value! var val env)
                                                    (succeed 'ok (lambda () (set-variable-value! var old-value env) (fail2)))))))
                                        fail)))))
         (analyze-application (lambda (exp)
                                (let ((fproc (analyze (operator exp)))
                                      (aprocs (map analyze (operands exp))))
                                   (lambda (env succeed fail)
                                      (fproc
                                         env
                                         (lambda (proc fail2)
                                            (get-args aprocs env (lambda (args fail3) (execute-application proc args succeed fail3)) fail2))
                                         fail)))))
         (get-args (lambda (aprocs env succeed fail)
                     (if (null? aprocs)
                        (succeed () fail)
                        ((car aprocs)
                           env
                           (lambda (arg fail2)
                              (get-args (cdr aprocs) env (lambda (args fail3) (succeed (cons arg args) fail3)) fail2))
                           fail))))
         (execute-application (lambda (proc args succeed fail)
                                (if (primitive-procedure? proc)
                                   (succeed (apply-primitive-procedure proc args) fail)
                                   (if (compound-procedure? proc)
                                      ((procedure-body proc)
                                         (extend-environment (procedure-parameters proc) args (procedure-environment proc))
                                         succeed
                                         fail)
                                      (error "Unknown procedure type -- EXECUTE-APPLICATION")))))
         (analyze-amb (lambda (exp)
                        (let ((cprocs (map analyze (amb-choices exp))))
                           (lambda (env succeed fail)
                              (letrec ((try-next (lambda (choices)
                                                   (if (null? choices)
                                                      (fail)
                                                      ((car choices) env succeed (lambda () (try-next (cdr choices))))))))
                                 (try-next cprocs))))))
         (let? (lambda (exp)
                 (tagged-list? exp 'let)))
         (let-bindings (lambda (exp)
                         (cadr exp)))
         (let-body (lambda (exp)
                     (cddr exp)))
         (let-var (lambda (binding)
                    (car binding)))
         (let-val (lambda (binding)
                    (<change>
                       (cadr binding)
                       ((lambda (x) x) (cadr binding)))))
         (make-combination (lambda (operator operands)
                             (cons operator operands)))
         (let->combination (lambda (exp)
                             (let ((bindings (let-bindings exp)))
                                (make-combination (make-lambda (map let-var bindings) (let-body exp)) (map let-val bindings)))))
         (the-global-environment (setup-environment))
         (input (__toplevel_cons
                  'begin
                  (__toplevel_cons
                     (__toplevel_cons
                        'define
                        (__toplevel_cons
                           (__toplevel_cons 'require (__toplevel_cons 'p ()))
                           (__toplevel_cons
                              (__toplevel_cons
                                 'if
                                 (__toplevel_cons
                                    (__toplevel_cons 'not (__toplevel_cons 'p ()))
                                    (__toplevel_cons (__toplevel_cons 'amb ()) ())))
                              ())))
                     (__toplevel_cons
                        (__toplevel_cons
                           'define
                           (__toplevel_cons
                              'N
                              (__toplevel_cons
                                 (__toplevel_cons
                                    'quote
                                    (__toplevel_cons
                                       (__toplevel_cons
                                          'naamwoord
                                          (__toplevel_cons 'huis (__toplevel_cons 'kat (__toplevel_cons 'muis ()))))
                                       ()))
                                 ())))
                        (__toplevel_cons
                           (__toplevel_cons
                              'define
                              (__toplevel_cons
                                 'W
                                 (__toplevel_cons
                                    (__toplevel_cons
                                       'quote
                                       (__toplevel_cons
                                          (__toplevel_cons 'werkwoord (__toplevel_cons 'eet (__toplevel_cons 'jaagt ())))
                                          ()))
                                    ())))
                           (__toplevel_cons
                              (__toplevel_cons
                                 'define
                                 (__toplevel_cons
                                    'L
                                    (__toplevel_cons
                                       (__toplevel_cons
                                          'quote
                                          (__toplevel_cons
                                             (__toplevel_cons 'lidwoord (__toplevel_cons 'de (__toplevel_cons 'een (__toplevel_cons 'het ()))))
                                             ()))
                                       ())))
                              (__toplevel_cons
                                 (__toplevel_cons
                                    'define
                                    (__toplevel_cons
                                       'V
                                       (__toplevel_cons
                                          (__toplevel_cons
                                             'quote
                                             (__toplevel_cons (__toplevel_cons 'voorzetsel (__toplevel_cons 'in (__toplevel_cons 'op ()))) ()))
                                          ())))
                                 (__toplevel_cons
                                    (__toplevel_cons
                                       'define
                                       (__toplevel_cons
                                          (__toplevel_cons 'ontleed-zin ())
                                          (__toplevel_cons
                                             (__toplevel_cons
                                                'list
                                                (__toplevel_cons
                                                   (__toplevel_cons 'quote (__toplevel_cons 'zin ()))
                                                   (__toplevel_cons
                                                      (__toplevel_cons 'ontleed-naamwoord-vorm ())
                                                      (__toplevel_cons (__toplevel_cons 'ontleed-werkwoord-vorm ()) ()))))
                                             ())))
                                    (__toplevel_cons
                                       (__toplevel_cons
                                          'define
                                          (__toplevel_cons
                                             (__toplevel_cons 'ontleed-eenvoudige-naamwoord-vorm ())
                                             (__toplevel_cons
                                                (__toplevel_cons
                                                   'list
                                                   (__toplevel_cons
                                                      (__toplevel_cons 'quote (__toplevel_cons 'eenvoudige-naamwoord-vorm ()))
                                                      (__toplevel_cons
                                                         (__toplevel_cons 'ontleed-woord (__toplevel_cons 'L ()))
                                                         (__toplevel_cons (__toplevel_cons 'ontleed-woord (__toplevel_cons 'N ())) ()))))
                                                ())))
                                       (__toplevel_cons
                                          (__toplevel_cons
                                             'define
                                             (__toplevel_cons
                                                (__toplevel_cons 'ontleed-naamwoord-vorm ())
                                                (__toplevel_cons
                                                   (__toplevel_cons
                                                      'define
                                                      (__toplevel_cons
                                                         (__toplevel_cons 'misschien (__toplevel_cons 'naamwoord-vorm ()))
                                                         (__toplevel_cons
                                                            (__toplevel_cons
                                                               'amb
                                                               (__toplevel_cons
                                                                  'naamwoord-vorm
                                                                  (__toplevel_cons
                                                                     (__toplevel_cons
                                                                        'misschien
                                                                        (__toplevel_cons
                                                                           (__toplevel_cons
                                                                              'list
                                                                              (__toplevel_cons
                                                                                 (__toplevel_cons 'quote (__toplevel_cons 'naamwoord-vorm ()))
                                                                                 (__toplevel_cons
                                                                                    'naamwoord-vorm
                                                                                    (__toplevel_cons (__toplevel_cons 'ontleed-voorzetsel-vorm ()) ()))))
                                                                           ()))
                                                                     ())))
                                                            ())))
                                                   (__toplevel_cons
                                                      (__toplevel_cons
                                                         'misschien
                                                         (__toplevel_cons (__toplevel_cons 'ontleed-eenvoudige-naamwoord-vorm ()) ()))
                                                      ()))))
                                          (__toplevel_cons
                                             (__toplevel_cons
                                                'define
                                                (__toplevel_cons
                                                   (__toplevel_cons 'ontleed-werkwoord-vorm ())
                                                   (__toplevel_cons
                                                      (__toplevel_cons
                                                         'define
                                                         (__toplevel_cons
                                                            (__toplevel_cons 'misschien (__toplevel_cons 'werkwoord-vorm ()))
                                                            (__toplevel_cons
                                                               (__toplevel_cons
                                                                  'amb
                                                                  (__toplevel_cons
                                                                     'werkwoord-vorm
                                                                     (__toplevel_cons
                                                                        (__toplevel_cons
                                                                           'misschien
                                                                           (__toplevel_cons
                                                                              (__toplevel_cons
                                                                                 'list
                                                                                 (__toplevel_cons
                                                                                    (__toplevel_cons 'quote (__toplevel_cons 'werkwoord-vorm ()))
                                                                                    (__toplevel_cons
                                                                                       'werkwoord-vorm
                                                                                       (__toplevel_cons (__toplevel_cons 'ontleed-voorzetsel-vorm ()) ()))))
                                                                              ()))
                                                                        ())))
                                                               ())))
                                                      (__toplevel_cons
                                                         (__toplevel_cons
                                                            'misschien
                                                            (__toplevel_cons (__toplevel_cons 'ontleed-woord (__toplevel_cons 'W ())) ()))
                                                         ()))))
                                             (__toplevel_cons
                                                (__toplevel_cons
                                                   'define
                                                   (__toplevel_cons
                                                      (__toplevel_cons 'ontleed-woord (__toplevel_cons 'woord-lijst ()))
                                                      (__toplevel_cons
                                                         (__toplevel_cons
                                                            'require
                                                            (__toplevel_cons
                                                               (__toplevel_cons
                                                                  'not
                                                                  (__toplevel_cons (__toplevel_cons 'null? (__toplevel_cons '*te-doen* ())) ()))
                                                               ()))
                                                         (__toplevel_cons
                                                            (__toplevel_cons
                                                               'require
                                                               (__toplevel_cons
                                                                  (__toplevel_cons
                                                                     'memq
                                                                     (__toplevel_cons
                                                                        (__toplevel_cons 'car (__toplevel_cons '*te-doen* ()))
                                                                        (__toplevel_cons (__toplevel_cons 'cdr (__toplevel_cons 'woord-lijst ())) ())))
                                                                  ()))
                                                            (__toplevel_cons
                                                               (__toplevel_cons
                                                                  'let
                                                                  (__toplevel_cons
                                                                     (__toplevel_cons
                                                                        (__toplevel_cons
                                                                           'gevonden
                                                                           (__toplevel_cons (__toplevel_cons 'car (__toplevel_cons '*te-doen* ())) ()))
                                                                        ())
                                                                     (__toplevel_cons
                                                                        (__toplevel_cons
                                                                           'set!
                                                                           (__toplevel_cons
                                                                              '*te-doen*
                                                                              (__toplevel_cons (__toplevel_cons 'cdr (__toplevel_cons '*te-doen* ())) ())))
                                                                        (__toplevel_cons
                                                                           (__toplevel_cons
                                                                              'list
                                                                              (__toplevel_cons
                                                                                 (__toplevel_cons 'car (__toplevel_cons 'woord-lijst ()))
                                                                                 (__toplevel_cons 'gevonden ())))
                                                                           ()))))
                                                               ())))))
                                                (__toplevel_cons
                                                   (__toplevel_cons
                                                      'define
                                                      (__toplevel_cons
                                                         (__toplevel_cons 'ontleed-voorzetsel-vorm ())
                                                         (__toplevel_cons
                                                            (__toplevel_cons
                                                               'list
                                                               (__toplevel_cons
                                                                  (__toplevel_cons 'quote (__toplevel_cons 'voorzetsel-vorm ()))
                                                                  (__toplevel_cons
                                                                     (__toplevel_cons 'ontleed-woord (__toplevel_cons 'V ()))
                                                                     (__toplevel_cons (__toplevel_cons 'ontleed-naamwoord-vorm ()) ()))))
                                                            ())))
                                                   (__toplevel_cons
                                                      (__toplevel_cons
                                                         'define
                                                         (__toplevel_cons '*te-doen* (__toplevel_cons (__toplevel_cons 'quote (__toplevel_cons () ())) ())))
                                                      (__toplevel_cons
                                                         (__toplevel_cons
                                                            'define
                                                            (__toplevel_cons
                                                               (__toplevel_cons 'ontleed (__toplevel_cons 'invoer ()))
                                                               (__toplevel_cons
                                                                  (__toplevel_cons 'set! (__toplevel_cons '*te-doen* (__toplevel_cons 'invoer ())))
                                                                  (__toplevel_cons
                                                                     (__toplevel_cons
                                                                        'let
                                                                        (__toplevel_cons
                                                                           (__toplevel_cons
                                                                              (__toplevel_cons 'gedaan (__toplevel_cons (__toplevel_cons 'ontleed-zin ()) ()))
                                                                              ())
                                                                           (__toplevel_cons
                                                                              (__toplevel_cons
                                                                                 'require
                                                                                 (__toplevel_cons (__toplevel_cons 'null? (__toplevel_cons '*te-doen* ())) ()))
                                                                              (__toplevel_cons 'gedaan ()))))
                                                                     ()))))
                                                         (__toplevel_cons
                                                            (__toplevel_cons
                                                               'ontleed
                                                               (__toplevel_cons
                                                                  (__toplevel_cons
                                                                     'quote
                                                                     (__toplevel_cons
                                                                        (__toplevel_cons
                                                                           'de
                                                                           (__toplevel_cons
                                                                              'kat
                                                                              (__toplevel_cons
                                                                                 'jaagt
                                                                                 (__toplevel_cons
                                                                                    'op
                                                                                    (__toplevel_cons
                                                                                       'de
                                                                                       (__toplevel_cons 'muis (__toplevel_cons 'in (__toplevel_cons 'het (__toplevel_cons 'huis ())))))))))
                                                                        ()))
                                                                  ()))
                                                            ()))))))))))))))))
         (next-alternative (lambda ()
                             #f))
         (try (lambda ()
                (ambeval
                   input
                   the-global-environment
                   (lambda (val next-alt)
                      (announce-output output-prompt)
                      (<change>
                         (user-print val)
                         ((lambda (x) x) (user-print val)))
                      (set! next-alternative next-alt))
                   (lambda ()
                      (announce-output ";;; There are no more values of")
                      (user-print input)
                      (set! next-alternative (lambda ()
                                             #f)))))))
   (try)
   (next-alternative)
   (next-alternative))