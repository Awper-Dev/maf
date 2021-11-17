; Changes:
; * removed: 2
; * added: 5
; * swaps: 3
; * negated predicates: 0
; * swapped branches: 3
; * calls to id fun: 10
(letrec ((result ())
         (output (lambda (i)
                   (set! result (cons i result))))
         (linebreak (lambda ()
                      (set! result (cons 'linebreak result))))
         (input (__toplevel_cons
                  (__toplevel_cons
                     'define
                     (__toplevel_cons
                        (__toplevel_cons 'fac (__toplevel_cons 'x ()))
                        (__toplevel_cons
                           (__toplevel_cons
                              'if
                              (__toplevel_cons
                                 (__toplevel_cons '= (__toplevel_cons 'x (__toplevel_cons 0 ())))
                                 (__toplevel_cons
                                    1
                                    (__toplevel_cons
                                       (__toplevel_cons
                                          '*
                                          (__toplevel_cons
                                             'x
                                             (__toplevel_cons
                                                (__toplevel_cons
                                                   'fac
                                                   (__toplevel_cons (__toplevel_cons '- (__toplevel_cons 'x (__toplevel_cons 1 ()))) ()))
                                                ())))
                                       ()))))
                           ())))
                  (__toplevel_cons (__toplevel_cons 'fac (__toplevel_cons 6 ())) ())))
         (read (lambda ()
                 (if (null? input)
                    ()
                    (let ((next (car input)))
                       (set! input (cdr input))
                       next))))
         (true #t)
         (false #f)
         (apply-in-underlying-scheme (lambda (op args)
                                       (if (null? args)
                                          (op)
                                          (if (null? (cdr args))
                                             (op (car args))
                                             (if (null? (cddr args))
                                                (op (car args) (cadr args))
                                                (error "apply"))))))
         (true? (lambda (x)
                  (not (eq? x false))))
         (self-evaluating? (lambda (exp)
                             (<change>
                                ()
                                true)
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
                         (cadr exp)))
         (if-consequent (lambda (exp)
                          (caddr exp)))
         (if-alternative (lambda (exp)
                           (if (not (null? (cdddr exp)))
                              (cadddr exp)
                              'false)))
         (lambda? (lambda (exp)
                    (tagged-list? exp 'lambda)))
         (lambda-parameters (lambda (exp)
                              (cadr exp)))
         (lambda-body (lambda (exp)
                        (cddr exp)))
         (make-lambda (lambda (parameters body)
                        (cons 'lambda (cons parameters body))))
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
                                     (error "Too many arguments supplied" vars vals)
                                     (error "Too few arguments supplied" vars vals)))))
         (make-frame (lambda (variables values)
                       (cons variables values)))
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
                                                                        (if (null? vars)
                                                                           (env-loop (enclosing-environment env))
                                                                           (if (eq? var (car vars))
                                                                              (car vals)
                                                                              (scan (cdr vars) (cdr vals)))))))
                                                          (if (eq? env the-empty-environment)
                                                             (error "Unbound variable" var)
                                                             (let ((frame (first-frame env)))
                                                                (<change>
                                                                   (scan (frame-variables frame) (frame-values frame))
                                                                   ((lambda (x) x) (scan (frame-variables frame) (frame-values frame))))))))))
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
                                                           (error "Unbound variable -- SET!" var)
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
                              (<change>
                                 ()
                                 true)
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
                                 (list '+ +)
                                 (list '* *)
                                 (list '= =)
                                 (list '- -)
                                 (list '< <)
                                 (list '> >)))
         (primitive-procedure-names (lambda ()
                                      (map car primitive-procedures)))
         (primitive-procedure-objects (lambda ()
                                        (map (lambda (proc) (list 'primitive (cadr proc))) primitive-procedures)))
         (apply-primitive-procedure (lambda (proc args)
                                      (apply-in-underlying-scheme (primitive-implementation proc) args)))
         (input-prompt ";;; M-Eval input:")
         (output-prompt ";;; M-Eval value:")
         (prompt-for-input (lambda (string)
                             (linebreak)
                             (linebreak)
                             (output string)
                             (linebreak)))
         (announce-output (lambda (string)
                            (linebreak)
                            (<change>
                               (output string)
                               (linebreak))
                            (<change>
                               (linebreak)
                               (output string))))
         (user-print (lambda (object)
                       (if (compound-procedure? object)
                          (output
                             (list 'compound-procedure (procedure-parameters object) (procedure-body object) '<procedure-env>))
                          (output object))))
         (the-global-environment (setup-environment))
         (make-machine (lambda (register-names ops controller-text)
                         (let ((machine (make-new-machine)))
                            (<change>
                               (for-each (lambda (register-name) ((machine 'allocate-register) register-name)) register-names)
                               ((lambda (x) x)
                                  (for-each (lambda (register-name) ((machine 'allocate-register) register-name)) register-names)))
                            (<change>
                               ((machine 'install-operations) ops)
                               ())
                            (<change>
                               ((machine 'install-instruction-sequence) (assemble controller-text machine))
                               ())
                            machine)))
         (make-register (lambda (name)
                          (let ((contents '*unassigned*))
                             (<change>
                                (letrec ((dispatch (lambda (message)
                                                     (if (eq? message 'get)
                                                        contents
                                                        (if (eq? message 'set)
                                                           (lambda (value)
                                                              (set! contents value))
                                                           (error "Unknown request -- REGISTER" message))))))
                                   dispatch)
                                ((lambda (x) x)
                                   (letrec ((dispatch (lambda (message)
                                                        (if (eq? message 'get)
                                                           contents
                                                           (if (eq? message 'set)
                                                              (lambda (value)
                                                                 (set! contents value))
                                                              (error "Unknown request -- REGISTER" message))))))
                                      dispatch))))))
         (get-contents (lambda (register)
                         (register 'get)))
         (set-contents! (lambda (register value)
                          ((register 'set) value)))
         (empty-arglist (lambda ()
                          ()))
         (adjoin-arg (lambda (arg arglist)
                       (append arglist (list arg))))
         (last-operand? (lambda (ops)
                          (null? (cdr ops))))
         (no-more-exps? (lambda (seq)
                          (null? seq)))
         (get-global-environment (lambda ()
                                   the-global-environment))
         (make-compiled-procedure (lambda (entry env)
                                    (list 'compiled-procedure entry env)))
         (compiled-procedure? (lambda (proc)
                                (tagged-list? proc 'compiled-procedure)))
         (compiled-procedure-entry (lambda (c-proc)
                                     (cadr c-proc)))
         (compiled-procedure-env (lambda (c-proc)
                                   (caddr c-proc)))
         (pop (lambda (stack)
                (stack 'pop)))
         (push (lambda (stack value)
                 ((stack 'push) value)))
         (make-stack (lambda ()
                       (let ((s ())
                             (number-pushes 0)
                             (max-depth 0)
                             (current-depth 0))
                          (letrec ((push (lambda (x)
                                           (set! s (cons x s))
                                           (set! number-pushes (+ 1 number-pushes))
                                           (<change>
                                              ()
                                              s)
                                           (set! current-depth (+ 1 current-depth))
                                           (set! max-depth (max current-depth max-depth))))
                                   (pop (lambda ()
                                          (if (null? s)
                                             (error "Empty stack -- POP")
                                             (let ((top (car s)))
                                                (<change>
                                                   ()
                                                   (cdr s))
                                                (<change>
                                                   (set! s (cdr s))
                                                   ((lambda (x) x) (set! s (cdr s))))
                                                (set! current-depth (- current-depth 1))
                                                top))))
                                   (initialize (lambda ()
                                                 (set! s ())
                                                 (set! number-pushes 0)
                                                 (set! max-depth 0)
                                                 (set! current-depth 0)
                                                 'done))
                                   (print-statistics (lambda ()
                                                       (linebreak)
                                                       (<change>
                                                          ()
                                                          'total-pushes)
                                                       (output (list 'total-pushes '= number-pushes 'maximum-depth '= max-depth))))
                                   (dispatch (lambda (message)
                                               (<change>
                                                  (if (eq? message 'push)
                                                     push
                                                     (if (eq? message 'pop)
                                                        (pop)
                                                        (if (eq? message 'initialize)
                                                           (initialize)
                                                           (if (eq? message 'print-statistics)
                                                              (print-statistics)
                                                              (error "Unknown request -- STACK" message)))))
                                                  ((lambda (x) x)
                                                     (if (eq? message 'push)
                                                        push
                                                        (if (eq? message 'pop)
                                                           (pop)
                                                           (if (eq? message 'initialize)
                                                              (initialize)
                                                              (if (eq? message 'print-statistics)
                                                                 (print-statistics)
                                                                 (error "Unknown request -- STACK" message))))))))))
                             dispatch))))
         (make-new-machine (lambda ()
                             (let ((pc (make-register 'pc))
                                   (flag (make-register 'flag))
                                   (stack (make-stack))
                                   (the-instruction-sequence ()))
                                (let ((the-ops (list
                                                 (list 'initialize-stack (lambda () (stack 'initialize)))
                                                 (list 'print-stack-statistics (lambda () (stack 'print-statistics)))))
                                      (register-table (list (list 'pc pc) (list 'flag flag))))
                                   (letrec ((allocate-register (lambda (name)
                                                                 (<change>
                                                                    (if (assoc name register-table)
                                                                       (error "Multiply defined register: " name)
                                                                       (set! register-table (cons (list name (make-register name)) register-table)))
                                                                    'register-allocated)
                                                                 (<change>
                                                                    'register-allocated
                                                                    (if (assoc name register-table)
                                                                       (error "Multiply defined register: " name)
                                                                       (set! register-table (cons (list name (make-register name)) register-table))))))
                                            (lookup-register (lambda (name)
                                                               (let ((val (assoc name register-table)))
                                                                  (if val
                                                                     (cadr val)
                                                                     (error "Unknown register:" name)))))
                                            (execute (lambda ()
                                                       (let ((insts (get-contents pc)))
                                                          (if (null? insts)
                                                             'done
                                                             (begin
                                                                ((instruction-execution-proc (car insts)))
                                                                (execute))))))
                                            (dispatch (lambda (message)
                                                        (if (eq? message 'start)
                                                           (begin
                                                              (set-contents! pc the-instruction-sequence)
                                                              (execute))
                                                           (if (eq? message 'install-instruction-sequence)
                                                              (lambda (seq)
                                                                 (set! the-instruction-sequence seq))
                                                              (if (eq? message 'allocate-register)
                                                                 allocate-register
                                                                 (if (eq? message 'get-register)
                                                                    lookup-register
                                                                    (if (eq? message 'install-operations)
                                                                       (<change>
                                                                          (lambda (ops)
                                                                             (set! the-ops (append the-ops ops)))
                                                                          (if (eq? message 'stack)
                                                                             stack
                                                                             (if (eq? message 'operations)
                                                                                the-ops
                                                                                (error "Unknown request -- MACHINE" message))))
                                                                       (<change>
                                                                          (if (eq? message 'stack)
                                                                             stack
                                                                             (if (eq? message 'operations)
                                                                                the-ops
                                                                                (error "Unknown request -- MACHINE" message)))
                                                                          (lambda (ops)
                                                                             (set! the-ops (append the-ops ops))))))))))))
                                      dispatch)))))
         (start (lambda (machine)
                  (machine 'start)))
         (get-register-contents (lambda (machine register-name)
                                  (get-contents (get-register machine register-name))))
         (set-register-contents! (lambda (machine register-name value)
                                   (set-contents! (get-register machine register-name) value)
                                   'done))
         (get-register (lambda (machine reg-name)
                         ((machine 'get-register) reg-name)))
         (assemble (lambda (controller-text machine)
                     (extract-labels controller-text (lambda (insts labels) (update-insts! insts labels machine) insts))))
         (extract-labels (lambda (text receive)
                           (if (null? text)
                              (receive () ())
                              (extract-labels
                                 (cdr text)
                                 (lambda (insts labels)
                                    (let ((next-inst (car text)))
                                       (if (symbol? next-inst)
                                          (receive insts (cons (make-label-entry next-inst insts) labels))
                                          (receive (cons (make-instruction next-inst) insts) labels))))))))
         (update-insts! (lambda (insts labels machine)
                          (let ((pc (get-register machine 'pc))
                                (flag (get-register machine 'flag))
                                (stack (machine 'stack))
                                (ops (machine 'operations)))
                             (for-each
                                (lambda (inst)
                                   (set-instruction-execution-proc!
                                      inst
                                      (make-execution-procedure (instruction-text inst) labels machine pc flag stack ops)))
                                insts))))
         (make-instruction (lambda (text)
                             (cons text ())))
         (instruction-text (lambda (inst)
                             (car inst)))
         (instruction-execution-proc (lambda (inst)
                                       (cdr inst)))
         (set-instruction-execution-proc! (lambda (inst proc)
                                            (set-cdr! inst proc)))
         (make-label-entry (lambda (label-name insts)
                             (cons label-name insts)))
         (lookup-label (lambda (labels label-name)
                         (let ((val (assoc label-name labels)))
                            (if val
                               (cdr val)
                               (error "Undefined label -- ASSEMBLE" label-name)))))
         (make-execution-procedure (lambda (inst labels machine pc flag stack ops)
                                     (if (eq? (car inst) 'assign)
                                        (make-assign inst machine labels ops pc)
                                        (if (eq? (car inst) 'test)
                                           (make-test inst machine labels ops flag pc)
                                           (if (eq? (car inst) 'branch)
                                              (make-branch inst machine labels flag pc)
                                              (if (eq? (car inst) 'goto)
                                                 (make-goto inst machine labels pc)
                                                 (if (eq? (car inst) 'save)
                                                    (make-save inst machine stack pc)
                                                    (if (eq? (car inst) 'restore)
                                                       (make-restore inst machine stack pc)
                                                       (if (eq? (car inst) 'perform)
                                                          (make-perform inst machine labels ops pc)
                                                          (error "Unknown instruction type -- ASSEMBLE" inst))))))))))
         (make-assign (lambda (inst machine labels operations pc)
                        (let ((target (get-register machine (assign-reg-name inst)))
                              (value-exp (assign-value-exp inst)))
                           (let ((value-proc (if (operation-exp? value-exp)
                                               (make-operation-exp value-exp machine labels operations)
                                               (make-primitive-exp (car value-exp) machine labels))))
                              (lambda ()
                                 (<change>
                                    (set-contents! target (value-proc))
                                    ((lambda (x) x) (set-contents! target (value-proc))))
                                 (advance-pc pc))))))
         (assign-reg-name (lambda (assign-instruction)
                            (cadr assign-instruction)))
         (assign-value-exp (lambda (assign-instruction)
                             (cddr assign-instruction)))
         (advance-pc (lambda (pc)
                       (set-contents! pc (cdr (get-contents pc)))))
         (make-test (lambda (inst machine labels operations flag pc)
                      (let ((condition (test-condition inst)))
                         (if (operation-exp? condition)
                            (let ((condition-proc (make-operation-exp condition machine labels operations)))
                               (lambda ()
                                  (set-contents! flag (condition-proc))
                                  (advance-pc pc)))
                            (error "Bad TEST instruction -- ASSEMBLE" inst)))))
         (test-condition (lambda (test-instruction)
                           (cdr test-instruction)))
         (make-branch (lambda (inst machine labels flag pc)
                        (<change>
                           (let ((dest (branch-dest inst)))
                              (if (label-exp? dest)
                                 (let ((insts (lookup-label labels (label-exp-label dest))))
                                    (lambda ()
                                       (if (get-contents flag)
                                          (set-contents! pc insts)
                                          (advance-pc pc))))
                                 (error "Bad BRANCH instruction -- ASSEMBLE" inst)))
                           ((lambda (x) x)
                              (let ((dest (branch-dest inst)))
                                 (if (label-exp? dest)
                                    (let ((insts (lookup-label labels (label-exp-label dest))))
                                       (lambda ()
                                          (if (get-contents flag)
                                             (set-contents! pc insts)
                                             (advance-pc pc))))
                                    (error "Bad BRANCH instruction -- ASSEMBLE" inst)))))))
         (branch-dest (lambda (branch-instruction)
                        (cadr branch-instruction)))
         (make-goto (lambda (inst machine labels pc)
                      (let ((dest (goto-dest inst)))
                         (if (label-exp? dest)
                            (let ((insts (lookup-label labels (label-exp-label dest))))
                               (lambda ()
                                  (set-contents! pc insts)))
                            (if (register-exp? dest)
                               (let ((reg (get-register machine (register-exp-reg dest))))
                                  (lambda ()
                                     (<change>
                                        (set-contents! pc (get-contents reg))
                                        ((lambda (x) x) (set-contents! pc (get-contents reg))))))
                               (error "Bad GOTO instruction -- ASSEMBLE" inst))))))
         (goto-dest (lambda (goto-instruction)
                      (<change>
                         (cadr goto-instruction)
                         ((lambda (x) x) (cadr goto-instruction)))))
         (make-save (lambda (inst machine stack pc)
                      (let ((reg (get-register machine (stack-inst-reg-name inst))))
                         (lambda ()
                            (push stack (get-contents reg))
                            (advance-pc pc)))))
         (make-restore (lambda (inst machine stack pc)
                         (let ((reg (get-register machine (stack-inst-reg-name inst))))
                            (lambda ()
                               (set-contents! reg (pop stack))
                               (advance-pc pc)))))
         (stack-inst-reg-name (lambda (stack-instruction)
                                (cadr stack-instruction)))
         (make-perform (lambda (inst machine labels operations pc)
                         (let ((action (perform-action inst)))
                            (if (operation-exp? action)
                               (let ((action-proc (make-operation-exp action machine labels operations)))
                                  (lambda ()
                                     (action-proc)
                                     (advance-pc pc)))
                               (error "Bad PERFORM instruction -- ASSEMBLE" inst)))))
         (perform-action (lambda (inst)
                           (<change>
                              (cdr inst)
                              ((lambda (x) x) (cdr inst)))))
         (make-primitive-exp (lambda (exp machine labels)
                               (if (constant-exp? exp)
                                  (let ((c (constant-exp-value exp)))
                                     (lambda ()
                                        c))
                                  (if (label-exp? exp)
                                     (let ((insts (lookup-label labels (label-exp-label exp))))
                                        (lambda ()
                                           insts))
                                     (if (register-exp? exp)
                                        (let ((r (get-register machine (register-exp-reg exp))))
                                           (lambda ()
                                              (get-contents r)))
                                        (error "Unknown expression type -- ASSEMBLE" exp))))))
         (register-exp? (lambda (exp)
                          (tagged-list? exp 'reg)))
         (register-exp-reg (lambda (exp)
                             (cadr exp)))
         (constant-exp? (lambda (exp)
                          (tagged-list? exp 'const)))
         (constant-exp-value (lambda (exp)
                               (cadr exp)))
         (label-exp? (lambda (exp)
                       (tagged-list? exp 'label)))
         (label-exp-label (lambda (exp)
                            (cadr exp)))
         (make-operation-exp (lambda (exp machine labels operations)
                               (let ((op (lookup-prim (operation-exp-op exp) operations))
                                     (aprocs (map (lambda (e) (make-primitive-exp e machine labels)) (operation-exp-operands exp))))
                                  (lambda ()
                                     (apply op (map (lambda (p) (p)) aprocs))))))
         (operation-exp? (lambda (exp)
                           (if (pair? exp)
                              (<change>
                                 (tagged-list? (car exp) 'op)
                                 #f)
                              (<change>
                                 #f
                                 (tagged-list? (car exp) 'op)))))
         (operation-exp-op (lambda (operation-exp)
                             (cadr (car operation-exp))))
         (operation-exp-operands (lambda (operation-exp)
                                   (cdr operation-exp)))
         (lookup-prim (lambda (symbol operations)
                        (let ((val (assoc symbol operations)))
                           (if val
                              (<change>
                                 (cadr val)
                                 (error "Unknown operation -- ASSEMBLE" symbol))
                              (<change>
                                 (error "Unknown operation -- ASSEMBLE" symbol)
                                 (cadr val))))))
         (eceval-operations (list
                              (list 'read read)
                              (list 'null? null?)
                              (list 'self-evaluating? self-evaluating?)
                              (list 'quoted? quoted?)
                              (list 'text-of-quotation text-of-quotation)
                              (list 'variable? variable?)
                              (list 'assignment? assignment?)
                              (list 'assignment-variable assignment-variable)
                              (list 'assignment-value assignment-value)
                              (list 'definition? definition?)
                              (list 'definition-variable definition-variable)
                              (list 'definition-value definition-value)
                              (list 'lambda? lambda?)
                              (list 'lambda-parameters lambda-parameters)
                              (list 'lambda-body lambda-body)
                              (list 'if? if?)
                              (list 'if-predicate if-predicate)
                              (list 'if-consequent if-consequent)
                              (list 'if-alternative if-alternative)
                              (list 'begin? begin?)
                              (list 'begin-actions begin-actions)
                              (list 'last-exp? last-exp?)
                              (list 'first-exp first-exp)
                              (list 'rest-exps rest-exps)
                              (list 'application? application?)
                              (list 'operator operator)
                              (list 'operands operands)
                              (list 'no-operands? no-operands?)
                              (list 'first-operand first-operand)
                              (list 'rest-operands rest-operands)
                              (list 'true? true?)
                              (list 'make-procedure make-procedure)
                              (list 'compound-procedure? compound-procedure?)
                              (list 'procedure-parameters procedure-parameters)
                              (list 'procedure-body procedure-body)
                              (list 'procedure-environment procedure-environment)
                              (list 'extend-environment extend-environment)
                              (list 'lookup-variable-value lookup-variable-value)
                              (list 'set-variable-value! set-variable-value!)
                              (list 'define-variable! define-variable!)
                              (list 'primitive-procedure? primitive-procedure?)
                              (list 'apply-primitive-procedure apply-primitive-procedure)
                              (list 'prompt-for-input prompt-for-input)
                              (list 'announce-output announce-output)
                              (list 'user-print user-print)
                              (list 'empty-arglist empty-arglist)
                              (list 'adjoin-arg adjoin-arg)
                              (list 'last-operand? last-operand?)
                              (list 'no-more-exps? no-more-exps?)
                              (list 'get-global-environment get-global-environment)))
         (eceval (make-machine
                   (__toplevel_cons
                      'exp
                      (__toplevel_cons
                         'env
                         (__toplevel_cons
                            'val
                            (__toplevel_cons
                               'proc
                               (__toplevel_cons 'argl (__toplevel_cons 'continue (__toplevel_cons 'unev ())))))))
                   eceval-operations
                   (__toplevel_cons
                      'read-eval-print-loop
                      (__toplevel_cons
                         (__toplevel_cons
                            'perform
                            (__toplevel_cons (__toplevel_cons 'op (__toplevel_cons 'initialize-stack ())) ()))
                         (__toplevel_cons
                            (__toplevel_cons
                               'perform
                               (__toplevel_cons
                                  (__toplevel_cons 'op (__toplevel_cons 'prompt-for-input ()))
                                  (__toplevel_cons (__toplevel_cons 'const (__toplevel_cons ";;; EC-Eval input:" ())) ())))
                            (__toplevel_cons
                               (__toplevel_cons
                                  'assign
                                  (__toplevel_cons 'exp (__toplevel_cons (__toplevel_cons 'op (__toplevel_cons 'read ())) ())))
                               (__toplevel_cons
                                  (__toplevel_cons
                                     'test
                                     (__toplevel_cons
                                        (__toplevel_cons 'op (__toplevel_cons 'null? ()))
                                        (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                  (__toplevel_cons
                                     (__toplevel_cons 'branch (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'end ())) ()))
                                     (__toplevel_cons
                                        (__toplevel_cons
                                           'assign
                                           (__toplevel_cons
                                              'env
                                              (__toplevel_cons (__toplevel_cons 'op (__toplevel_cons 'get-global-environment ())) ())))
                                        (__toplevel_cons
                                           (__toplevel_cons
                                              'assign
                                              (__toplevel_cons
                                                 'continue
                                                 (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'print-result ())) ())))
                                           (__toplevel_cons
                                              (__toplevel_cons
                                                 'goto
                                                 (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                              (__toplevel_cons
                                                 'print-result
                                                 (__toplevel_cons
                                                    (__toplevel_cons
                                                       'perform
                                                       (__toplevel_cons (__toplevel_cons 'op (__toplevel_cons 'print-stack-statistics ())) ()))
                                                    (__toplevel_cons
                                                       (__toplevel_cons
                                                          'perform
                                                          (__toplevel_cons
                                                             (__toplevel_cons 'op (__toplevel_cons 'announce-output ()))
                                                             (__toplevel_cons (__toplevel_cons 'const (__toplevel_cons ";;; EC-Eval value:" ())) ())))
                                                       (__toplevel_cons
                                                          (__toplevel_cons
                                                             'perform
                                                             (__toplevel_cons
                                                                (__toplevel_cons 'op (__toplevel_cons 'user-print ()))
                                                                (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'val ())) ())))
                                                          (__toplevel_cons
                                                             (__toplevel_cons
                                                                'goto
                                                                (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'read-eval-print-loop ())) ()))
                                                             (__toplevel_cons
                                                                'unknown-expression-type
                                                                (__toplevel_cons
                                                                   (__toplevel_cons
                                                                      'assign
                                                                      (__toplevel_cons
                                                                         'val
                                                                         (__toplevel_cons (__toplevel_cons 'const (__toplevel_cons 'unknown-expression-type-error ())) ())))
                                                                   (__toplevel_cons
                                                                      (__toplevel_cons
                                                                         'goto
                                                                         (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'signal-error ())) ()))
                                                                      (__toplevel_cons
                                                                         'unknown-procedure-type
                                                                         (__toplevel_cons
                                                                            (__toplevel_cons 'restore (__toplevel_cons 'continue ()))
                                                                            (__toplevel_cons
                                                                               (__toplevel_cons
                                                                                  'assign
                                                                                  (__toplevel_cons
                                                                                     'val
                                                                                     (__toplevel_cons (__toplevel_cons 'const (__toplevel_cons 'unknown-procedure-type-error ())) ())))
                                                                               (__toplevel_cons
                                                                                  (__toplevel_cons
                                                                                     'goto
                                                                                     (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'signal-error ())) ()))
                                                                                  (__toplevel_cons
                                                                                     'signal-error
                                                                                     (__toplevel_cons
                                                                                        (__toplevel_cons
                                                                                           'perform
                                                                                           (__toplevel_cons
                                                                                              (__toplevel_cons 'op (__toplevel_cons 'user-print ()))
                                                                                              (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'val ())) ())))
                                                                                        (__toplevel_cons
                                                                                           (__toplevel_cons
                                                                                              'goto
                                                                                              (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'read-eval-print-loop ())) ()))
                                                                                           (__toplevel_cons
                                                                                              'eval-dispatch
                                                                                              (__toplevel_cons
                                                                                                 (__toplevel_cons
                                                                                                    'test
                                                                                                    (__toplevel_cons
                                                                                                       (__toplevel_cons 'op (__toplevel_cons 'self-evaluating? ()))
                                                                                                       (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                 (__toplevel_cons
                                                                                                    (__toplevel_cons
                                                                                                       'branch
                                                                                                       (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-self-eval ())) ()))
                                                                                                    (__toplevel_cons
                                                                                                       (__toplevel_cons
                                                                                                          'test
                                                                                                          (__toplevel_cons
                                                                                                             (__toplevel_cons 'op (__toplevel_cons 'variable? ()))
                                                                                                             (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                       (__toplevel_cons
                                                                                                          (__toplevel_cons
                                                                                                             'branch
                                                                                                             (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-variable ())) ()))
                                                                                                          (__toplevel_cons
                                                                                                             (__toplevel_cons
                                                                                                                'test
                                                                                                                (__toplevel_cons
                                                                                                                   (__toplevel_cons 'op (__toplevel_cons 'quoted? ()))
                                                                                                                   (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                             (__toplevel_cons
                                                                                                                (__toplevel_cons
                                                                                                                   'branch
                                                                                                                   (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-quoted ())) ()))
                                                                                                                (__toplevel_cons
                                                                                                                   (__toplevel_cons
                                                                                                                      'test
                                                                                                                      (__toplevel_cons
                                                                                                                         (__toplevel_cons 'op (__toplevel_cons 'assignment? ()))
                                                                                                                         (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                                   (__toplevel_cons
                                                                                                                      (__toplevel_cons
                                                                                                                         'branch
                                                                                                                         (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-assignment ())) ()))
                                                                                                                      (__toplevel_cons
                                                                                                                         (__toplevel_cons
                                                                                                                            'test
                                                                                                                            (__toplevel_cons
                                                                                                                               (__toplevel_cons 'op (__toplevel_cons 'definition? ()))
                                                                                                                               (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                                         (__toplevel_cons
                                                                                                                            (__toplevel_cons
                                                                                                                               'branch
                                                                                                                               (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-definition ())) ()))
                                                                                                                            (__toplevel_cons
                                                                                                                               (__toplevel_cons
                                                                                                                                  'test
                                                                                                                                  (__toplevel_cons
                                                                                                                                     (__toplevel_cons 'op (__toplevel_cons 'if? ()))
                                                                                                                                     (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                                               (__toplevel_cons
                                                                                                                                  (__toplevel_cons 'branch (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-if ())) ()))
                                                                                                                                  (__toplevel_cons
                                                                                                                                     (__toplevel_cons
                                                                                                                                        'test
                                                                                                                                        (__toplevel_cons
                                                                                                                                           (__toplevel_cons 'op (__toplevel_cons 'lambda? ()))
                                                                                                                                           (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                                                     (__toplevel_cons
                                                                                                                                        (__toplevel_cons
                                                                                                                                           'branch
                                                                                                                                           (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-lambda ())) ()))
                                                                                                                                        (__toplevel_cons
                                                                                                                                           (__toplevel_cons
                                                                                                                                              'test
                                                                                                                                              (__toplevel_cons
                                                                                                                                                 (__toplevel_cons 'op (__toplevel_cons 'begin? ()))
                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                                                           (__toplevel_cons
                                                                                                                                              (__toplevel_cons
                                                                                                                                                 'branch
                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-begin ())) ()))
                                                                                                                                              (__toplevel_cons
                                                                                                                                                 (__toplevel_cons
                                                                                                                                                    'test
                                                                                                                                                    (__toplevel_cons
                                                                                                                                                       (__toplevel_cons 'op (__toplevel_cons 'application? ()))
                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                                                                 (__toplevel_cons
                                                                                                                                                    (__toplevel_cons
                                                                                                                                                       'branch
                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-application ())) ()))
                                                                                                                                                    (__toplevel_cons
                                                                                                                                                       (__toplevel_cons
                                                                                                                                                          'goto
                                                                                                                                                          (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'unknown-expression-type ())) ()))
                                                                                                                                                       (__toplevel_cons
                                                                                                                                                          'ev-self-eval
                                                                                                                                                          (__toplevel_cons
                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                'assign
                                                                                                                                                                (__toplevel_cons 'val (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ())))
                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                (__toplevel_cons 'goto (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'continue ())) ()))
                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                   'ev-variable
                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                         'assign
                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                            'val
                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                               (__toplevel_cons 'op (__toplevel_cons 'lookup-variable-value ()))
                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                  (__toplevel_cons 'reg (__toplevel_cons 'exp ()))
                                                                                                                                                                                  (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'env ())) ())))))
                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                         (__toplevel_cons 'goto (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'continue ())) ()))
                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                            'ev-quoted
                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                  'assign
                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                     'val
                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                        (__toplevel_cons 'op (__toplevel_cons 'text-of-quotation ()))
                                                                                                                                                                                        (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                  (__toplevel_cons 'goto (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'continue ())) ()))
                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                     'ev-lambda
                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                           'assign
                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                              'unev
                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                 (__toplevel_cons 'op (__toplevel_cons 'lambda-parameters ()))
                                                                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                              'assign
                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                 'exp
                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                    (__toplevel_cons 'op (__toplevel_cons 'lambda-body ()))
                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                 'assign
                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                    'val
                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                       (__toplevel_cons 'op (__toplevel_cons 'make-procedure ()))
                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                          (__toplevel_cons 'reg (__toplevel_cons 'unev ()))
                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                             (__toplevel_cons 'reg (__toplevel_cons 'exp ()))
                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'env ())) ()))))))
                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                 (__toplevel_cons 'goto (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'continue ())) ()))
                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                    'ev-application
                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                       (__toplevel_cons 'save (__toplevel_cons 'continue ()))
                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                          (__toplevel_cons 'save (__toplevel_cons 'env ()))
                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                'assign
                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                   'unev
                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                      (__toplevel_cons 'op (__toplevel_cons 'operands ()))
                                                                                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                (__toplevel_cons 'save (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                      'assign
                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                         'exp
                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                            (__toplevel_cons 'op (__toplevel_cons 'operator ()))
                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                         'assign
                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                            'continue
                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-appl-did-operator ())) ())))
                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                            'goto
                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                            'ev-appl-did-operator
                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                               (__toplevel_cons 'restore (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                  (__toplevel_cons 'restore (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                        'assign
                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                           'argl
                                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'op (__toplevel_cons 'empty-arglist ())) ())))
                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                           'assign
                                                                                                                                                                                                                                           (__toplevel_cons 'proc (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'val ())) ())))
                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                              'test
                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                 (__toplevel_cons 'op (__toplevel_cons 'no-operands? ()))
                                                                                                                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'unev ())) ())))
                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                 'branch
                                                                                                                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'apply-dispatch ())) ()))
                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                 (__toplevel_cons 'save (__toplevel_cons 'proc ()))
                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                    'ev-appl-operand-loop
                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                       (__toplevel_cons 'save (__toplevel_cons 'argl ()))
                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                             'assign
                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                'exp
                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                   (__toplevel_cons 'op (__toplevel_cons 'first-operand ()))
                                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'unev ())) ()))))
                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                'test
                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                   (__toplevel_cons 'op (__toplevel_cons 'last-operand? ()))
                                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'unev ())) ())))
                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                   'branch
                                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-appl-last-arg ())) ()))
                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                   (__toplevel_cons 'save (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                      (__toplevel_cons 'save (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                            'assign
                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                               'continue
                                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-appl-accumulate-arg ())) ())))
                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                               'goto
                                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                               'ev-appl-accumulate-arg
                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                  (__toplevel_cons 'restore (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                     (__toplevel_cons 'restore (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                        (__toplevel_cons 'restore (__toplevel_cons 'argl ()))
                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                              'assign
                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                 'argl
                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'op (__toplevel_cons 'adjoin-arg ()))
                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                       (__toplevel_cons 'reg (__toplevel_cons 'val ()))
                                                                                                                                                                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'argl ())) ())))))
                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                 'assign
                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                    'unev
                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                       (__toplevel_cons 'op (__toplevel_cons 'rest-operands ()))
                                                                                                                                                                                                                                                                                                       (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'unev ())) ()))))
                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                    'goto
                                                                                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-appl-operand-loop ())) ()))
                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                    'ev-appl-last-arg
                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                          'assign
                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                             'continue
                                                                                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-appl-accum-last-arg ())) ())))
                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                             'goto
                                                                                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                             'ev-appl-accum-last-arg
                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'restore (__toplevel_cons 'argl ()))
                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                      'assign
                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                         'argl
                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'op (__toplevel_cons 'adjoin-arg ()))
                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'reg (__toplevel_cons 'val ()))
                                                                                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'argl ())) ())))))
                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                      (__toplevel_cons 'restore (__toplevel_cons 'proc ()))
                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                            'goto
                                                                                                                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'apply-dispatch ())) ()))
                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                            'apply-dispatch
                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                  'test
                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons 'op (__toplevel_cons 'primitive-procedure? ()))
                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'proc ())) ())))
                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                     'branch
                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'primitive-apply ())) ()))
                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                        'test
                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons 'op (__toplevel_cons 'compound-procedure? ()))
                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'proc ())) ())))
                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                           'branch
                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'compound-apply ())) ()))
                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                              'goto
                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'unknown-procedure-type ())) ()))
                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                              'primitive-apply
                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                    'assign
                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                       'val
                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons 'op (__toplevel_cons 'apply-primitive-procedure ()))
                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons 'reg (__toplevel_cons 'proc ()))
                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'argl ())) ())))))
                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'restore (__toplevel_cons 'continue ()))
                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons 'goto (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'continue ())) ()))
                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                          'compound-apply
                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                'assign
                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                   'unev
                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons 'op (__toplevel_cons 'procedure-parameters ()))
                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'proc ())) ()))))
                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                   'assign
                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                      'env
                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons 'op (__toplevel_cons 'procedure-environment ()))
                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'proc ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                      'assign
                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                         'env
                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'op (__toplevel_cons 'extend-environment ()))
                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'reg (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'reg (__toplevel_cons 'argl ()))
                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'env ())) ()))))))
                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                         'assign
                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                            'unev
                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'op (__toplevel_cons 'procedure-body ()))
                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'proc ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                            'goto
                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-sequence ())) ()))
                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                            'ev-begin
                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                  'assign
                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                     'unev
                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons 'op (__toplevel_cons 'begin-actions ()))
                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'save (__toplevel_cons 'continue ()))
                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                        'goto
                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-sequence ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                        'ev-sequence
                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                              'assign
                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                 'exp
                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'op (__toplevel_cons 'first-exp ()))
                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'unev ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                 'test
                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'op (__toplevel_cons 'last-exp? ()))
                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'unev ())) ())))
                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                    'branch
                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-sequence-last-exp ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'save (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons 'save (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                             'assign
                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                'continue
                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-sequence-continue ())) ())))
                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                'goto
                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                'ev-sequence-continue
                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons 'restore (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons 'restore (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                            'assign
                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                               'unev
                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'op (__toplevel_cons 'rest-exps ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'unev ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                               'goto
                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-sequence ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                               'ev-sequence-last-exp
                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'restore (__toplevel_cons 'continue ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                        'goto
                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                        'ev-if
                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons 'save (__toplevel_cons 'exp ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons 'save (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons 'save (__toplevel_cons 'continue ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                       'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                          'continue
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-if-decide ())) ())))
                                                                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                          'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                             'exp
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'op (__toplevel_cons 'if-predicate ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                             'goto
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                             'ev-if-decide
                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'restore (__toplevel_cons 'continue ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons 'restore (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons 'restore (__toplevel_cons 'exp ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            'test
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'op (__toplevel_cons 'true? ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'val ())) ())))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               'branch
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-if-consequent ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               'ev-if-alternative
                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        'exp
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons 'op (__toplevel_cons 'if-alternative ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        'goto
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        'ev-if-consequent
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 'exp
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'op (__toplevel_cons 'if-consequent ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 'goto
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 'ev-assignment
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          'unev
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons 'op (__toplevel_cons 'assignment-variable ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons 'save (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                'exp
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons 'op (__toplevel_cons 'assignment-value ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons 'save (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'save (__toplevel_cons 'continue ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         'continue
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-assignment-1 ())) ())))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         'goto
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         'ev-assignment-1
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'restore (__toplevel_cons 'continue ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'restore (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons 'restore (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        'perform
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons 'op (__toplevel_cons 'set-variable-value! ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons 'reg (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons 'reg (__toplevel_cons 'val ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'env ())) ())))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons 'val (__toplevel_cons (__toplevel_cons 'const (__toplevel_cons 'ok ())) ())))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons 'goto (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'continue ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              'ev-definition
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       'unev
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons 'op (__toplevel_cons 'definition-variable ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                 (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons 'save (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                    (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             'exp
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons 'op (__toplevel_cons 'definition-value ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'exp ())) ()))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                       (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons 'save (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons 'save (__toplevel_cons 'continue ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      'continue
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'ev-definition-1 ())) ())))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      'goto
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons (__toplevel_cons 'label (__toplevel_cons 'eval-dispatch ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                   (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      'ev-definition-1
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons 'restore (__toplevel_cons 'continue ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons 'restore (__toplevel_cons 'env ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                            (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons 'restore (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                               (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     'perform
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons 'op (__toplevel_cons 'define-variable! ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons 'reg (__toplevel_cons 'unev ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                           (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons 'reg (__toplevel_cons 'val ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'env ())) ())))))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        'assign
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons 'val (__toplevel_cons (__toplevel_cons 'const (__toplevel_cons 'ok ())) ())))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     (__toplevel_cons
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons 'goto (__toplevel_cons (__toplevel_cons 'reg (__toplevel_cons 'continue ())) ()))
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        (__toplevel_cons 'end ())))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
   (start eceval)
   (equal?
      result
      (__toplevel_cons
         'linebreak
         (__toplevel_cons
            ";;; EC-Eval input:"
            (__toplevel_cons
               'linebreak
               (__toplevel_cons
                  'linebreak
                  (__toplevel_cons
                     720
                     (__toplevel_cons
                        'linebreak
                        (__toplevel_cons
                           ";;; EC-Eval value:"
                           (__toplevel_cons
                              'linebreak
                              (__toplevel_cons
                                 (__toplevel_cons
                                    'total-pushes
                                    (__toplevel_cons
                                       '=
                                       (__toplevel_cons 208 (__toplevel_cons 'maximum-depth (__toplevel_cons '= (__toplevel_cons 26 ()))))))
                                 (__toplevel_cons
                                    'linebreak
                                    (__toplevel_cons
                                       'linebreak
                                       (__toplevel_cons
                                          ";;; EC-Eval input:"
                                          (__toplevel_cons
                                             'linebreak
                                             (__toplevel_cons
                                                'linebreak
                                                (__toplevel_cons
                                                   'ok
                                                   (__toplevel_cons
                                                      'linebreak
                                                      (__toplevel_cons
                                                         ";;; EC-Eval value:"
                                                         (__toplevel_cons
                                                            'linebreak
                                                            (__toplevel_cons
                                                               (__toplevel_cons
                                                                  'total-pushes
                                                                  (__toplevel_cons
                                                                     '=
                                                                     (__toplevel_cons 3 (__toplevel_cons 'maximum-depth (__toplevel_cons '= (__toplevel_cons 3 ()))))))
                                                               (__toplevel_cons
                                                                  'linebreak
                                                                  (__toplevel_cons
                                                                     'linebreak
                                                                     (__toplevel_cons ";;; EC-Eval input:" (__toplevel_cons 'linebreak (__toplevel_cons 'linebreak ()))))))))))))))))))))))))))