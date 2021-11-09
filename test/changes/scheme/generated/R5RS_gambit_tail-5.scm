; Changes:
; * removed: 1
; * added: 1
; * swaps: 0
; * negated predicates: 0
; * swapped branches: 0
; * calls to id fun: 1
(letrec ((inport #f)
         (outport #f)
         (readline (lambda (port line-so-far)
                     (let ((x (read-char port)))
                        (if (eof-object? x)
                           x
                           (if (char=? x #\
)
                              (list->string (reverse (cons x line-so-far)))
                              (readline port (cons x line-so-far)))))))
         (tail-r-aux (lambda (port file-so-far)
                       (<change>
                          ()
                          x)
                       (let ((x (readline port ())))
                          (if (eof-object? x)
                             (begin
                                (display file-so-far outport)
                                (close-output-port outport))
                             (tail-r-aux port (cons x file-so-far))))))
         (tail-r (lambda (port)
                   (<change>
                      (tail-r-aux port ())
                      ((lambda (x) x) (tail-r-aux port ())))))
         (go (lambda ()
               (set! inport (open-input-file "input.txt"))
               (<change>
                  (set! outport (open-output-file "output.txt"))
                  ())
               (tail-r inport)
               (close-input-port inport))))
   (go))