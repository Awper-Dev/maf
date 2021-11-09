; Changes:
; * removed: 0
; * added: 0
; * swaps: 2
; * negated predicates: 0
; * swapped branches: 1
; * calls to id fun: 3
(letrec ((copy (lambda (from-vector to-vector from-index to-index)
                 (vector-set! to-vector to-index (vector-ref from-vector from-index))))
         (move (lambda (from-vector to-vector from-low from-high to-index)
                 (letrec ((move-iter (lambda (n)
                                       (<change>
                                          (if (<= (+ from-low n) from-high)
                                             (begin
                                                (copy from-vector to-vector (+ from-low n) (+ to-index n))
                                                (move-iter (+ n 1)))
                                             #f)
                                          ((lambda (x) x)
                                             (if (<= (+ from-low n) from-high)
                                                (begin
                                                   (<change>
                                                      (copy from-vector to-vector (+ from-low n) (+ to-index n))
                                                      (move-iter (+ n 1)))
                                                   (<change>
                                                      (move-iter (+ n 1))
                                                      (copy from-vector to-vector (+ from-low n) (+ to-index n))))
                                                #f))))))
                    (<change>
                       (move-iter 0)
                       ((lambda (x) x) (move-iter 0))))))
         (merge (lambda (vector1 vector2 vector low1 high1 low2 high2 to-index)
                  (letrec ((merge-iter (lambda (index index1 index2)
                                         (<change>
                                            (if (> index1 high1)
                                               (move vector2 vector index2 high2 index)
                                               (if (> index2 high2)
                                                  (move vector1 vector index1 high1 index)
                                                  (if (< (vector-ref vector1 index1) (vector-ref vector2 index2))
                                                     (begin
                                                        (copy vector1 vector index1 index)
                                                        (merge-iter (+ index 1) (+ index1 1) index2))
                                                     (begin
                                                        (copy vector2 vector index2 index)
                                                        (merge-iter (+ index 1) index1 (+ index2 1))))))
                                            ((lambda (x) x)
                                               (if (> index1 high1)
                                                  (move vector2 vector index2 high2 index)
                                                  (if (> index2 high2)
                                                     (move vector1 vector index1 high1 index)
                                                     (if (< (vector-ref vector1 index1) (vector-ref vector2 index2))
                                                        (<change>
                                                           (begin
                                                              (copy vector1 vector index1 index)
                                                              (merge-iter (+ index 1) (+ index1 1) index2))
                                                           (begin
                                                              (copy vector2 vector index2 index)
                                                              (merge-iter (+ index 1) index1 (+ index2 1))))
                                                        (<change>
                                                           (begin
                                                              (copy vector2 vector index2 index)
                                                              (merge-iter (+ index 1) index1 (+ index2 1)))
                                                           (begin
                                                              (copy vector1 vector index1 index)
                                                              (merge-iter (+ index 1) (+ index1 1) index2)))))))))))
                     (merge-iter to-index low1 low2))))
         (bottom-up-merge-sort (lambda (vector)
                                 (letrec ((merge-subs (lambda (len)
                                                        (let ((aux-vector (make-vector (vector-length vector) 0)))
                                                           (letrec ((merge-subs-iter (lambda (index)
                                                                                       (if (< index (- (vector-length vector) (* 2 len)))
                                                                                          (begin
                                                                                             (merge vector vector aux-vector index (+ index len -1) (+ index len) (+ index len len -1) index)
                                                                                             (move aux-vector vector index (+ index len len -1) index)
                                                                                             (merge-subs-iter (+ index len len)))
                                                                                          (if (< index (- (vector-length vector) len))
                                                                                             (begin
                                                                                                (merge
                                                                                                   vector
                                                                                                   vector
                                                                                                   aux-vector
                                                                                                   index
                                                                                                   (+ index len -1)
                                                                                                   (+ index len)
                                                                                                   (- (vector-length vector) 1)
                                                                                                   index)
                                                                                                (move aux-vector vector index (- (vector-length vector) 1) index))
                                                                                             #f)))))
                                                              (merge-subs-iter 0)))))
                                          (merge-sort-iter (lambda (len)
                                                             (if (< len (vector-length vector))
                                                                (begin
                                                                   (merge-subs len)
                                                                   (merge-sort-iter (* 2 len)))
                                                                #f))))
                                    (merge-sort-iter 1)))))
   (let ((aVector (vector 8 3 6 6 0 5 4 2 9 6)))
      (<change>
         (bottom-up-merge-sort aVector)
         (equal? aVector (vector 0 2 3 4 5 6 6 6 8 9)))
      (<change>
         (equal? aVector (vector 0 2 3 4 5 6 6 6 8 9))
         (bottom-up-merge-sort aVector))))