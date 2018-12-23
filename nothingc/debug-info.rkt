#lang racket/base

(provide compute-debug-information)

(require racket/match)
(require racket/set)

(require "lir.rkt")
(require "intervals.rkt")

(define (compute-debug-information peepholed-instrs)
  (define var-mapping
    (parameterize ((current-location-sanitizer values))
      (for/hash [((loc liveness) (in-hash (compute-live-intervals peepholed-instrs)))
                 #:when (and (location? loc) (lir-value-var loc))]
        (values loc liveness))))
  (define transition-points
    (let* ((ps (for*/fold [(ps (hash))]
                          [((loc liveness) (in-hash var-mapping))
                           (span (in-list (interval->list liveness)))]
                 (let* ((ps (hash-update ps (car span) (lambda (x) (set-add x `(map ,loc))) set))
                        (ps (hash-update ps (cdr span) (lambda (x) (set-add x `(unmap ,loc))) set)))
                   ps)))
           (ps (hash->list ps))
           (ps (sort ps < #:key car))
           (ps (map (match-lambda [(cons instr-num changes)
                                   (list instr-num (fresh-label '_debug_) changes)])
                    ps)))
      ps))
  (define instrumented-instrs
    (let loop ((instrs peepholed-instrs) (transition-points transition-points) (i 0))
      (cond
        [(null? transition-points) instrs]
        [(null? instrs)
         (error 'insert-debug-information
                "Should never happen: had remaining transitions after all instrs dead")]
        [(= i (car (car transition-points)))
         (cons (cadr (car transition-points)) (loop instrs (cdr transition-points) i))]
        [else
         (cons (car instrs) (loop (cdr instrs) transition-points (+ i 1)))])))
  (define debug-map
    (for/hash [(entry transition-points)]
      (match entry [(list _ label actions) (values label actions)])))
  ;; (pretty-print `((var-mapping ,var-mapping)
  ;;                 ;; (transition-points ,transition-points)
  ;;                 ;; (debug-map ,debug-map)
  ;;                 ))
  (values instrumented-instrs debug-map))
