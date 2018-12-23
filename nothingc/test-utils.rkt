#lang racket/base

(require (only-in racket/list flatten))
(require rackunit)

(provide unhex-string
	 check-encoding-equal?)

(define (unhex-string str) ;; grumble
  (define cleaned (regexp-replace* #rx"[^0-9a-fA-F]+" str ""))
  (for/list [(i (in-range (/ (string-length cleaned) 2)))]
    (string->number (substring cleaned (* i 2) (+ 2 (* i 2))) 16)))

(define-syntax-rule (check-encoding-equal? actual expected)
  (check-equal? (flatten actual) (unhex-string expected)))
