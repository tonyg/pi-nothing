#lang racket/base
;; Concrete machine: x86_64.

(require (only-in "machine.rkt" machine-description))

(provide machine-x86_64)

(define machine-x86_64
  (machine-description 'x86_64
		       (list)
		       (lambda (is) (error 'expand-instructions "Unimplemented"))
		       (lambda (is) (error 'expand-temporary-loads-and-stores "Unimplemented"))
		       (lambda (iac is) (error 'assemble "Unimplemented"))))
