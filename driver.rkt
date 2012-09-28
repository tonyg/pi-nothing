#lang racket/base

(require racket/match)

(require racket/pretty)

(require "lir.rkt")
(require "machine.rkt")
(require "nothing.rkt")
(require "regalloc.rkt")
(require "peephole.rkt")
(require "linker.rkt")

(provide compile-procedure)

(define (compile-procedure md arg-names body-exp env)
  (define argcount (length arg-names))
  (define rib (map (lambda (a) (list a (fresh-reg))) arg-names))
  (define target-reg (fresh-reg))
  (define-values (body-instrs body-data)
    (frontend body-exp (append rib env)))
  (define most-tail-args (apply max (map (match-lambda
					  [`(tailcall ,_ ,_ ,args) (length args)]
					  [_ 0])
					 body-instrs)))
  (define surplus-tail-args (max 0 (- most-tail-args argcount)))
  ;;(pretty-print `(most-tail-args ,most-tail-args))
  ;;(pretty-print `(surplus-tail-args ,surplus-tail-args))
  (pretty-print `(pre-expansion (body-instrs ,body-instrs)
				(body-data ,body-data)))
  (define init-arg-instrs (do ((i 0 (+ i 1))
			       (rib rib (cdr rib))
			       (prolog '() (cons `(move-word ,(cadr (car rib))
							     ,(inward-argument-location md i))
						 prolog)))
			      ((null? rib) (reverse prolog))))
  (define instrs (expand-instructions md init-arg-instrs body-instrs))
  ;;(pretty-print `(post-expansion ,instrs))
  (define-values (temp-count allocated-instrs) (allocate-registers md surplus-tail-args instrs))
  (define peepholed-instrs (peephole allocated-instrs))
  (pretty-print `(peepholed-instrs ,peepholed-instrs))
  (define-values (machine-code machine-data)
    (assemble md argcount temp-count peepholed-instrs))
  (pretty-print `(pre-linking (machine-code ,machine-code)
			      (machine-data ,machine-data)))
  (define-values (linked relocs) (internal-link (list machine-code
						      machine-data
						      body-data)
						#x80000000))
  (write `(relocations ,relocs)) (newline) (flush-output)
  (list->bytes linked))
