#lang racket/base
;; Copyright (C) 2012-2015 Tony Garnock-Jones <tonyg@leastfixedpoint.com>
;;
;; This file is part of pi-nothing.
;;
;; pi-nothing is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License,
;; or (at your option) any later version.
;;
;; pi-nothing is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with pi-nothing. If not, see <http://www.gnu.org/licenses/>.

(require racket/match)

(require racket/pretty)

(require "lir.rkt")
(require "machine.rkt")
(require "nothing.rkt")
(require "regalloc.rkt")
(require "peephole.rkt")
(require "linker.rkt")
(require "debug-info.rkt")

(provide compile-procedure
	 compile-and-link-procedure)

(define (compile-procedure md proc-name arg-names body-exp env)
  (define argcount (length arg-names))
  (define rib (map (lambda (a) (list a (fresh-reg a))) arg-names))
  (define target-reg (fresh-reg))
  (define-values (body-instrs body-data)
    (frontend proc-name body-exp (append rib env)))
  (define most-tail-args (apply max
				argcount
				(map (match-lambda
				      [`(tailcall ,_ ,args) (length args)]
				      [_ 0])
				     body-instrs)))
  ;; (pretty-display `(pre-expansion (body-instrs ,body-instrs)
  ;;                                 (body-data ,body-data)))
  (define init-arg-instrs (do ((i 0 (+ i 1))
			       (rib rib (cdr rib))
			       (prolog '() (cons `(move-word ,(cadr (car rib))
							     ,(inward-argument-location md i))
						 prolog)))
			      ((null? rib) (reverse prolog))))
  (define instrs (expand-instructions md init-arg-instrs body-instrs))
  (define leaf? (not (findf (match-lambda [`(call ,_ ,_ ,_) #t] [_ #f]) instrs)))
  ;; (pretty-display `(post-expansion ,instrs))
  (define-values (temp-count allocated-instrs) (allocate-registers md instrs))
  ;; (pretty-display `((leaf? ,leaf?)
  ;;                   (argcount ,argcount)
  ;;                   (most-tail-args ,most-tail-args)
  ;;                   (temp-count ,temp-count)))
  ;; (pretty-display `(post-allocation ,allocated-instrs))
  (define peepholed-instrs (peephole allocated-instrs))
  ;; (pretty-display `(peepholed-instrs ,peepholed-instrs))
  (define-values (peepholed-instrs/debug debug-map)
    (compute-debug-information peepholed-instrs))
  ;; (pretty-display `(peepholed-instrs/debug ,peepholed-instrs/debug))
  ;; (pretty-display `(debug-map ,debug-map))
  (define-values (machine-code machine-data)
    (assemble md argcount most-tail-args temp-count leaf? peepholed-instrs/debug))
  ;; (pretty-display `(pre-linking (machine-code ,machine-code)
  ;;                               (machine-data ,machine-data)))
  (values machine-code
	  (list machine-data
		body-data)
          debug-map))

(define (compile-and-link-procedure md proc-name arg-names body-exp env base-address)
  (define-values (code data debug-map)
    (compile-procedure md proc-name arg-names body-exp env))
  (define-values (linked relocs link-map) (link (list code data) base-address))
  (write `(relocations ,relocs)) (newline) (flush-output)
  (values (list->bytes linked) link-map debug-map))
