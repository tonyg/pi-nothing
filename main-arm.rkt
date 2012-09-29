#lang racket/base

(require racket/match)
(require (only-in racket/file file->list))
(require (only-in racket/list make-list))
(require racket/pretty)

(require "driver.rkt")
(require "linker.rkt")
(require "dump-bytes.rkt")
(require "disasm.rkt")

(require "lir.rkt")
(require "machine.rkt")
(require "asm-arm7.rkt")
(require "mach-arm7.rkt")

(define md machine-arm7)

(define start-addr #x00010000)

(define (startup-code)
  (list (*mov 'al 0 'lr 0)
	(*mov 'al 0 'sp #x00100000)
	(*bl 'al (label-reference 'main))
	(*b 'al 0) ;; loop forever
	))

(define (compile-toplevel form)
  (match form
    [`(define (,proc ,argname ...)
	,body ...)
     (define-values (code data) (compile-procedure md argname `(begin ,@body) '()))
     (values (cons (label-anchor proc) code) data)]
    [_
     (error 'compile-toplevel "Cannot compile toplevel form: ~v" form)]))

(define (link-blobs blobs)
  (define all-blobs (cons (startup-code) blobs))
  (pretty-print `(all-blobs ,all-blobs))
  (define-values (linked0 relocs link-map) (link all-blobs start-addr))
  (when (not (null? relocs))
    (error 'link-and-emit "Unresolved relocations: ~v" relocs))
  (define linked (list->bytes linked0))
  (dump-bytes! linked #:base start-addr) (flush-output)
  (for-each (match-lambda [(cons anchor addr)
			   (write `(,(label-anchor-name anchor) -> ,(number->string addr 16)))
			   (newline)])
	    link-map)
  (disassemble-bytes! linked
		      #:arch (machine-description-architecture md)
		      #:base start-addr)
  linked)

(define (pad-to bs multiple)
  (define l (machine-code-length bs))
  (define leftover (modulo l multiple))
  (if (zero? leftover)
      bs
      (cons bs (make-list (- multiple leftover) 0))))

(define (compile-file filename)
  (define all-forms (file->list filename))
  (let loop ((forms all-forms)
	     (blobs-rev '()))
    (match forms
      ['()
       (define blobs (reverse blobs-rev))
       (link-blobs blobs)]
      [(cons form rest)
       (define-values (code data) (compile-toplevel form))
       (loop rest
	     (list* (pad-to data 4)
		    (pad-to code 4)
		    blobs-rev))])))

(let ((bs (compile-file "kernel.nothing")))
  (with-output-to-file "kernel.bin"
    (lambda () (write-bytes bs))
    #:exists 'replace))
