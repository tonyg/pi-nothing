#lang racket/base
;; Mach-O x86_64 executables (OS X)
;; Copyright (C) 2013 Tony Garnock-Jones <tonygarnockjones@gmail.com>
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

;; TODO: factor out commonality between main-arm.rkt and this.

(require racket/match)
(require racket/system)
(require racket/format)
(require racket/pretty)
(require (only-in racket/file file->list))
(require (only-in racket/list make-list append-map))

(require "driver.rkt")
(require "linker.rkt")
(require "dump-bytes.rkt")
(require "disasm.rkt")

(require "lir.rkt")
(require "machine.rkt")
(require "asm-x86_64.rkt")
(require "mach-x86_64.rkt")

;; It looks like (on my system, at least) program images are loaded
;; into core at 0x100000000. The first page begins with the Mach-O
;; header, so the actual program text starts toward the end of the
;; page. We force a 12-bit alignment before our "start" symbol so that
;; we know our code will be generated on the first page boundary
;; following the origin: 0x100001000.

(define assembly-prelude
  (string-append ".text\n"
		 ".code64\n"
		 ".globl start\n"
		 ".align 12\n"
		 "start:\n"))

(define md machine-x86_64)
(define start-addr #x100001000)

(define (write-image filename bs)
  (define assembly-filename (string-append filename ".S"))
  (with-output-to-file assembly-filename #:exists 'replace
    (lambda ()
      (display assembly-prelude)
      (for ((b (in-bytes bs)))
	(printf ".byte 0x~a\n" (~r b #:base 16 #:min-width 2 #:pad-string "0")))))
  (system* "/usr/bin/env" "gcc" "-nostdlib" "-static" "-o" filename assembly-filename))

(define (startup-code)
  (list (*op 'and #xfffffffffffffff0 'rsp) ;; 16-byte stack alignment; also reqd for syscalls
	(*call (label-reference 'main))
	(*mov 'rax 'rdi)
	(*call (label-reference '%%exit))
))

(define (make-syscall name body)
  (list (label-anchor name)
	(*push 'rbp)
	(*mov 'rsp 'rbp)
	(*op 'and #xfffffffffffffff0 'rsp)
	body
	(*leave)
	(*ret)))

(define (syscalls)
  (list (make-syscall '%%write ;; RDI=fd, RSI=ptr, RDX=length
		      (list (*mov #x2000004 'rax) ;; SYS_write
			    (*syscall)))
	(make-syscall '%%exit ;; RDI=exit_status
		      (list (*mov #x2000001 'rax) ;; SYS_exit
			    (*syscall)))
	))

(define (compile-toplevel form global-env)
  (match form
    [`(define (,proc ,argname ...)
	,body ...)
     (write `(compiling ,proc ...)) (newline)
     (define-values (code data) (compile-procedure md argname `(begin ,@body) global-env))
     (values (cons (label-anchor proc) code) data)]
    [`(struct ,_ ...)	(values '() '())]
    [`(const ,_ ...)	(values '() '())]
    [_
     (error 'compile-toplevel "Cannot compile toplevel form: ~v" form)]))

(define (link-blobs blobs)
  (define all-blobs (list* (startup-code)
			   (syscalls)
			   blobs))
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
  		      #:base 0) ;; should be start-addr, not 0
  linked)

(define (pad-to bs multiple)
  (define l (machine-code-length bs))
  (define leftover (modulo l multiple))
  (if (zero? leftover)
      bs
      (cons bs (make-list (- multiple leftover) #x90)))) ;; NOP

(define (field-def-size def)
  (match def
    [`(,name word64) 8]
    [`(,name word64 ,n) (* 8 n)]
    [`(,name word32) 4]
    [`(,name word32 ,n) (* 4 n)]
    [`(,name byte) 1]
    [`(,name byte ,n) (* 1 n)]))

(define (symbol-append . syms)
  (string->symbol (apply string-append (map symbol->string syms))))

(define (extract-constants forms)
  (append-map (match-lambda
	       [`(struct ,name (,field-defs ...))
		(define struct-size (foldl + 0 (map field-def-size field-defs)))
		(do ((field-defs field-defs (cdr field-defs))
		     (offset 0 (+ offset (field-def-size (car field-defs))))
		     (acc (list (list (symbol-append 'sizeof- name) (lit struct-size)))
			  (cons (list (symbol-append name '- (car (car field-defs))) (lit offset))
				acc)))
		    ((null? field-defs) (reverse acc)))]
	       [`(const ,name ,(? number? literal-value))
		(list (list name (lit literal-value)))]
	       [_
		'()])
	      forms))

(define (compile-file filename)
  (define all-forms (file->list filename))
  (define global-env (extract-constants all-forms))
  (let loop ((forms all-forms)
	     (blobs-rev '()))
    (match forms
      ['()
       (define blobs (reverse blobs-rev))
       (link-blobs blobs)]
      [(cons form rest)
       (define-values (code data) (compile-toplevel form global-env))
       (loop rest
	     (list* (pad-to data 4)
		    (pad-to code 4)
		    blobs-rev))])))

(define (compile-and-link filename-base)
  (let ((bs (compile-file (string-append filename-base".nothing"))))
    (write-image filename-base bs)))

(require racket/cmdline)
(compile-and-link
 (command-line
  #:program "exec-macho.rkt"
  #:args (base-filename)
  base-filename))
