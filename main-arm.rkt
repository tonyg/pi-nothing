#lang racket/base
;; Copyright (C) 2012 Tony Garnock-Jones <tonygarnockjones@gmail.com>
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
(require (only-in racket/file file->list))
(require (only-in racket/list make-list append-map))
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

(define start-addr (make-parameter #x00010000))
(define stack-origin (make-parameter #x00100000))
(define output-file (make-parameter #f))

(define (startup-code)
  (define stack-top (stack-origin))
  (define (allocate-stack! npages)
    (begin0 stack-top
      (set! stack-top (- stack-top (* npages 4096)))))
  (list (*mov 'al 0 'lr 0)

        ;; Set up stack pointers in all modes, including SVC mode (the current mode)
        (let ((disable-interrupts #xc0))
          (list (*mrs 'al #f 'r8) ;; avoid stomping on R0-R3, which are used for ATAGs etc.
                (*msr 'al #f '(c) (bitwise-ior disable-interrupts arm-mode-fiq))
                (*mov 'al 0 'sp (allocate-stack! 1))
                (*msr 'al #f '(c) (bitwise-ior disable-interrupts arm-mode-irq))
                (*mov 'al 0 'sp (allocate-stack! 1))
                (*msr 'al #f '(c) 'r8)
                (*mov 'al 0 'sp stack-top)))

        ;; because we took care to preserve R0-R3, they are implicitly
        ;; visible as the first four arguments to main.
	(*bl 'al (label-reference 'main))
	(*b 'al 0) ;; loop forever
	))

(define (__udivsi3-code)
  (define A 'r0)
  (define B 'r1)
  (define R 'r2)
  (define I 'r3)
  (define Q 'r7)
  (define ONE 'lr) ;; !
  (list (label-anchor '__udivsi3)
	;; Based on clang-163.7.1's udivsi3.S, under MIT license
	  (*push 'al '(r7 lr))
	  (*clz 'al 'r2 A)
	  (*tst 'al B B)
	  (*clz 'al 'r3 B)
	  (*mov 'al 0 Q 0)
	  (*b 'eq (label-reference '__udivsi3-division-by-zero))
	  (*mov 'al 0 ONE 1)
	  (*sub 'al 1 I 'r3 'r2)
	  (*b 'lt (label-reference '__udivsi3-return))
	(label-anchor '__udivsi3-mainloop)
	  (*sub 'al 1 R A (@shifted B I))
	  (*orr 'hs 0 Q Q (@shifted ONE I))
	  (*mov 'hs 0 A R)
	  (*sub 'ne 1 I I 1)
	  (*b 'hi (label-reference '__udivsi3-mainloop))
	  (*sub 'al 1 R A B)
	  (*orr 'hs 0 Q Q 1)
	  (*mov 'hs 0 A R)
	(label-anchor '__udivsi3-return)
	  (*mov 'al 0 'r1 A) ;; remainder
	  (*mov 'al 0 'r0 Q)
	  (*pop 'al '(r7 pc))
	(label-anchor '__udivsi3-division-by-zero)
	  (*pop 'al '(r7 lr))
	  (*b 'al (label-reference 'division-by-zero))))

(define (exception-handler fiq? vector-address-label)
  (define reglist (if fiq?
                      '(r0 r1 r2 r3 r4 r5 r6 r7)
                      '(r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12)))
  (list (*push 'al reglist)
        (label-linker vector-address-label
                      4
                      (lambda (delta i)
                        (define adjusted (- delta 8)) ;; (pc+8)-relative
                        (*ldr 'al
                              'r0
                              (if (negative? adjusted)
                                  (@reg 'pc '- (- adjusted))
                                  (@reg 'pc '+ adjusted)))))
        (*mov 'al 0 'r11 'lr) ;; R11 is saved in our calling convention
        (*mov 'al 0 'lr 'pc) ;; gets this-instruction-plus-eight because of pipelining
        (*mov 'al 0 'pc 'r0)
        ;; here is where lr points after the mov-to-lr just above
        ;; R0 expected now to have a *positive* offset for LR in it, to be subtracted.
        (*sub 'al 0 'lr 'r11 'r0)
        (*pop 'al reglist)
        (*mov 'al 1 'pc 'lr) ;; the S bit makes SPSR -> CPSR, i.e. "iret"
        ))

(define (system-management-code)
  (list (label-anchor 'sys:wait-for-interrupt)
          ;; Per ARM ARM, cache management functions take the form
          ;; MCR p15, 0, <Rd>, c7, <CRm>, <opcode2>
          ;; where Wait For Interrupt has Rd=0, CRm=0, opcode2=4
          (*mcr 'al 15 0 'r0 7 0 4)
          (*mov 'al 0 'pc 'lr)
        (label-anchor 'sys:get-cpsr)
          (*mrs 'al #f 'r0)
          (*mov 'al 0 'pc 'lr)
        (label-anchor 'sys:get-spsr)
          (*mrs 'al #t 'r0)
          (*mov 'al 0 'pc 'lr)
        (label-anchor 'sys:set-cpsr)
          (*msr 'al #f '(c x s f) 'r0)
          (*mov 'al 0 'pc 'lr)
        (label-anchor 'sys:set-spsr)
          (*msr 'al #t '(c x s f) 'r0)
          (*mov 'al 0 'pc 'lr)
        (label-anchor 'sys:interrupt-vector-undefined-instruction)
          0 0 0 0 ;; undefined instruction, normal ret returns to just after failing insn
        (label-anchor 'sys:exception-handler-undefined-instruction)
          (exception-handler #f 'sys:interrupt-vector-undefined-instruction)
        (label-anchor 'sys:interrupt-vector-swi)
          0 0 0 0 ;; swi, normal ret returns to just after swi
        (label-anchor 'sys:exception-handler-swi)
          (exception-handler #f 'sys:interrupt-vector-swi)
        (label-anchor 'sys:interrupt-vector-prefetch-abort)
          0 0 0 0 ;; prefetch abort, normal ret returns to after failure PLUS FOUR
        (label-anchor 'sys:exception-handler-prefetch-abort)
          (exception-handler #f 'sys:interrupt-vector-prefetch-abort)
        (label-anchor 'sys:interrupt-vector-data-abort)
          0 0 0 0 ;; data abort, normal ret returns to after failure PLUS EIGHT
        (label-anchor 'sys:exception-handler-data-abort)
          (exception-handler #f 'sys:interrupt-vector-data-abort)
        (label-anchor 'sys:interrupt-vector-irq)
          0 0 0 0 ;; irq, normal ret returns to FOUR BYTES after normal next insn
        (label-anchor 'sys:exception-handler-irq)
          (exception-handler #f 'sys:interrupt-vector-irq)
        (label-anchor 'sys:interrupt-vector-fiq)
          0 0 0 0 ;; fiq, normal ret returns to FOUR BYTES after normal next insn
        (label-anchor 'sys:exception-handler-fiq)
          (exception-handler #t 'sys:interrupt-vector-fiq)
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
			   (__udivsi3-code)
                           (system-management-code)
			   blobs))
  (pretty-print `(all-blobs ,all-blobs))
  (define-values (linked0 relocs link-map) (link all-blobs (start-addr)))
  (when (not (null? relocs))
    (error 'link-and-emit "Unresolved relocations: ~v" relocs))
  (define linked (list->bytes linked0))
  (dump-bytes! linked #:base (start-addr)) (flush-output)
  (for-each (match-lambda [(cons anchor addr)
			   (write `(,(label-anchor-name anchor) -> ,(number->string addr 16)))
			   (newline)])
	    link-map)
  (disassemble-bytes! linked
		      #:arch (machine-description-architecture md)
		      #:base (start-addr))
  linked)

(define (pad-to bs multiple)
  (define l (machine-code-length bs))
  (define leftover (modulo l multiple))
  (if (zero? leftover)
      bs
      (cons bs (make-list (- multiple leftover) 0))))

(define (field-def-size def)
  (match def
    [`(,name word) 4]
    [`(,name word ,n) (* 4 n)]
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
    (with-output-to-file (or (output-file) (string-append filename-base".img"))
      (lambda () (write-bytes bs))
      #:exists 'replace)))

(require racket/cmdline)
(file-stream-buffer-mode (current-output-port) 'none)
(compile-and-link
 (command-line
  #:program "main-arm.rkt"
  #:once-each
  [("-o" "--output") f
   "Set output filename (default: INPUT.img)"
   (output-file f)]
  ["--start" addr-str
   "Set start address"
   (start-addr (string->number addr-str))]
  ["--stack" addr-str
   "Set stack origin"
   (stack-origin (string->number addr-str))]
  #:args (base-filename)
  base-filename))
