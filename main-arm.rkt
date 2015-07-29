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
(require racket/date) ;; for KVer in write-trailer

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

(define (define-coprocessor-fetch name n op1 crn crm op2)
  (list (label-anchor name)
        (*mrc 'al n op1 'r0 crn crm op2)
        (*mov 'al 0 'pc 'lr)))

(define (define-coprocessor-store name n op1 crn crm op2)
  (list (label-anchor name)
        (*mcr 'al n op1 'r0 crn crm op2)
        (*mov 'al 0 'pc 'lr)))

(define (system-management-code)
  (list ;; Per ARM ARM, cache management functions take the form
        ;; MCR p15, 0, <Rd>, c7, <CRm>, <opcode2>
        ;; where Wait For Interrupt has Rd=0, CRm=0, opcode2=4
        ;;
        ;; TODO: ARMv7 makes this UNPREDICTABLE! and replaces it
        ;; with a specific WFI instruction.
        ;;
        (define-coprocessor-store 'sys:wait-for-interrupt 15 0 7 0 4)

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

        (define-coprocessor-fetch 'sys:get-sctlr 15 0 1 0 0) ;; SCTLR = System Control Register
        (define-coprocessor-store 'sys:set-sctlr 15 0 1 0 0)

        (define-coprocessor-fetch 'sys:get-ttbr0 15 0 2 0 0) ;; TTBR0 = root page table addr 0
        (define-coprocessor-store 'sys:set-ttbr0 15 0 2 0 0)
        (define-coprocessor-fetch 'sys:get-ttbr1 15 0 2 0 1) ;; TTBR1 = root page table addr 0
        (define-coprocessor-store 'sys:set-ttbr1 15 0 2 0 1)
        (define-coprocessor-fetch 'sys:get-ttbcr 15 0 2 0 2) ;; TTBCR = Transl. Table Base Ctl Reg
        (define-coprocessor-store 'sys:set-ttbcr 15 0 2 0 2)

        (define-coprocessor-fetch 'sys:get-mmu-domains 15 0 3 0 0)
        (define-coprocessor-store 'sys:set-mmu-domains 15 0 3 0 0)

        ;; Cache management
        (define-coprocessor-store 'sys:invalidate-instruction-cache 15 0 7 5 0)
        (label-anchor 'sys:instruction-sync-barrier)
        (label-anchor 'sys:instruction-mem-barrier)
        (define-coprocessor-store 'sys:flush-prefetch-buffer 15 0 7 5 4)
        (define-coprocessor-store 'sys:flush-branch-target-cache 15 0 7 5 6)
        (define-coprocessor-store 'sys:invalidate-data-cache 15 0 7 6 0)
        (define-coprocessor-store 'sys:clean-l1-data-cache 15 0 7 10 0)
        (define-coprocessor-store 'sys:clean-l2-data-cache 15 1 7 10 0)
        ;; TODO: ARMv7-specific instruction replaces the next two definitions:
        (define-coprocessor-store 'sys:data-sync-barrier 15 0 7 10 4)
        (define-coprocessor-store 'sys:data-mem-barrier 15 0 7 10 5)

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

;; Write a Raspberry Pi kernel trailer, to make the loader give us a devicetree.
(define (write-trailer)
  ;; Trailer format:
  ;;  * padded to 4-byte boundary
  ;;  * empty field to mark the end of the kernel, 8 bytes of zeros
  ;;  * each field is data, padded to 4-byte boundary
  ;;             then length, as little-endian 4-byte word; ACTUAL length, not padded length
  ;;             then key, as 4 bytes of ASCII in left-to-right order, i.e. big-endianish
  ;;  * the final field in the file must be RPTL = Raspberry Pi Trailer
  ;; Generally, integers will be little-endian.
  (define total-trailer-length 0)
  (define (counting-write bs)
    (set! total-trailer-length (+ total-trailer-length (bytes-length bs)))
    (write-bytes bs))
  (define (write-trailer-field label data)
    (counting-write data)
    (counting-write (make-bytes (bitwise-and 3 (- (bytes-length data))) 0))
    (counting-write (integer->integer-bytes (bytes-length data) 4 #f #f))
    (counting-write label))
  (write-trailer-field #"\0\0\0\0" #"")
  (write-trailer-field #"283x" (integer->integer-bytes 0 4 #f #f))
  (write-trailer-field #"DDTK" (integer->integer-bytes 0 4 #f #f))
  (write-trailer-field #"DTOK" (integer->integer-bytes 1 4 #f #f)) ;; 1 = we want devicetree
  (write-trailer-field #"KVer" (bytes-append #"pi-nothing experimental kernel "
                                             (string->bytes/latin-1
                                              (parameterize ((date-display-format 'iso-8601))
                                                (date->string (current-date) #t)))))
  (write-trailer-field #"RPTL" (integer->integer-bytes (+ total-trailer-length 8) 4 #f #f)))

(define (compile-and-link filename-base)
  (let ((bs (compile-file (string-append filename-base".nothing"))))
    (with-output-to-file (or (output-file) (string-append filename-base".img"))
      (lambda ()
        (write-bytes bs)
        (write-bytes (make-bytes (bitwise-and 3 (- (bytes-length bs))) 0)) ;; pad to multiple-of-four
        (write-trailer))
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
