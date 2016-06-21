#lang racket/base
;; pi-nothing ELF executable-producing compiler
;; Copyright (C) 2013-2015 Tony Garnock-Jones <tonyg@leastfixedpoint.com>
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

(require bitsyntax)

(require "driver.rkt")
(require "linker.rkt")
(require "dump-bytes.rkt")
(require "disasm.rkt")

(require "lir.rkt")
(require "machine.rkt")
(require (only-in "tailcall.rkt" make-location-resolver))
(require "elf.rkt")

(define (compile-toplevel md form global-env)
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

(define (field-def-size def)
  (match def
    [`(,name word64) 8]
    [`(,name word64 ,n) (* 8 n)]
    [`(,name word32) 4]
    [`(,name word32 ,n) (* 4 n)]
    [`(,name byte) 1]
    [`(,name byte ,n) (* 1 n)]))

(define (extract-constants forms)
  (define (symbol-append . syms)
    (string->symbol (apply string-append (map symbol->string syms))))
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

(define (compile-file filename
                      #:md md
                      #:pad-chunk pad-chunk)
  (define all-forms (file->list filename))
  (define global-env (extract-constants all-forms))
  (for/list [(form all-forms)]
    (define-values (code data) (compile-toplevel md form global-env))
    (list (pad-chunk code)
          (pad-chunk data))))

(define (link-blobs blobs md start-addr)
  (define-values (linked0 relocs link-map) (link blobs start-addr))
  (when (not (null? relocs))
    (error 'link-blobs "Unresolved relocations: ~v" relocs))
  (define linked (list->bytes linked0))
  (dump-bytes! linked #:base start-addr) (flush-output)
  (for-each (match-lambda [(cons anchor addr)
			   (write `(,(label-anchor-name anchor) -> ,(number->string addr 16)))
			   (newline)])
	    link-map)
  (disassemble-bytes! linked
  		      #:arch (machine-description-architecture md)
  		      #:base start-addr
                      #:link-map link-map)
  linked)

(define ((make-pad-chunk multiple pad-byte) bs)
  (define l (machine-code-length bs))
  (define leftover (modulo l multiple))
  (if (zero? leftover)
      bs
      (cons bs (make-list (- multiple leftover) pad-byte))))

(define (compile-and-link filename-base #:arch arch)
  ;; It looks like (on my Linux systems, at least) program images are
  ;; usually loaded into core at 0x400000, so we do the same here.
  (define origin-addr #x0000000000400000)
  (define start-offset #x80) ;; need to skip past the ELF header.
  (define start-addr (+ origin-addr start-offset))

  (define md (match arch
               ['arm7 (local-require "mach-arm7.rkt") machine-arm7]
               ['i386 (local-require "mach-i386.rkt") machine-i386]
               ['x86_64 (local-require "mach-x86_64.rkt") machine-x86_64]))

  (define blobs (list (match arch
                        ['arm7 (arm7-prelude)]
                        ['i386 (i386-prelude)]
                        ['x86_64 (x86_64-prelude)])
                      (compile-file (string-append filename-base".nothing")
                                    #:md md
                                    #:pad-chunk (match arch
                                                  ['arm7 (make-pad-chunk 4 0)]
                                                  ['i386 (make-pad-chunk 4 #x90)] ;; NOP
                                                  ['x86_64 (make-pad-chunk 16 #x90)] ;; NOP
                                                  ))))

  (define linked (link-blobs blobs md start-addr))

  (write-executable (format "~a.~a.elf" filename-base arch)
                    (match arch
                      ['arm7 (elf32-executable #:image linked
                                               #:machine 'arm7
                                               #:origin origin-addr
                                               #:start-offset start-offset
                                               #:e_flags (+ #x80  ;; EF_ARM_NEW_ABI
                                                            #x02) ;; EF_ARM_HASENTRY
                                               )]
                      ['i386 (elf32-executable #:image linked
                                               #:machine 'i386
                                               #:origin origin-addr
                                               #:start-offset start-offset)]
                      ['x86_64 (elf64-executable #:image linked
                                                 #:machine 'x86_64
                                                 #:origin origin-addr
                                                 #:start-offset start-offset)])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (arm7-prelude)
  (local-require "asm-arm7.rkt")
  (local-require "mach-arm7.rkt")

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
          (label-anchor 'division-by-zero)
            (*b 'al (label-reference 'division-by-zero))))

  (define (make-syscall name arg-count temp-count body-maker)
    (define R (make-location-resolver calling-convention-arm7 arg-count 0 (+ temp-count 1) #t))
    (define (A n) (R (inward-argument-location machine-arm7 n)))
    (list (label-anchor name)
          (*str 'al 'r7 (R (temporary temp-count)))
          (body-maker R A)
          (*ldr 'al 'r7 (R (temporary temp-count)))
          (*mov 'al 0 'pc 'lr)))

  (list (*bl 'al (label-reference 'main))
        (*bl 'al (label-reference '%%exit))
        (__udivsi3-code)
        (label-anchor '%%ostype)
        (*mov 'al 0 'r0 0)
        (*mov 'al 0 'pc 'lr)
        (label-anchor '%%wordsize)
        (*mov 'al 0 'r0 32)
        (*mov 'al 0 'pc 'lr)
        ;; System call table: http://syscalls.kernelgrok.com/
        (make-syscall '%%write 3 0 ;; r0=fd, r1=ptr, r2=length
                      (lambda (R A)
                        (list (*mov 'al 0 'r7 4)
                              (*swi 'al 0))))
        (make-syscall '%%exit 1 0 ;; r0=exit_status
                      (lambda (R A)
                        (list (*mov 'al 0 'r7 1) ;; __NR_exit <asm/unistd_64.h>
                              (*swi 'al 0))))
        (make-syscall '%%mmap 6 2 ;; r0=addr, r1=len, r2=prot, r3=flags,
                                  ;; r4=fd, r5=offset
                      (lambda (R A)
                        (list (*str 'al 'r4 (R (temporary 0)))
                              (*str 'al 'r5 (R (temporary 1)))
                              (*ldr 'al 'r4 (A 4))
                              (*ldr 'al 'r5 (A 5))
                              (*mov 'al 0 'r5 (@shifted 'r5 -12)) ;; convert to pages
                              (*mov 'al 0 'r7 #xc0) ;; mmap_pgoff
                              (*swi 'al 0)
                              (*ldr 'al 'r4 (R (temporary 0)))
                              (*ldr 'al 'r5 (R (temporary 1))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (i386-prelude)
  (local-require "asm-i386.rkt")
  (error 'i386-prelude "Unimplemented"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (x86_64-prelude)
  (local-require "asm-x86_64.rkt")

  (define (make-syscall name body)
    (list (label-anchor name)
          (*push 'rbp)
          (*mov 'rsp 'rbp)
          (*push 'r10)
          (*mov 'rcx 'r10)
          (*op 'and #xfffffffffffffff0 'rsp)
          body
          (*pop 'r10)
          (*leave)
          (*ret)))

  (list (*op 'and #xfffffffffffffff0 'rsp) ;; 16-byte stack alignment; also reqd for syscalls
	(*call (label-reference 'main))
	(*mov 'rax 'rdi)
	(*call (label-reference '%%exit))
	(label-anchor '%%ostype)
	(*mov 0 'rax)
	(*ret)
	(label-anchor '%%wordsize)
	(*mov 64 'rax)
	(*ret)
        ;; System call table: http://blog.rchapman.org/post/36801038863/linux-system-call-table-for-x86-64
        (make-syscall '%%write ;; RDI=fd, RSI=ptr, RDX=length
		      (list (*mov 1 'rax) ;; __NR_write <asm/unistd_64.h>
			    (*syscall)))
	(make-syscall '%%exit ;; RDI=exit_status
		      (list (*mov 60 'rax) ;; __NR_exit <asm/unistd_64.h>
			    (*syscall)))
	(make-syscall '%%mmap ;; RDI=addr, RSI=len, RDX=prot
                              ;; RCX=flags, R8=fd, R9=offset
		      (list (*mov 9 'rax) ;; __NR_mmap <asm/unistd_64.h>
			    (*syscall)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ main
  (require racket/cmdline)

  (file-stream-buffer-mode (current-output-port) 'none)

  (define target-architecture (make-parameter #f))

  (define base-filename
    (command-line
     #:program "exec-elf.rkt"
     #:once-any
     [("-a" "--arch") arch-str
      "Set target architecture (arm7, i386, x86_64)"
      (target-architecture (string->symbol arch-str))]
     #:args (base-filename)
     base-filename))

  (unless (target-architecture) (error 'exec-elf "Missing -a/--arch flag"))
  (compile-and-link base-filename
                    #:arch (target-architecture)))
