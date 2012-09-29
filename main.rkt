#lang racket/base

;;---------------------------------------------------------------------------
;; Other machines

;; (define available-regs (map preg (list 'rax 'rbx 'rcx 'rdx 'rsi 'rdi
;; 				       'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15)))
;;(define available-regs (map preg (list 'r0 'r1 'r2 'r3 'r4 'r5 'r6 'r7)))
;;(define available-regs (map preg (list 'r0 'r1)))
;;(define available-regs (map preg (list)))

(require "driver.rkt")
(require "dump-bytes.rkt")
(require "disasm.rkt")
(require "platform.rkt")

(require "lir.rkt")
(require "machine.rkt")
(require "mach-arm7.rkt")
(require "mach-i386.rkt")
(require "mach-x86_64.rkt")

;;(define te-machine machine-x86_64)
(define te-machine machine-i386)
;;(define te-machine machine-arm7)

(define (te args exp env)
  (display "===========================================================================")
  (newline)
  (pretty-print exp)
  (define machine-code (compile-and-link-procedure te-machine args exp env #x80000000))
  (dump-bytes! machine-code #:base #x80000000) (newline) (flush-output)
  (disassemble-bytes! machine-code
		      #:arch (machine-description-architecture te-machine)
		      #:base #x80000000)
  (display "===========================================================================")
  (newline)
  (newline))

(define (re args exp env vals)
  (local-require "reflect-machine-code.rkt")
  (local-require (only-in '#%foreign _pointer _void))
  (define inttype (machine-description-word-ctype (current-machine-description)))
  (display "***************************************************************************")
  (newline)
  (pretty-print exp)
  (pretty-print args)
  (pretty-print vals)
  (define machine-code (compile-and-link-procedure (current-machine-description) args exp env
						   ;; TODO: better way of determining base-address
						   #x80000000))
  (dump-bytes! machine-code #:base #x80000000) (newline) (flush-output)
  (disassemble-bytes! machine-code #:base #x80000000)
  (define p (reflect-machine-code machine-code
				  (map (lambda (arg) inttype) args)
				  inttype))
  (define result (apply p vals))
  (printf "Result: ~v\n" result)
  (display "***************************************************************************")
  (newline)
  (newline)
  result)

(require racket/pretty)
(require rackunit)

(te '() '(data #"Hello") '())

(te '() '(outermost 1 (middle 2 (innermost 3) 4) 5) '())

(te '() `(+ 1 2 3) '())
(te '() `(let ((a (? 123))) (+ a a a)) '())

(te '() '(/ 99 11) '())

(te '() `(/ (? 123) (? 234)) '())

(te '() `(let ((mutable a 0)) (while (<s a 10) (set! a (+ a 1))) a) '())

(te '()
    `(let ((a (? 123))
	   (b (? 234)))
       (+ a 90 9 b))
    '())

(te '()
    `(+ (? 123) (- 99 9) 9 (? 234))
    '())

(te '()
    `(+ (fib 2) (fib 1))
    `((fib ,(label 'FIB))))

(te '() `(if (if (<s 11 22) 33 44) 55 66) '())
(te '()
    `(cond [(A) 11] [(B) 22] [(C) 33])
    `((A ,(label 'A))
      (B ,(label 'B))
      (C ,(label 'C))))

(te '(arg)
    `(if (<s arg 2)
	 arg
	 (+ (fib (- arg 1)) (fib (- arg 2))))
    `((fib ,(label 'FIB))))

(te '() `(x (x (x))) `((x ,(label 'X))))

(te '(cx cy)
    '(let ((mutable zx 0)
	   (mutable zy 0)
	   (mutable i 0))
       (while (<s (+ (* zx zx) (* zy zy)) 4)
	 (let ((tx (+ cx (- (* zx zx) (* zy zy))))
	       (ty (+ cy (* 2 zx zy))))
	   (set! i (+ i 1))
	   (set! zx tx)
	   (set! zy ty)))
       i)
    `())

(te '(cx cy)
    '(let ((mutable zx 0)
	   (mutable zy 0)
	   (mutable i 0))
       (while (<s (+ (* zx zx) (* zy zy)) 4)
	 (let ((tx zx) (ty zy))
	   (set! zx (+ cx (- (* tx tx) (* ty ty))))
	   (set! zy (+ cy (* 2 tx ty)))
	   (set! i (+ i 1))))
       i)
    `())

(te '()
    '(let ((v20 (? 20)) (v21 (? 21)) (v22 (? 22)) (v23 (? 23)) (v24 (? 24))
	   (v25 (? 25)) (v26 (? 26)) (v27 (? 27)) (v28 (? 28)) (v29 (? 29)))
       (+ v20 v21 v22 v23 v24 v25 v26 v27 v28 v29))
    '())

(te '()
    '(let ((v20 (? 20)) (v21 (? 21)) (v22 (? 22)) (v23 (? 23)) (v24 (? 24))
	   (v25 (? 25)) (v26 (? 26)) (v27 (? 27)) (v28 (? 28)) (v29 (? 29)))
       (x v20 v21 v22 v23 v24 v25 v26 v27 v28 v29))
    `((x ,(label 'X))))

(te '(argc argv)
    '(begin
       (puts (data #"Hello world"))
       #x12345678)
    `((puts ,(label '_puts))))

(check-equal? (re '(a b) '(+ a b) '() '(123 234)) 357)
(check-equal? (re '(a b) '(if (>s a b) 111 222) '() '(123 234)) 222)
(check-equal? (re '(a b) '(if (>s a b) 111 222) '() '(234 123)) 111)
(check-equal? (re '(a b) '(if (<s a b) 111 222) '() '(123 234)) 111)

(check-equal? (re '(a b) '(if (= a b) 111 222) '() '(123 123)) 111)
(check-equal? (re '(a b) '(if (= a b) 111 222) '() '(123 234)) 222)

(check-equal? (re '(a b) '(if (>s a b) a b) '() '(123 234)) 234)
(check-equal? (re '(a b) '(if (>s a b) a b) '() '(234 123)) 234)
(check-equal? (re '(a b) '(if (<s a b) a b) '() '(123 234)) 123)
(check-equal? (re '(a b) '(if (<s a b) a b) '() '(234 123)) 123)

(check-equal? (re '() '(/ 123 60) '() '()) 2)
(check-equal? (re '() '(% 123 60) '() '()) 3)
