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
(require "mach-i386.rkt")

(define (te args exp env)
  (display "===========================================================================")
  (newline)
  (pretty-print exp)
  (define machine-code (compile-procedure machine-i386 args exp env))
  (dump-bytes! machine-code)
  (disassemble-bytes! machine-code #:arch 'i386)
  (display "===========================================================================")
  (newline)
  (newline))

(require racket/pretty)

(te '() `(+ 1 2 3) '())
(te '() `(let ((a (? 123))) (+ a a a)) '())

(te '() '(/ 99 11) '())

(te '() `(/ (? 123) (? 234)) '())

(te '() `(let ((mutable a 0)) (while (< a 10) (set! a (+ a 1))) a) '())

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

(te '() `(if (if (< 11 22) 33 44) 55 66) '())
(te '()
    `(cond [(A) 11] [(B) 22] [(C) 33])
    `((A ,(label 'A))
      (B ,(label 'B))
      (C ,(label 'C))))

(te '(arg)
    `(if (< arg 2)
	 arg
	 (+ (fib (- arg 1)) (fib (- arg 2))))
    `((fib ,(label 'FIB))))

(te '() `(x (x (x))) `((x ,(label 'X))))

(te '(cx cy)
    '(let ((mutable zx 0)
	   (mutable zy 0)
	   (mutable i 0))
       (while (< (+ (* zx zx) (* zy zy)) 4)
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
       (while (< (+ (* zx zx) (* zy zy)) 4)
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

(let ((args '(a b))
      (exp '(+ a b))
      (env '()))
  (local-require "reflect-machine-code.rkt")
  (local-require (only-in '#%foreign _int32 _pointer _void))
  (define machine-code (compile-procedure (current-machine-description) args exp env))
  (dump-bytes! machine-code)
  (disassemble-bytes! machine-code)
  (define p (reflect-machine-code machine-code (list _int32 _int32) _int32))
  (printf "Result: ~v" (p 123 234)))
