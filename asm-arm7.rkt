#lang racket/base

(require rackunit)

(require "asm-common.rkt")

(provide )

(define (reg-num reg)
  (cond
   ((number? reg) reg)
   ((eq? reg 'sp) 13)
   ((eq? reg 'lr) 14)
   ((eq? reg 'pc) 15)
   (else (error 'reg-num "Invalid register ~v" reg))))

(define (condition-code-num cc)
  (case cc
    ((eq) 0)
    ((ne) 1)
    ((cs) 2)
    ((cc) 3)
    ((mi) 4)
    ((pl) 5)
    ((vs) 6)
    ((vc) 7)
    ((hi) 8)
    ((ls) 9)
    ((ge) 10)
    ((lt) 11)
    ((gt) 12)
    ((le) 13)
    ((al) 14)
    ((nv) 15)
    (else (error 'condition-code-num "Invalid condition-code label ~v" cc))))

(define (bool->bit v)
  (if (boolean? v)
      (if v 1 0)
      v))

(define (*str cc p u w rn rt imm5 type rm) ;; A8.6.195, STR (register), A8-386 in ARM DDI 0406B
  (imm32 (bitfield 4 (condition-code-num cc)
		   3 3
		   1 (bool->bit p)
		   1 (bool->bit u)
		   1 0
		   1 (bool->bit w)
		   1 0
		   4 (reg-num rn)
		   4 (reg-num rt)
		   5 imm5
		   2 type
		   1 0
		   4 rm)))

(require (only-in racket/list flatten))
(let-values (((instrs relocs)
	      (internal-link 32
			     imm32*
			     (flatten (list (*str 'al  0 0 0  0 0  0 0  0)
					    (*str 'gt  0 0 0  1 2  0 0  3))))))
  (write-bytes (list->bytes instrs))
  (void))
