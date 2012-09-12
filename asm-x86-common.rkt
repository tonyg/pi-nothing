#lang racket/base
;; Common definitions for machine-code emission for i386 and x86_64.

(require "asm-common.rkt")

(provide (all-from-out "asm-common.rkt")

	 (struct-out @imm)
	 (struct-out @reg)

	 memory?

	 condition-codes
	 invert-condition-code
	 condition-code-num

	 register=?
	 register?

	 rex
	 mod-r-m*
	 mod-r-m

	 arithmetic-opcode
	 )

(struct @imm (address) #:prefab)
(struct @reg (register offset) #:prefab)

(define (memory? x)
  (or (@imm? x)
      (@reg? x)))

(define condition-codes '#((o)
			   (no)
			   (b nae)
			   (nb ae)
			   (e z)
			   (ne nz)
			   (be na)
			   (nbe a)
			   (s)
			   (ns)
			   (p pe)
			   (np po)
			   (l nge)
			   (nl ge)
			   (le ng)
			   (nle g)))

(define (invert-condition-code cc)
  (case cc
    ((o) 'no)
    ((b nae) 'nb)
    ((nb ae) 'b)
    ((e z) 'nz)
    ((ne nz) 'e)
    ((be na) 'a)
    ((nbe a) 'na)
    ((s) 'ns)
    ((ns) 's)
    ((p pe) 'np)
    ((np po) 'p)
    ((l nge) 'nl)
    ((nl ge) 'l)
    ((le ng) 'g)
    ((nle g) 'ng)))

(define (condition-code-num code-sym)
  (let loop ((i 0))
    (cond
     ((>= i 16) (error 'condition-code-num "Invalid condition-code ~v" code-sym))
     ((member code-sym (vector-ref condition-codes i)) i)
     (else (loop (+ i 1))))))

(define (register=? x y)
  (eq? x y))

(define (register? x)
  (symbol? x))

;; In 32-bit mode, #x66 is the 16-bit-operand override prefix

(define (rex reg-num w rreg xreg breg)
  (define (rex-bit r)
    (cond
     ((register? r) (bitwise-and 1 (shr (reg-num r) 3)))
     ((@imm? r) 0)
     ((@reg? r) (shr (reg-num (@reg-register r)) 3))
     ((number? r) (bitwise-and 1 (shr r 3)))
     (else (error 'rex-bit "Unsupported argument ~v" r))))
  (bitfield 4 4
	    1 w
	    1 (rex-bit rreg)
	    1 (rex-bit xreg)
	    1 (rex-bit breg)))

(define (mod-r-m* mod reg rm)
  (bitfield 2 mod 3 (bitwise-and 7 reg) 3 (bitwise-and 7 rm)))

(define (hi? v)
  (>= v 8))

;; Mod values:
;;  00 - no displacement, [reg]
;;  01 - 8bit displacement, [reg + n]
;;  10 - 32bit displacement, [reg + n]
;;  11 - direct, reg
(define (mod-r-m is-64bit? reg-num opcodes reg modrm)
  (define (rex-wrap r x b tail)
    (if is-64bit?
	(list (rex reg-num 1 r x b) opcodes tail)
	(list opcodes tail)))
  (let ((reg (cond
	      ((number? reg) reg)
	      ((register? reg) (reg-num reg))
	      (else (error 'mod-r-m "needs a number or a register for reg ~v" reg)))))
    (cond
     ((register? modrm)
      (rex-wrap reg 0 (reg-num modrm)
		(mod-r-m* 3 reg (reg-num modrm))))
     ((@imm? modrm)
      ;; raw absolute address, always 32 bits
      ;; see also caveat wrt (@reg 'ebp 0) below
      (if is-64bit?
	  (rex-wrap reg 0 0 (list (mod-r-m* 0 reg 4) #x25 (imm32 (@imm-address modrm))))
	  (list opcodes (mod-r-m* 0 reg 5) (imm32 (@imm-address modrm)))))
     ((@reg? modrm)
      (let ((base-reg (@reg-register modrm))
	    (offset (@reg-offset modrm)))
	(let ((mod (cond ((zero? offset) 0)
			 ((onebyte-immediate? offset) 1)
			 (else 2)))
	      (offset-bytes (cond ((zero? offset) '())
				  ((onebyte-immediate? offset) (imm8 offset))
				  (else (imm32 offset))))
	      (base-reg-num (reg-num base-reg)))
	  (cond
	   ((= base-reg-num 4) ;; esp, rsp
	    ;; can't directly use base reg, must use scaled indexing
	    (rex-wrap mod reg 4
		      (list (mod-r-m* mod reg 4) #x24 offset-bytes)))
	   ((and (= (bitwise-and 7 base-reg-num) 5) ;; ebp, rbp, r13
		 (zero? offset))
	    ;; conflicts with raw absolute address "@imm" usage so we
	    ;; encode it with an explicit "+0"; see also above
	    (rex-wrap 1 reg base-reg-num
		      (list (mod-r-m* 1 reg base-reg-num) 0)))
	   (else
	    ;; normal
	    (rex-wrap reg 0 base-reg-num
		      (list (mod-r-m* mod reg base-reg-num) offset-bytes)))))))
     (else
      (error 'mod-r-m "needs a register or memory for modrm ~v" modrm)))))

(define (arithmetic-opcode opcode)
  (cond
   ((assq opcode '((add 0) (or 1) (adc 2) (sbb 3) (and 4) (sub 5) (xor 6) (cmp 7))) => cadr)
   (else (error 'arithmetic-opcode "Invalid opcode ~v" opcode))))