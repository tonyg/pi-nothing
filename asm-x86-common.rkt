#lang racket/base
;; Common definitions for machine-code emission for i386 and x86_64.

(provide (struct-out relocation)
	 (struct-out label-reference)
	 (struct-out label-anchor)

	 (struct-out @imm)
	 (struct-out @reg)

	 memory?

	 condition-codes
	 invert-condition-code
	 condition-code-num

	 register=?
	 register?
	 immediate?

	 bitfield

	 onebyte-immediate?
	 imm8
	 imm32*
	 imm32
	 imm32-if
	 imm64*
	 imm64
	 imm64-if

	 mod-r-m*
	 mod-r-m

	 arithmetic-opcode

	 round-up-to-nearest
	 internal-link
	 )

(struct relocation (target) #:prefab)
(struct label-reference (name is-8bit) #:prefab)
(struct label-anchor (name) #:prefab)

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

(define (immediate? x)
  (or (number? x)
      (relocation? x)
      (label-reference? x)))

(define (bitfield . args)
  (define (loop acc args)
    (if (null? args)
	acc
	(let* ((width-parameter (car args))
	       (signed? (negative? width-parameter))
	       (width-in-bits (abs width-parameter))
	       (limit (inexact->exact (expt 2 width-in-bits))))
	  (let ((value (cadr args)))
	    (if (if signed?
		    (let ((half-limit (quotient limit 2)))
		      (or (>= value half-limit)
			  (< value (- half-limit))))
		    (or (>= value limit)
			(< value 0)))
		(error 'bitfield "Value ~v exceeds bitfield width ~v" value width-parameter)
		(loop (+ (* acc limit) (modulo value limit))
		      (cddr args)))))))
  (loop 0 args))

;; In 32-bit mode, #x66 is the 16-bit-operand override prefix

(define (onebyte-immediate? n)
  (and (number? n) (< n 128) (>= n -128)))

(define (imm8 i)
  (modulo i 256))

(define (shr v amount)
  (arithmetic-shift v (- amount)))

(define (imm32* i)
  (list (modulo i 256)
	(modulo (shr i 8) 256)
	(modulo (shr i 16) 256)
	(modulo (shr i 24) 256)))

(define (imm32 i)
  (if (or (relocation? i) (label-reference? i))
      (list i 0 0 0 0)
      (imm32* i)))

(define (imm32-if test-result i)
  (if test-result (imm32 i) (imm8 i)))

(define (imm64* i)
  (list (modulo i 256)
	(modulo (shr i 8) 256)
	(modulo (shr i 16) 256)
	(modulo (shr i 24) 256)
	(modulo (shr i 32) 256)
	(modulo (shr i 40) 256)
	(modulo (shr i 48) 256)
	(modulo (shr i 56) 256)))

(define (imm64 i)
  (if (or (relocation? i) (label-reference? i))
      (list i 0 0 0 0 0 0 0 0)
      (imm64* i)))

(define (imm64-if test-result i)
  (if test-result (imm64 i) (imm8 i)))

(define (mod-r-m* mod reg rm)
  (bitfield 2 mod 3 reg 3 rm))

;; Mod values:
;;  00 - no displacement, [reg]
;;  01 - 8bit displacement, [reg + n]
;;  10 - 32bit displacement, [reg + n]
;;  11 - direct, reg
(define (mod-r-m reg-num immNN reg modrm)
  (let ((reg (cond
	      ((number? reg) reg)
	      ((register? reg) (reg-num reg))
	      (else (error 'mod-r-m "needs a number or a register for reg ~v" reg)))))
    (cond
     ((register? modrm)
      (mod-r-m* 3 reg (reg-num modrm)))
     ((@imm? modrm)
      ;; raw absolute address, always 32 bits
      ;; see also caveat wrt (@reg 'ebp 0) below
      (list (mod-r-m* 0 reg 5) (immNN (@imm-address modrm))))
     ((@reg? modrm)
      (let ((base-reg (@reg-register modrm))
	    (offset (@reg-offset modrm)))
	(let ((mod (cond ((zero? offset) 0)
			 ((onebyte-immediate? offset) 1)
			 (else 2)))
	      (offset-bytes (cond ((zero? offset) '())
				  ((onebyte-immediate? offset) (imm8 offset))
				  (else (immNN offset)))))
	  (cond
	   ((register=? base-reg 'esp)
	    ;; can't directly use base reg, must use scaled indexing
	    (list (mod-r-m* mod reg 4) #x24 offset-bytes))
	   ((and (register=? base-reg 'ebp) (zero? offset))
	    ;; conflicts with raw absolute address "@imm" usage so we
	    ;; encode it with an explicit "+0"; see also above
	    (list (mod-r-m* 1 reg (reg-num base-reg)) 0))
	   (else
	    ;; normal
	    (list (mod-r-m* mod reg (reg-num base-reg)) offset-bytes))))))
     (else
      (error 'mod-r-m "needs a register or memory for modrm ~v" modrm)))))

(define (arithmetic-opcode opcode)
  (cond
   ((assq opcode '((add 0) (or 1) (adc 2) (sbb 3) (and 4) (sub 5) (xor 6) (cmp 7))) => cadr)
   (else (error 'arithmetic-opcode "Invalid opcode ~v" opcode))))

(define (round-up-to-nearest n val)
  (let ((temp (+ val n -1)))
    (- temp (remainder temp n))))

(define (internal-link word-size-bytes immNN* instrs)
  (define positions
    (let loop ((i 0)
	       (instrs instrs)
	       (acc '()))
      (cond
       ((null? instrs) (reverse acc))
       ((label-anchor? (car instrs)) (loop i (cdr instrs) (cons (cons (car instrs) i) acc)))
       ((label-reference? (car instrs)) (loop i (cdr instrs) acc))
       (else (loop (+ i 1) (cdr instrs) acc)))))
  (let loop ((i 0)
	     (instrs instrs)
	     (acc '())
	     (relocs '()))
    (cond
     ((null? instrs) (values (reverse acc) (reverse relocs)))
     ((label-anchor? (car instrs)) (loop i (cdr instrs) acc relocs))
     ((label-reference? (car instrs))
      (define l (car instrs))
      (cond
       ((assoc (label-anchor (label-reference-name l)) positions)
	=> (lambda (cell)
	     (define anchor-pos (cdr cell))
	     (define delta (- anchor-pos i))
	     (if (label-reference-is-8bit (car instrs))
		 (loop (+ i 1)
		       (cdr (cdr instrs))
		       (cons (imm8 (- delta 1)) acc)
		       relocs)
		 (loop (+ i word-size-bytes)
		       (cdr (cdr (cdr (cdr (cdr instrs)))))
		       (append (reverse (immNN* (- delta word-size-bytes))) acc)
		       relocs))))
       (else
	(loop i
	      (cdr instrs)
	      acc
	      (cons (cons i (car instrs)) relocs)))))
     (else (loop (+ i 1) (cdr instrs) (cons (car instrs) acc) relocs)))))
