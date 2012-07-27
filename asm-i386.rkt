#lang racket/base

(provide (struct-out relocation)
	 (struct-out label-reference)
	 (struct-out label-anchor)

	 (struct-out @imm)
	 (struct-out @reg)

	 invert-condition-code

	 onebyte-immediate?
	 imm8
	 imm32*
	 imm32
	 imm32-if
	 round-up-to-nearest

	 mod-r-m*
	 mod-r-m

	 *op
	 *imul
	 *mul
	 *div
	 *inc
	 *mov
	 *cmov
	 *call-or-jmp-like
	 *call
	 *jmp
	 *jmp-cc
	 *push32
	 *pop32

	 *leave
	 *ret

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

(define regs '((eax 0)
	       (ecx 1)
	       (edx 2)
	       (ebx 3)
	       (esp 4)
	       (ebp 5)
	       (esi 6)
	       (edi 7)))

(define (reg-num reg)
  (cond
   ((assq reg regs) => cadr)
   (else (error 'reg-num "Invalid register ~v" reg))))

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

(define (mod-r-m* mod reg rm)
  (bitfield 2 mod 3 reg 3 rm))

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

;; Mod values:
;;  00 - no displacement, [reg]
;;  01 - 8bit displacement, [reg + n]
;;  10 - 32bit displacement, [reg + n]
;;  11 - direct, reg
(define (mod-r-m reg modrm)
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
      (list (mod-r-m* 0 reg 5) (imm32 (@imm-address modrm))))
     ((@reg? modrm)
      (let ((base-reg (@reg-register modrm))
	    (offset (@reg-offset modrm)))
	(let ((mod (cond ((zero? offset) 0)
			 ((onebyte-immediate? offset) 1)
			 (else 2)))
	      (offset-bytes (cond ((zero? offset) '())
				  ((onebyte-immediate? offset) (imm8 offset))
				  (else (imm32 offset)))))
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

(define (*op opcode source target . maybe-8bit)
  (let ((opcode (arithmetic-opcode opcode))
	(w-bit (if (null? maybe-8bit) 1 (if (car maybe-8bit) 0 1))))
    (cond
     ((immediate? source)
      (let ((s-bit (if (and (= w-bit 1) (onebyte-immediate? source)) 1 0)))
	(if (register=? target 'eax)
	    (list (bitfield 2 0 3 opcode 2 2 1 w-bit)
		  (imm32-if (= w-bit 1) source))
	    (list (bitfield 2 2 3 0 1 0 1 s-bit 1 w-bit)
		  (mod-r-m opcode target)
		  (imm32-if (and (= w-bit 1) (not (onebyte-immediate? source))) source)))))
     ((memory? source)
      (cond
       ((not (register? target))
	(error '*op "~v: Cannot have memory source ~v and non-register target ~v"
	       opcode source target))
       (else
	(list (bitfield 2 0 3 opcode 2 1 1 w-bit) (mod-r-m target source)))))
     ((register? source)
      (cond
       ((or (memory? target) (register? target))
	(list (bitfield 2 0 3 opcode 2 0 1 w-bit) (mod-r-m source target)))
       (else
	(error '*op "~v: Cannot have register source ~v and non-mem, non-reg target ~v"
	       opcode source target))))
     (else
      (error '*op "~v: Invalid source ~v (target ~v)" opcode source target)))))

;; Signed multiply
(define (*imul source target)
  (cond
   ((not (register? target))
    (error '*imul "Cannot have non-register target ~v" target))
   ((immediate? source)
    (list (if (onebyte-immediate? source) #x6B #x69)
	  (mod-r-m target target)
	  (imm32-if (not (onebyte-immediate? source)) source)))
   (else ;; memory or register source
    (list #x0F #xAF (mod-r-m target source)))))

;; Unsigned multiply
(define (*mul multiplicand)
  (list #xF7 (mod-r-m 4 multiplicand)))

(define (*div divisor)
  (list #xF7 (mod-r-m 6 divisor)))

(define (*inc target)
  (list #xFF (mod-r-m 0 target)))

(define (*mov source target . maybe-8bit)
  (let ((w-bit (if (null? maybe-8bit) 1 (if (car maybe-8bit) 0 1))))
    (cond
     ((immediate? source)
      (if (register? target)
	  ;; special alternate encoding
	  (list (bitfield 4 #b1011 1 w-bit 3 (reg-num target))
		(imm32-if (= w-bit 1) source))
	  (list (bitfield 2 3 3 0 2 3 1 w-bit)
		(mod-r-m 0 target)
		(imm32-if (= w-bit 1) source))))
     ((memory? source)
      (cond
       ((and (@imm? source) (register=? target 'eax))
	;; special alternate encoding
	(list (bitfield 7 #b1010000 1 w-bit) (imm32 (@imm-address source))))
       ((not (register? target))
	(error "*mov: Cannot have memory source and non-register target" (list source target)))
       (else
	(list (bitfield 2 2 3 1 2 1 1 w-bit) (mod-r-m target source)))))
     ((register? source)
      (cond
       ((and (@imm? target) (register=? source 'eax))
	;; special alternate encoding
	(list (bitfield 7 #b1010001 1 w-bit) (imm32 (@imm-address target))))
       ((or (memory? target) (register? target))
	(list (bitfield 2 2 3 1 2 0 1 w-bit) (mod-r-m source target)))
       (else
	(error "*mov: Cannot have register source and non-mem, non-reg target"
	       (list source target)))))
     (else
      (error "*mov: Invalid source" (list source target))))))

(define (*cmov code source target)
  (list #x0F (bitfield 4 4 4 (condition-code-num code)) (mod-r-m target source)))

(define (*call-or-jmp-like immediate-opcode indirect-mod loc)
  (cond
   ((immediate? loc)
    (list immediate-opcode (imm32 loc)))
   ((or (register? loc) (memory? loc))
    (list #xFF (mod-r-m indirect-mod loc)))
   (else
    (error "*call/*jmp: Invalid location" loc))))

(define (*call loc)
  (*call-or-jmp-like #xE8 2 loc))

(define (is-short-jump? loc)
  (and (label-reference? loc)
       (label-reference-is-8bit loc)))

(define (*jmp loc)
  (if (is-short-jump? loc)
      (list #xEB loc 0)
      (*call-or-jmp-like #xE9 4 loc)))

(define (*jmp-cc code loc)
  (let ((tttn (condition-code-num code)))
    (if (is-short-jump? loc)
	(list (bitfield 4 7 4 tttn) loc 0)
	(list #x0F (bitfield 4 8 4 tttn) (imm32 loc)))))

(define (*push32 reg)
  (mod-r-m* 1 2 (reg-num reg)))

(define (*pop32 reg)
  (mod-r-m* 1 3 (reg-num reg)))

(define (round-up-to-nearest n val)
  (let ((temp (+ val n -1)))
    (- temp (remainder temp n))))

(define (*leave) #xC9)
(define (*ret) #xC3)

(define (internal-link instrs)
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
		 (loop (+ i 4)
		       (cdr (cdr (cdr (cdr (cdr instrs)))))
		       (append (reverse (imm32* (- delta 4))) acc)
		       relocs))))
       (else
	(loop i
	      (cdr instrs)
	      acc
	      (cons (cons i (car instrs)) relocs)))))
     (else (loop (+ i 1) (cdr instrs) (cons (car instrs) acc) relocs)))))
