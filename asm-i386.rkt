#lang racket/base

(require "asm-x86-common.rkt")

(provide (all-from-out "asm-x86-common.rkt")

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
	 *push
	 *pop

	 *leave
	 *ret

	 internal-link-32
	 )

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

(define (mod-r-m-32 reg modrm)
  (mod-r-m reg-num imm32 reg modrm))

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
		  (mod-r-m-32 opcode target)
		  (imm32-if (and (= w-bit 1) (not (onebyte-immediate? source))) source)))))
     ((memory? source)
      (cond
       ((not (register? target))
	(error '*op "~v: Cannot have memory source ~v and non-register target ~v"
	       opcode source target))
       (else
	(list (bitfield 2 0 3 opcode 2 1 1 w-bit) (mod-r-m-32 target source)))))
     ((register? source)
      (cond
       ((or (memory? target) (register? target))
	(list (bitfield 2 0 3 opcode 2 0 1 w-bit) (mod-r-m-32 source target)))
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
	  (mod-r-m-32 target target)
	  (imm32-if (not (onebyte-immediate? source)) source)))
   (else ;; memory or register source
    (list #x0F #xAF (mod-r-m-32 target source)))))

;; Unsigned multiply
(define (*mul multiplicand)
  (list #xF7 (mod-r-m-32 4 multiplicand)))

(define (*div divisor)
  (list #xF7 (mod-r-m-32 6 divisor)))

(define (*inc target)
  (list #xFF (mod-r-m-32 0 target)))

(define (*mov source target . maybe-8bit)
  (let ((w-bit (if (null? maybe-8bit) 1 (if (car maybe-8bit) 0 1))))
    (cond
     ((immediate? source)
      (if (register? target)
	  ;; special alternate encoding
	  (list (bitfield 4 #b1011 1 w-bit 3 (reg-num target))
		(imm32-if (= w-bit 1) source))
	  (list (bitfield 2 3 3 0 2 3 1 w-bit)
		(mod-r-m-32 0 target)
		(imm32-if (= w-bit 1) source))))
     ((memory? source)
      (cond
       ((and (@imm? source) (register=? target 'eax))
	;; special alternate encoding
	(list (bitfield 7 #b1010000 1 w-bit) (imm32 (@imm-address source))))
       ((not (register? target))
	(error "*mov: Cannot have memory source and non-register target" (list source target)))
       (else
	(list (bitfield 2 2 3 1 2 1 1 w-bit) (mod-r-m-32 target source)))))
     ((register? source)
      (cond
       ((and (@imm? target) (register=? source 'eax))
	;; special alternate encoding
	(list (bitfield 7 #b1010001 1 w-bit) (imm32 (@imm-address target))))
       ((or (memory? target) (register? target))
	(list (bitfield 2 2 3 1 2 0 1 w-bit) (mod-r-m-32 source target)))
       (else
	(error "*mov: Cannot have register source and non-mem, non-reg target"
	       (list source target)))))
     (else
      (error "*mov: Invalid source" (list source target))))))

(define (*cmov code source target)
  (list #x0F (bitfield 4 4 4 (condition-code-num code)) (mod-r-m-32 target source)))

(define (*call-or-jmp-like immediate-opcode indirect-mod loc)
  (cond
   ((immediate? loc)
    (list immediate-opcode (imm32 loc)))
   ((or (register? loc) (memory? loc))
    (list #xFF (mod-r-m-32 indirect-mod loc)))
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

(define (*push reg)
  (mod-r-m* 1 2 (reg-num reg)))

(define (*pop reg)
  (mod-r-m* 1 3 (reg-num reg)))

(define (*leave) #xC9)
(define (*ret) #xC3)

(define (internal-link-32 instrs)
  (internal-link 4 imm32* instrs))
