#lang racket/base
;; Copyright (C) 2012-2015 Tony Garnock-Jones <tonyg@leastfixedpoint.com>
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

(require rackunit)

(require "asm-x86-common.rkt")

(provide (all-from-out "asm-x86-common.rkt")

	 *op
	 *imul
	 *not
	 *mul
	 *imul/extended
	 *div
	 *inc
	 *mov
	 *cmov
	 *movz
	 *setcc-eax
	 *call
	 *jmp
	 *jmp-cc
	 *push
	 *pop
	 *rol
	 *ror
	 *shl
	 *shr
	 *sar

	 *leave
	 *ret

	 *int
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

(define (mod-r-m-32 opcodes reg modrm)
  (mod-r-m #f 0 reg-num opcodes reg modrm))

(define (*op opcode source target . maybe-8bit)
  (let ((opcode (arithmetic-opcode opcode))
	(w-bit (if (null? maybe-8bit) 1 (if (car maybe-8bit) 0 1))))
    (cond
     ((immediate? source)
      (let ((s-bit (if (and (= w-bit 1) (onebyte-immediate? source)) 1 0)))
	(if (and (register=? target 'eax) (not (onebyte-immediate? source)))
	    (list (bitfield 2 0 3 opcode 2 2 1 w-bit)
		  (imm32-if (= w-bit 1) source))
	    (list (mod-r-m-32 (bitfield 2 2 3 0 1 0 1 s-bit 1 w-bit) opcode target)
		  (imm32-if (and (= w-bit 1) (not (onebyte-immediate? source))) source)))))
     ((memory? source)
      (cond
       ((not (register? target))
	(error '*op "~v: Cannot have memory source ~v and non-register target ~v"
	       opcode source target))
       (else
	(mod-r-m-32 (bitfield 2 0 3 opcode 2 1 1 w-bit) target source))))
     ((register? source)
      (cond
       ((or (memory? target) (register? target))
	(mod-r-m-32 (bitfield 2 0 3 opcode 2 0 1 w-bit) source target))
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
    (list (mod-r-m-32 (if (onebyte-immediate? source) #x6B #x69) target target)
	  (imm32-if (not (onebyte-immediate? source)) source)))
   (else ;; memory or register source
    (mod-r-m-32 (list #x0F #xAF) target source))))

(define (*not target)
  (mod-r-m-32 #xF7 2 target))

;; Unsigned multiply -- yields EDX:EAX
(define (*mul multiplicand)
  (mod-r-m-32 #xF7 4 multiplicand))

;; Signed multiply -- yields EDX:EAX
(define (*imul/extended multiplicand)
  (mod-r-m-32 #xF7 5 multiplicand))

(define (*div divisor)
  (mod-r-m-32 #xF7 6 divisor))

(define (*inc target)
  (mod-r-m-32 #xFF 0 target))

(define (*shift-ish name subop amount target)
  (cond
   ((immediate? amount)
    (list (mod-r-m-32 #xC1 subop target) amount))
   ((eq? amount 'rcx)
    (mod-r-m-32 #xD3 subop target))
   (else
    (error '*shl "~a: Can only assemble immediate or CL shift; got ~v" name amount))))

(define (*rol amount target) (*shift-ish '*rol 0 amount target))
(define (*ror amount target) (*shift-ish '*ror 1 amount target))
(define (*shl amount target) (*shift-ish '*shl 4 amount target))
(define (*shr amount target) (*shift-ish '*shr 5 amount target))
(define (*sar amount target) (*shift-ish '*sar 7 amount target))

(define (*mov source target . maybe-8bit)
  (let ((w-bit (if (null? maybe-8bit) 1 (if (car maybe-8bit) 0 1))))
    (cond
     ((immediate? source)
      (if (register? target)
	  ;; special alternate encoding
	  (list (bitfield 4 #b1011 1 w-bit 3 (reg-num target))
		(imm32-if (= w-bit 1) source))
	  (list (mod-r-m-32 (bitfield 2 3 3 0 2 3 1 w-bit) 0 target)
		(imm32-if (= w-bit 1) source))))
     ((memory? source)
      (cond
       ((and (@imm? source) (register=? target 'eax))
	;; special alternate encoding
	(list (bitfield 7 #b1010000 1 w-bit) (imm32-abs (@imm-address source))))
       ((not (register? target))
	(error "*mov: Cannot have memory source and non-register target" (list source target)))
       (else
	(mod-r-m-32 (bitfield 2 2 3 1 2 1 1 w-bit) target source))))
     ((register? source)
      (cond
       ((and (@imm? target) (register=? source 'eax))
	;; special alternate encoding
	(list (bitfield 7 #b1010001 1 w-bit) (imm32-abs (@imm-address target))))
       ((or (memory? target) (register? target))
	(mod-r-m-32 (bitfield 2 2 3 1 2 0 1 w-bit) source target))
       (else
	(error "*mov: Cannot have register source and non-mem, non-reg target"
	       (list source target)))))
     (else
      (error "*mov: Invalid source" (list source target))))))

(define (*cmov code source target)
  (mod-r-m-32 (list #x0F (bitfield 4 4 4 (condition-code-num code))) target source))

(define (*movz source target) ;; load 8-bit value into 32-bit register with zero-extend
  (mod-r-m-32 (list #x0F #xB6) target source))

(define (*setcc-eax code)
  (list (mod-r-m-32 (list #x0F (bitfield 4 9 4 (condition-code-num code))) 0 'eax)
	(*op 'and 1 'eax)))

(define (*call-or-jmp-like immediate-opcode indirect-mod loc)
  (cond
   ((immediate? loc)
    (list immediate-opcode (imm32-rel loc)))
   ((or (register? loc) (memory? loc))
    (mod-r-m-32 #xFF indirect-mod loc))
   (else
    (error "*call/*jmp: Invalid location" loc))))

(define (*call loc)
  (*call-or-jmp-like #xE8 2 loc))

(define (*jmp loc)
  ;; Short, 8-bit form: (list #xEB loc)
  (*call-or-jmp-like #xE9 4 loc))

(define (*jmp-cc code loc)
  (let ((tttn (condition-code-num code)))
    ;; Short, 8-bit form: (list (bitfield 4 7 4 tttn) loc)
    (list #x0F (bitfield 4 8 4 tttn) (imm32-rel loc))))

(define (*push reg)
  (mod-r-m* 1 2 (reg-num reg)))

(define (*pop reg)
  (mod-r-m* 1 3 (reg-num reg)))

(define (*leave) #xC9)
(define (*ret) #xC3)

(define (*int n) (list #xCD n))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require (only-in racket/list flatten))

(define (unhex-string str) ;; grumble
  (define cleaned (regexp-replace* #rx"[^0-9a-fA-F]+" str ""))
  (for/list [(i (in-range (/ (string-length cleaned) 2)))]
    (string->number (substring cleaned (* i 2) (+ 2 (* i 2))) 16)))

(check-equal? (flatten (*setcc-eax 'ne)) (unhex-string "0f 95 c0 83 e0 01"))
