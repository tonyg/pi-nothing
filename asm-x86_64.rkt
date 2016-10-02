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

(require "asm-x86-common.rkt")
(require "linker.rkt")

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
	 *setcc-rax
	 *call
	 *jmp
	 *jmp-cc
	 *push
	 *pop
	 *lea
	 *rol
	 *ror
	 *shl
	 *shr
	 *sar

	 *leave
	 *ret

	 *syscall
	 *sysret

	 *sqrtsd
	 *addsd
	 *mulsd
	 *subsd
	 *minsd
	 *divsd
	 *maxsd

	 *movsd
	 *comisd
	 *ucomisd
	 *cvtsd2si
	 *cvtsi2sd
	 )

(define regs '((rax 0)
	       (rcx 1)
	       (rdx 2)
	       (rbx 3)
	       (rsp 4)
	       (rbp 5)
	       (rsi 6)
	       (rdi 7)
	       (r8 8)
	       (r9 9)
	       (r10 10)
	       (r11 11)
	       (r12 12)
	       (r13 13)
	       (r14 14)
	       (r15 15)
	       (rip rip-relative)
	       (xmm0 0)
	       (xmm1 1)
	       (xmm2 2)
	       (xmm3 3)
	       (xmm4 4)
	       (xmm5 5)
	       (xmm6 6)
	       (xmm7 7)
	       (xmm8 8)
	       (xmm9 9)
	       (xmm10 10)
	       (xmm11 11)
	       (xmm12 12)
	       (xmm13 13)
	       (xmm14 14)
	       (xmm15 15)))

(define (reg-num reg)
  (cond
   ((assq reg regs) => cadr)
   (else (error 'reg-num "Invalid register ~v" reg))))

(define (mod-r-m-64 opcodes reg modrm)
  (mod-r-m #t 1 reg-num opcodes reg modrm))

(define (*op opcode source target)
  (let ((opcode (arithmetic-opcode opcode)))
    (cond
     ((immediate? source)
      (let ((s-bit (if (onebyte-immediate? source) 1 0)))
	(if (and (register=? target 'rax) (not (onebyte-immediate? source)))
	    (list (rex reg-num 1 0 0 0)
		  (bitfield 2 0 3 opcode 2 2 1 1)
		  (imm32* source))
	    (list (mod-r-m-64 (bitfield 2 2 3 0 1 0 1 s-bit 1 1) opcode target)
		  (imm32-if (not (onebyte-immediate? source)) source)))))
     ((memory? source)
      (cond
       ((not (register? target))
	(error '*op "~v: Cannot have memory source ~v and non-register target ~v"
	       opcode source target))
       (else
	(mod-r-m-64 (bitfield 2 0 3 opcode 2 1 1 1) target source))))
     ((register? source)
      (cond
       ((or (memory? target) (register? target))
	(mod-r-m-64 (bitfield 2 0 3 opcode 2 0 1 1) source target))
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
    (list (mod-r-m-64 (if (onebyte-immediate? source) #x6B #x69) target target)
	  (imm32-if (not (onebyte-immediate? source)) source)))
   (else ;; memory or register source
    (mod-r-m-64 (list #x0F #xAF) target source))))

(define (*not target)
  (mod-r-m-64 #xF7 2 target))

;; Unsigned multiply -- yields RDX:RAX
(define (*mul multiplicand)
  (mod-r-m-64 #xF7 4 multiplicand))

;; Signed multiply -- yields RDX:RAX
(define (*imul/extended multiplicand)
  (mod-r-m-64 #xF7 5 multiplicand))

(define (*div divisor)
  (mod-r-m-64 #xF7 6 divisor))

(define (*inc target)
  (mod-r-m-64 #xFF 0 target))

(define (*shift-ish name subop amount target)
  (cond
   ((immediate? amount)
    (list (mod-r-m-64 #xC1 subop target) amount))
   ((eq? amount 'rcx)
    (mod-r-m-64 #xD3 subop target))
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
      (if (and (register? target) (not (fourbyte-immediate? source)))
	  ;; special alternate encoding
	  (list (if (= w-bit 1) (rex reg-num 1 0 0 target) '())
		(bitfield 4 #b1011 1 w-bit 3 (bitwise-and 7 (reg-num target)))
		(imm64-if (= w-bit 1) source))
	  (list (mod-r-m-64 (bitfield 2 3 3 0 2 3 1 w-bit) 0 target)
		(imm32-if (= w-bit 1) source))))
     ((memory? source)
      (cond
       ((and (@imm? source) (not (or (label-reference? (@imm-address source))
                                     (fourbyte-immediate? (@imm-address source)))))
	(if (register=? target 'rax)
	    ;; special alternate encoding
	    (list (rex reg-num 1 0 0 0)
		  (bitfield 7 #b1010000 1 w-bit)
		  (imm64* (@imm-address source)))
	    (error "*mov: Cannot move 64-bit direct into non-rax register" (list source target))))
       ((not (register? target))
	(error "*mov: Cannot have memory source and non-register target" (list source target)))
       (else
	(mod-r-m-64 (bitfield 2 2 3 1 2 1 1 w-bit) target source))))
     ((register? source)
      (cond
       ((and (@imm? target) (not (fourbyte-immediate? (@imm-address target))))
	(if (register=? source 'rax)
	    ;; special alternate encoding
	    (list (rex reg-num 1 0 0 0)
		  (bitfield 7 #b1010001 1 w-bit)
		  (imm64* (@imm-address target)))
	    (error "*mov: Cannot move non-rax register into 64-bit direct" (list source target))))
       ((or (memory? target) (register? target))
	(mod-r-m-64 (bitfield 2 2 3 1 2 0 1 w-bit) source target))
       (else
	(error "*mov: Cannot have register source and non-mem, non-reg target"
	       (list source target)))))
     (else
      (error "*mov: Invalid source" (list source target))))))

(define (*cmov code source target)
  (mod-r-m-64 (list #x0F (bitfield 4 4 4 (condition-code-num code))) target source))

(define (*movz source target) ;; load 8-bit value into 64-bit register with zero-extend
  (mod-r-m-64 (list #x0F #xB6) target source))

(define (*setcc-rax code)
  (list (list #x0F (bitfield 4 9 4 (condition-code-num code)) (mod-r-m* 3 0 0))
	(*op 'and 1 'rax)))

(define (*call-or-jmp-like immediate-opcode indirect-mod loc)
  (cond
   ((immediate? loc)
    (list immediate-opcode (imm32-rel loc)))
   ((or (register? loc) (memory? loc))
    (mod-r-m-64 #xFF indirect-mod loc))
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

(define (*lea loc reg)
  (mod-r-m-64 #x8D reg loc))

(define (*leave) #xC9)
(define (*ret) #xC3)

;; rcx <- rip following the syscall; r11 <- saved flags
;; the msr IA32_LSTAR is the target of the syscall
;; the complement of IA32_FMASK (msr C0000084) is anded with RFLAGS during this instr
;; the CS and SS selectors are loaded from IA32_STAR_MSR
(define (*syscall) (list #x0F #x05))

;; rip <- rcx
;; RFLAGS <- r11
;; CS and SS from IA32_STAR_MSR
;; gas calls this instruction variant (with its REX prefix) "sysretq".
;; The non-REX variant it calls "sysretl".
(define (*sysret) (list (rex reg-num 1 0 0 0) #x0F #x07))

;;---------------------------------------------------------------------------
;; SSE2 floating point

(define (mod-r-m-sse opcodes reg modrm)
  (mod-r-m #t 0 reg-num opcodes reg modrm))

(define (sse-sd-op prefix op reg modrm)
  (list prefix (mod-r-m-sse (list #x0F op) reg modrm)))

;;        movmskpd??                            #x50
(define (*sqrtsd source target) (sse-sd-op #xF2 #x51 target source))
;;        rsqrtsd absent (rsqrtss only)         #x52
;;        rcpsd absent (rcpss only)             #x53
;;        andsd??                               #x54
;;        andnsd??                              #x55
;;        orsd??                                #x56
;;        xorsd??                               #x57
(define (*addsd source target)  (sse-sd-op #xF2 #x58 target source))
(define (*mulsd source target)  (sse-sd-op #xF2 #x59 target source))
;;        cvtsd2ss                              #x5A
;;        cvtdq2sd??                            #x5B
(define (*subsd source target)  (sse-sd-op #xF2 #X5C target source))
(define (*minsd source target)  (sse-sd-op #xF2 #x5D target source))
(define (*divsd source target)  (sse-sd-op #xF2 #x5E target source))
(define (*maxsd source target)  (sse-sd-op #xF2 #x5F target source))

(define (*movsd source target)
  (if (memory? target)
      (if (memory? source)
	  (error '*movsd "Cannot move double from memory to memory")
	  (sse-sd-op #xF2 #x11 source target))
      (sse-sd-op #xF2 #x10 target source)))

;; As always, comparison is based on the sign of (target - source).
;; If target - source is positive, the "greater-than" bits will be set.
;; For *comisd and *ucomisd, source may refer to memory.
(define (*ucomisd source target) (sse-sd-op #x66 #x2E target source))
(define (*comisd source target) (sse-sd-op #x66 #x2F target source))

;; N.B.: these always load/store 64 bits worth of integer.
;; Variations exist that load/store 32 bits worth, but they are not implemented here.
(define (*cvtsd2si source target) (list #xF2 (mod-r-m-64 (list #x0F #x2D) target source)))
(define (*cvtsi2sd source target) (list #xF2 (mod-r-m-64 (list #x0F #x2A) target source)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require "test-utils.rkt")

  (check-encoding-equal? (*setcc-rax 'ne) "0f 95 c0 48 83 e0 01")

  (check-encoding-equal? (*mov 'rcx 'rbx) "48 89 cb")
  (check-encoding-equal? (*mov 'rbx 'r8) "49 89 d8")
  (check-encoding-equal? (*mov 'r11 'rax) "4c 89 d8")
  (check-encoding-equal? (*mov 'r11 'r15) "4d 89 df")

  (check-encoding-equal? (*op 'add 10 'rax) "48 83 c0 0a")
  (check-encoding-equal? (*op 'add 1000000000 'rax) "48 05 00 ca 9a 3b")
  (check-encoding-equal? (*op 'xor 10 'rax) "48 83 f0 0a")
  (check-encoding-equal? (*op 'xor 1000000000 'rax) "48 35 00 ca 9a 3b")

  (check-encoding-equal? (*op 'add 10 'r15) "49 83 c7 0a")
  (check-encoding-equal? (*op 'add 1000000000 'r15) "49 81 c7 00 ca 9a 3b")
  (check-encoding-equal? (*op 'xor 10 'r15) "49 83 f7 0a")
  (check-encoding-equal? (*op 'xor 1000000000 'r15) "49 81 f7 00 ca 9a 3b")

  (check-encoding-equal? (*op 'add (@imm 10) 'r13) "4c 03 2c 25 0a 00 00 00")
  (check-encoding-equal? (*op 'add 10 (@reg 'rbp 0)) "48 83 45 00 0a")
  (check-encoding-equal? (*op 'add 10 (@reg 'r13 0)) "49 83 45 00 0a")
  (check-encoding-equal? (*op 'add 10 (@reg 'r15 0)) "49 83 07 0a")
  (check-encoding-equal? (*op 'add 10 (@reg 'rbp 8)) "48 83 45 08 0a")
  (check-encoding-equal? (*op 'add 10 (@reg 'r13 8)) "49 83 45 08 0a")
  (check-encoding-equal? (*op 'add 10 (@reg 'r15 8)) "49 83 47 08 0a")

  (check-encoding-equal? (*op 'add (@imm 10) 'r15) "4c 03 3c 25 0a 00 00 00")
  (check-encoding-equal? (*op 'add (@imm 1000000000) 'r15) "4c 03 3c 25 00 ca 9a 3b")
  (check-encoding-equal? (*op 'xor (@imm 10) 'r15) "4c 33 3c 25 0a 00 00 00")
  (check-encoding-equal? (*op 'xor (@imm 1000000000) 'r15) "4c 33 3c 25 00 ca 9a 3b")

  (check-encoding-equal? (*op 'add 'rax 'r15) "49 01 c7")
  (check-encoding-equal? (*op 'add 'r15 'rax) "4c 01 f8")
  (check-encoding-equal? (*op 'add 'rbx 'r15) "49 01 df")
  (check-encoding-equal? (*op 'add 'r15 'rbx) "4c 01 fb")
  (check-encoding-equal? (*op 'add 'rcx 'rbx) "48 01 cb")
  (check-encoding-equal? (*op 'add 'r14 'r15) "4d 01 f7")

  (check-encoding-equal? (*mov 'r15 (@reg 'rbp -8)) "4c 89 7d f8")

  (check-encoding-equal? (*mov #x123456789a 'rax) "48 b8 9a 78 56 34 12 00 00 00")
  (check-encoding-equal? (*mov #x123456789a 'rdx) "48 ba 9a 78 56 34 12 00 00 00")
  (check-encoding-equal? (*mov #x123456789a 'r11) "49 bb 9a 78 56 34 12 00 00 00")
  (check-encoding-equal? (*mov (@imm #x123456789a) 'rax) "48 a1 9a 78 56 34 12 00 00 00")
  (check-encoding-equal? (*mov (@imm #x12345678) 'rax) "48 8b 04 25 78 56 34 12")
  (check-encoding-equal? (*mov (@imm #x12345678) 'rdx) "48 8b 14 25 78 56 34 12")
  (check-encoding-equal? (*mov (@imm #x12345678) 'r11) "4c 8b 1c 25 78 56 34 12")

  (check-encoding-equal? (*mov 'rax (@imm #x123456789a)) "48 a3 9a 78 56 34 12 00 00 00")
  (check-encoding-equal? (*mov 'rax (@imm #x12345678)) "48 89 04 25 78 56 34 12")
  (check-encoding-equal? (*mov 'rdx (@imm #x12345678)) "48 89 14 25 78 56 34 12")
  (check-encoding-equal? (*mov 'r11 (@imm #x12345678)) "4c 89 1c 25 78 56 34 12")

  (check-encoding-equal? (*op 'cmp 'rax 'rbx) "48 39 c3")
  (check-encoding-equal? (*op 'cmp 'rbx 'rax) "48 39 d8")
  (check-encoding-equal? (*op 'cmp 1 'rbx) "48 83 fb 01")

  (check-encoding-equal? (*lea (@reg 'rax 16) 'rbx) "48 8d 58 10")
  (check-encoding-equal? (*lea (@reg 'rax 0) 'rbx) "48 8d 18")
  (check-encoding-equal? (*lea (@reg 'rax -16) 'rbx) "48 8d 58 f0")
  (check-encoding-equal? (*lea (@reg 'r11 16) 'rbx) "49 8d 5b 10")
  (check-encoding-equal? (*lea (@reg 'r11 0) 'rbx) "49 8d 1b")
  (check-encoding-equal? (*lea (@reg 'r11 -16) 'rbx) "49 8d 5b f0")
  (check-encoding-equal? (*lea (@reg 'r13 16) 'rbx) "49 8d 5d 10")
  (check-encoding-equal? (*lea (@reg 'r13 0) 'rbx) "49 8d 5d 00")
  (check-encoding-equal? (*lea (@reg 'r13 -16) 'rbx) "49 8d 5d f0")

  (check-encoding-equal? (*lea (@reg 'rax 16) 'r13) "4c 8d 68 10")
  (check-encoding-equal? (*lea (@reg 'rax 0) 'r13) "4c 8d 28")
  (check-encoding-equal? (*lea (@reg 'rax -16) 'r13) "4c 8d 68 f0")
  (check-encoding-equal? (*lea (@reg 'r11 16) 'r13) "4d 8d 6b 10")
  (check-encoding-equal? (*lea (@reg 'r11 0) 'r13) "4d 8d 2b")
  (check-encoding-equal? (*lea (@reg 'r11 -16) 'r13) "4d 8d 6b f0")
  (check-encoding-equal? (*lea (@reg 'r13 16) 'r13) "4d 8d 6d 10")
  (check-encoding-equal? (*lea (@reg 'r13 0) 'r13) "4d 8d 6d 00")
  (check-encoding-equal? (*lea (@reg 'r13 -16) 'r13) "4d 8d 6d f0")

  (check-encoding-equal? (*lea (@reg 'rbp 16) 'r13) "4c 8d 6d 10")
  (check-encoding-equal? (*lea (@reg 'rbp 0) 'r13) "4c 8d 6d 00")
  (check-encoding-equal? (*lea (@reg 'rbp -16) 'r13) "4c 8d 6d f0")

  (check-encoding-equal? (*lea (@reg 'rsp 16) 'rbx) "48 8d 5c 24 10")
  (check-encoding-equal? (*lea (@reg 'rsp 0) 'rbx) "48 8d 1c 24")
  (check-encoding-equal? (*lea (@reg 'rsp -16) 'rbx) "48 8d 5c 24 f0")
  (check-encoding-equal? (*lea (@reg 'rsp 16) 'rsp) "48 8d 64 24 10")
  (check-encoding-equal? (*lea (@reg 'rsp 0) 'rsp) "48 8d 24 24")
  (check-encoding-equal? (*lea (@reg 'rsp -16) 'rsp) "48 8d 64 24 f0")
  (check-encoding-equal? (*lea (@reg 'rsp 16) 'rbp) "48 8d 6c 24 10")
  (check-encoding-equal? (*lea (@reg 'rsp 0) 'rbp) "48 8d 2c 24")
  (check-encoding-equal? (*lea (@reg 'rsp -16) 'rbp) "48 8d 6c 24 f0")
  (check-encoding-equal? (*lea (@reg 'rsp 16) 'r13) "4c 8d 6c 24 10")
  (check-encoding-equal? (*lea (@reg 'rsp 0) 'r13) "4c 8d 2c 24")
  (check-encoding-equal? (*lea (@reg 'rsp -16) 'r13) "4c 8d 6c 24 f0")

  (check-encoding-equal? (*lea (@reg 'rip 16) 'rbx) "48 8d 1d 10 00 00 00")
  (check-encoding-equal? (*lea (@reg 'rip 0) 'rbx) "48 8d 1d 00 00 00 00")
  (check-encoding-equal? (*lea (@reg 'rip -16) 'rbx) "48 8d 1d f0 ff ff ff")
  (check-encoding-equal? (*lea (@reg 'rip 16) 'r13) "4c 8d 2d 10 00 00 00")
  (check-encoding-equal? (*lea (@reg 'rip 0) 'r13) "4c 8d 2d 00 00 00 00")
  (check-encoding-equal? (*lea (@reg 'rip -16) 'r13) "4c 8d 2d f0 ff ff ff")

  (check-encoding-equal? (*rol 3 'rax) "48 c1 c0 03")
  (check-encoding-equal? (*rol 'rcx 'rax) "48 d3 c0")
  (check-encoding-equal? (*rol 3 (@reg 'rax 16)) "48 c1 40 10 03")
  (check-encoding-equal? (*rol 'rcx (@reg 'rax 16)) "48 d3 40 10")

  (check-encoding-equal? (*ror 3 'rax) "48 c1 c8 03")
  (check-encoding-equal? (*ror 'rcx 'rax) "48 d3 c8")
  (check-encoding-equal? (*ror 3 (@reg 'rax 16)) "48 c1 48 10 03")
  (check-encoding-equal? (*ror 'rcx (@reg 'rax 16)) "48 d3 48 10")

  (check-encoding-equal? (*shl 3 'rax) "48 c1 e0 03")
  (check-encoding-equal? (*shl 'rcx 'rax) "48 d3 e0")
  (check-encoding-equal? (*shl 3 (@reg 'rax 16)) "48 c1 60 10 03")
  (check-encoding-equal? (*shl 'rcx (@reg 'rax 16)) "48 d3 60 10")

  (check-encoding-equal? (*shr 3 'rax) "48 c1 e8 03")
  (check-encoding-equal? (*shr 'rcx 'rax) "48 d3 e8")
  (check-encoding-equal? (*shr 3 (@reg 'rax 16)) "48 c1 68 10 03")
  (check-encoding-equal? (*shr 'rcx (@reg 'rax 16)) "48 d3 68 10")

  (check-encoding-equal? (*sar 3 'rax) "48 c1 f8 03")
  (check-encoding-equal? (*sar 'rcx 'rax) "48 d3 f8")
  (check-encoding-equal? (*sar 3 (@reg 'rax 16)) "48 c1 78 10 03")
  (check-encoding-equal? (*sar 'rcx (@reg 'rax 16)) "48 d3 78 10")

  (check-encoding-equal? (*addsd 'xmm1 'xmm0) "f2 0f 58 c1")
  (check-encoding-equal? (*addsd 'xmm0 'xmm1) "f2 0f 58 c8")
  (check-encoding-equal? (*addsd 'xmm11 'xmm0) "f2 41 0f 58 c3")
  (check-encoding-equal? (*addsd 'xmm0 'xmm11) "f2 44 0f 58 d8")
  (check-encoding-equal? (*addsd 'xmm11 'xmm10) "f2 45 0f 58 d3")
  (check-encoding-equal? (*addsd 'xmm10 'xmm11) "f2 45 0f 58 da")

  (check-encoding-equal? (*addsd (@reg 'rax 0) 'xmm0) "f2 0f 58 00")
  (check-encoding-equal? (*addsd (@reg 'rax 1000) 'xmm0) "f2 0f 58 80 e8 03 00 00")
  (check-encoding-equal? (*addsd (@imm #x11223344) 'xmm0) "f2 0f 58 04 25 44 33 22 11")
  (check-encoding-equal? (*addsd (@imm #x11223344) 'xmm11) "f2 44 0f 58 1c 25 44 33 22 11")
  (check-encoding-equal? (*addsd (@reg 'r15 1000) 'xmm0) "f2 41 0f 58 87 e8 03 00 00")
  (check-encoding-equal? (*addsd (@reg 'r15 1000) 'xmm11) "f2 45 0f 58 9f e8 03 00 00")

  (check-encoding-equal? (*sqrtsd 'xmm12 'xmm11) "f2 45 0f 51 dc")
  (check-encoding-equal? (*addsd  'xmm12 'xmm11) "f2 45 0f 58 dc")
  (check-encoding-equal? (*mulsd  'xmm12 'xmm11) "f2 45 0f 59 dc")
  (check-encoding-equal? (*subsd  'xmm12 'xmm11) "f2 45 0f 5c dc")
  (check-encoding-equal? (*minsd  'xmm12 'xmm11) "f2 45 0f 5d dc")
  (check-encoding-equal? (*divsd  'xmm12 'xmm11) "f2 45 0f 5e dc")
  (check-encoding-equal? (*maxsd  'xmm12 'xmm11) "f2 45 0f 5f dc")

  (check-encoding-equal? (*movsd 'xmm0 'xmm1) "f2 0f 10 c8")
  (check-encoding-equal? (*movsd (@reg 'rax 1000) 'xmm1) "f2 0f 10 88 e8 03 00 00")
  (check-encoding-equal? (*movsd 'xmm1 (@reg 'rax 1000)) "f2 0f 11 88 e8 03 00 00")

  (check-encoding-equal? (*ucomisd 'xmm0 'xmm1) "66 0f 2e c8")
  (check-encoding-equal? (*ucomisd (@reg 'rax 0) 'xmm0) "66 0f 2e 00")
  (check-encoding-equal? (*ucomisd (@reg 'rax 1000) 'xmm11) "66 44 0f 2e 98 e8 03 00 00")

  (check-encoding-equal? (*comisd 'xmm0 'xmm1) "66 0f 2f c8")
  (check-encoding-equal? (*comisd (@reg 'rax 0) 'xmm0) "66 0f 2f 00")
  (check-encoding-equal? (*comisd (@reg 'rax 1000) 'xmm11) "66 44 0f 2f 98 e8 03 00 00")

  (check-encoding-equal? (*cvtsd2si (@reg 'rax 0) 'rax) "f2 48 0f 2d 00")
  (check-encoding-equal? (*cvtsd2si 'xmm0 'rax) "f2 48 0f 2d c0")
  (check-encoding-equal? (*cvtsd2si 'xmm11 'rax) "f2 49 0f 2d c3")

  (check-encoding-equal? (*cvtsd2si (@reg 'rax 0) 'rbp) "f2 48 0f 2d 28")
  (check-encoding-equal? (*cvtsd2si (@reg 'rbp 0) 'rbp) "f2 48 0f 2d 6d 00")
  (check-encoding-equal? (*cvtsd2si 'xmm11 'rbp) "f2 49 0f 2d eb")
  (check-encoding-equal? (*cvtsd2si 'xmm11 'r14) "f2 4d 0f 2d f3")

  (check-encoding-equal? (*cvtsd2si (@reg 'rax 0) 'r14) "f2 4c 0f 2d 30")
  (check-encoding-equal? (*cvtsd2si (@reg 'rbp 0) 'r14) "f2 4c 0f 2d 75 00")

  (check-encoding-equal? (*cvtsi2sd (@reg 'rax 0) 'xmm3) "f2 48 0f 2a 18")
  (check-encoding-equal? (*cvtsi2sd (@reg 'rax 1000) 'xmm3) "f2 48 0f 2a 98 e8 03 00 00")
  (check-encoding-equal? (*cvtsi2sd 'rax 'xmm3) "f2 48 0f 2a d8")
  (check-encoding-equal? (*cvtsi2sd 'rbp 'xmm11) "f2 4c 0f 2a dd")
  (check-encoding-equal? (*cvtsi2sd 'r14 'xmm11) "f2 4d 0f 2a de")

  (check-encoding-equal? (*cvtsi2sd (@reg 'rax 0) 'xmm11) "f2 4c 0f 2a 18")
  (check-encoding-equal? (*cvtsi2sd (@reg 'rbp 0) 'xmm11) "f2 4c 0f 2a 5d 00")
  )
