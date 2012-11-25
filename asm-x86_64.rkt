#lang racket/base
;; Copyright (C) 2012 Tony Garnock-Jones <tonygarnockjones@gmail.com>
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
	 *div
	 *inc
	 *mov
	 *cmov
	 *setcc-rax
	 *call
	 *jmp
	 *jmp-cc
	 *push
	 *pop
	 *lea

	 *leave
	 *ret

	 *syscall
	 *sysret
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
	       (rip rip-relative)))

(define (reg-num reg)
  (cond
   ((assq reg regs) => cadr)
   (else (error 'reg-num "Invalid register ~v" reg))))

(define (mod-r-m-64 opcodes reg modrm)
  (mod-r-m #t reg-num opcodes reg modrm))

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

;; Unsigned multiply
(define (*mul multiplicand)
  (mod-r-m-64 #xF7 4 multiplicand))

(define (*div divisor)
  (mod-r-m-64 #xF7 6 divisor))

(define (*inc target)
  (mod-r-m-64 #xFF 0 target))

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
       ((and (@imm? source) (not (fourbyte-immediate? (@imm-address source))))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require (only-in racket/list flatten))

(define (unhex-string str) ;; grumble
  (define cleaned (regexp-replace* #rx"[^0-9a-fA-F]+" str ""))
  (for/list [(i (in-range (/ (string-length cleaned) 2)))]
    (string->number (substring cleaned (* i 2) (+ 2 (* i 2))) 16)))

(check-equal? (flatten (*setcc-rax 'ne)) (unhex-string "0f 95 c0 48 83 e0 01"))

(check-equal? (flatten (*mov 'rcx 'rbx)) (unhex-string "48 89 cb"))
(check-equal? (flatten (*mov 'rbx 'r8)) (list #x49 #x89 #xd8))
(check-equal? (flatten (*mov 'r11 'rax)) (list #x4c #x89 #xd8))
(check-equal? (flatten (*mov 'r11 'r15)) (list #x4d #x89 #xdf))

(check-equal? (flatten (*op 'add 10 'rax)) (unhex-string "48 83 c0 0a"))
(check-equal? (flatten (*op 'add 1000000000 'rax)) (unhex-string "48 05 00 ca 9a 3b"))
(check-equal? (flatten (*op 'xor 10 'rax)) (unhex-string "48 83 f0 0a"))
(check-equal? (flatten (*op 'xor 1000000000 'rax)) (unhex-string "48 35 00 ca 9a 3b"))

(check-equal? (flatten (*op 'add 10 'r15)) (unhex-string "49 83 c7 0a"))
(check-equal? (flatten (*op 'add 1000000000 'r15)) (unhex-string "49 81 c7 00 ca 9a 3b"))
(check-equal? (flatten (*op 'xor 10 'r15)) (unhex-string "49 83 f7 0a"))
(check-equal? (flatten (*op 'xor 1000000000 'r15)) (unhex-string "49 81 f7 00 ca 9a 3b"))

(check-equal? (flatten (*op 'add (@imm 10) 'r13)) (unhex-string "4c 03 2c 25 0a 00 00 00"))
(check-equal? (flatten (*op 'add 10 (@reg 'rbp 0))) (unhex-string "48 83 45 00 0a"))
(check-equal? (flatten (*op 'add 10 (@reg 'r13 0))) (unhex-string "49 83 45 00 0a"))
(check-equal? (flatten (*op 'add 10 (@reg 'r15 0))) (unhex-string "49 83 07 0a"))
(check-equal? (flatten (*op 'add 10 (@reg 'rbp 8))) (unhex-string "48 83 45 08 0a"))
(check-equal? (flatten (*op 'add 10 (@reg 'r13 8))) (unhex-string "49 83 45 08 0a"))
(check-equal? (flatten (*op 'add 10 (@reg 'r15 8))) (unhex-string "49 83 47 08 0a"))

(check-equal? (flatten (*op 'add (@imm 10) 'r15)) (unhex-string "4c 03 3c 25 0a 00 00 00"))
(check-equal? (flatten (*op 'add (@imm 1000000000) 'r15)) (unhex-string "4c 03 3c 25 00 ca 9a 3b"))
(check-equal? (flatten (*op 'xor (@imm 10) 'r15)) (unhex-string "4c 33 3c 25 0a 00 00 00"))
(check-equal? (flatten (*op 'xor (@imm 1000000000) 'r15)) (unhex-string "4c 33 3c 25 00 ca 9a 3b"))

(check-equal? (flatten (*op 'add 'rax 'r15)) (unhex-string "49 01 c7"))
(check-equal? (flatten (*op 'add 'r15 'rax)) (unhex-string "4c 01 f8"))
(check-equal? (flatten (*op 'add 'rbx 'r15)) (unhex-string "49 01 df"))
(check-equal? (flatten (*op 'add 'r15 'rbx)) (unhex-string "4c 01 fb"))
(check-equal? (flatten (*op 'add 'rcx 'rbx)) (unhex-string "48 01 cb"))
(check-equal? (flatten (*op 'add 'r14 'r15)) (unhex-string "4d 01 f7"))

(check-equal? (flatten (*mov 'r15 (@reg 'rbp -8))) (unhex-string "4c 89 7d f8"))

(check-equal? (flatten (*mov #x123456789a 'rax)) (unhex-string "48 b8 9a 78 56 34 12 00 00 00"))
(check-equal? (flatten (*mov #x123456789a 'rdx)) (unhex-string "48 ba 9a 78 56 34 12 00 00 00"))
(check-equal? (flatten (*mov #x123456789a 'r11)) (unhex-string "49 bb 9a 78 56 34 12 00 00 00"))
(check-equal? (flatten (*mov (@imm #x123456789a) 'rax)) (unhex-string "48 a1 9a 78 56 34 12 00 00 00"))
(check-equal? (flatten (*mov (@imm #x12345678) 'rax)) (unhex-string "48 8b 04 25 78 56 34 12"))
(check-equal? (flatten (*mov (@imm #x12345678) 'rdx)) (unhex-string "48 8b 14 25 78 56 34 12"))
(check-equal? (flatten (*mov (@imm #x12345678) 'r11)) (unhex-string "4c 8b 1c 25 78 56 34 12"))

(check-equal? (flatten (*mov 'rax (@imm #x123456789a))) (unhex-string "48 a3 9a 78 56 34 12 00 00 00"))
(check-equal? (flatten (*mov 'rax (@imm #x12345678))) (unhex-string "48 89 04 25 78 56 34 12"))
(check-equal? (flatten (*mov 'rdx (@imm #x12345678))) (unhex-string "48 89 14 25 78 56 34 12"))
(check-equal? (flatten (*mov 'r11 (@imm #x12345678))) (unhex-string "4c 89 1c 25 78 56 34 12"))

(check-equal? (flatten (*op 'cmp 'rax 'rbx)) (unhex-string "48 39 c3"))
(check-equal? (flatten (*op 'cmp 'rbx 'rax)) (unhex-string "48 39 d8"))
(check-equal? (flatten (*op 'cmp 1 'rbx)) (unhex-string "48 83 fb 01"))

(check-equal? (flatten (*lea (@reg 'rax 16) 'rbx)) (unhex-string "48 8d 58 10"))
(check-equal? (flatten (*lea (@reg 'rax 0) 'rbx)) (unhex-string "48 8d 18"))
(check-equal? (flatten (*lea (@reg 'rax -16) 'rbx)) (unhex-string "48 8d 58 f0"))
(check-equal? (flatten (*lea (@reg 'r11 16) 'rbx)) (unhex-string "49 8d 5b 10"))
(check-equal? (flatten (*lea (@reg 'r11 0) 'rbx)) (unhex-string "49 8d 1b"))
(check-equal? (flatten (*lea (@reg 'r11 -16) 'rbx)) (unhex-string "49 8d 5b f0"))
(check-equal? (flatten (*lea (@reg 'r13 16) 'rbx)) (unhex-string "49 8d 5d 10"))
(check-equal? (flatten (*lea (@reg 'r13 0) 'rbx)) (unhex-string "49 8d 5d 00"))
(check-equal? (flatten (*lea (@reg 'r13 -16) 'rbx)) (unhex-string "49 8d 5d f0"))

(check-equal? (flatten (*lea (@reg 'rax 16) 'r13)) (unhex-string "4c 8d 68 10"))
(check-equal? (flatten (*lea (@reg 'rax 0) 'r13)) (unhex-string "4c 8d 28"))
(check-equal? (flatten (*lea (@reg 'rax -16) 'r13)) (unhex-string "4c 8d 68 f0"))
(check-equal? (flatten (*lea (@reg 'r11 16) 'r13)) (unhex-string "4d 8d 6b 10"))
(check-equal? (flatten (*lea (@reg 'r11 0) 'r13)) (unhex-string "4d 8d 2b"))
(check-equal? (flatten (*lea (@reg 'r11 -16) 'r13)) (unhex-string "4d 8d 6b f0"))
(check-equal? (flatten (*lea (@reg 'r13 16) 'r13)) (unhex-string "4d 8d 6d 10"))
(check-equal? (flatten (*lea (@reg 'r13 0) 'r13)) (unhex-string "4d 8d 6d 00"))
(check-equal? (flatten (*lea (@reg 'r13 -16) 'r13)) (unhex-string "4d 8d 6d f0"))

(check-equal? (flatten (*lea (@reg 'rbp 16) 'r13)) (unhex-string "4c 8d 6d 10"))
(check-equal? (flatten (*lea (@reg 'rbp 0) 'r13)) (unhex-string "4c 8d 6d 00"))
(check-equal? (flatten (*lea (@reg 'rbp -16) 'r13)) (unhex-string "4c 8d 6d f0"))

(check-equal? (flatten (*lea (@reg 'rsp 16) 'rbx)) (unhex-string "48 8d 5c 24 10"))
(check-equal? (flatten (*lea (@reg 'rsp 0) 'rbx)) (unhex-string "48 8d 1c 24"))
(check-equal? (flatten (*lea (@reg 'rsp -16) 'rbx)) (unhex-string "48 8d 5c 24 f0"))
(check-equal? (flatten (*lea (@reg 'rsp 16) 'rsp)) (unhex-string "48 8d 64 24 10"))
(check-equal? (flatten (*lea (@reg 'rsp 0) 'rsp)) (unhex-string "48 8d 24 24"))
(check-equal? (flatten (*lea (@reg 'rsp -16) 'rsp)) (unhex-string "48 8d 64 24 f0"))
(check-equal? (flatten (*lea (@reg 'rsp 16) 'rbp)) (unhex-string "48 8d 6c 24 10"))
(check-equal? (flatten (*lea (@reg 'rsp 0) 'rbp)) (unhex-string "48 8d 2c 24"))
(check-equal? (flatten (*lea (@reg 'rsp -16) 'rbp)) (unhex-string "48 8d 6c 24 f0"))
(check-equal? (flatten (*lea (@reg 'rsp 16) 'r13)) (unhex-string "4c 8d 6c 24 10"))
(check-equal? (flatten (*lea (@reg 'rsp 0) 'r13)) (unhex-string "4c 8d 2c 24"))
(check-equal? (flatten (*lea (@reg 'rsp -16) 'r13)) (unhex-string "4c 8d 6c 24 f0"))

(check-equal? (flatten (*lea (@reg 'rip 16) 'rbx)) (unhex-string "48 8d 1d 10 00 00 00"))
(check-equal? (flatten (*lea (@reg 'rip 0) 'rbx)) (unhex-string "48 8d 1d 00 00 00 00"))
(check-equal? (flatten (*lea (@reg 'rip -16) 'rbx)) (unhex-string "48 8d 1d f0 ff ff ff"))
(check-equal? (flatten (*lea (@reg 'rip 16) 'r13)) (unhex-string "4c 8d 2d 10 00 00 00"))
(check-equal? (flatten (*lea (@reg 'rip 0) 'r13)) (unhex-string "4c 8d 2d 00 00 00 00"))
(check-equal? (flatten (*lea (@reg 'rip -16) 'r13)) (unhex-string "4c 8d 2d f0 ff ff ff"))
