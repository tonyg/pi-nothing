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

(require "asm-common.rkt")
(require "linker.rkt")

(provide (all-from-out "asm-common.rkt")
	 (all-defined-out)) ;; TODO

;; A Delta is either Integer or Register or a (@shifted Register Shift).
(struct @shifted (reg shift) #:prefab)

;; PlusMinus is either '+ or '-

;; An Address is a (@reg Register PlusMinus Delta)
(struct @reg (register op delta) #:prefab)

;; A AddressMode is either a plain Address ("offset" addressing), or
;; one of the following:
(struct @pre (address) #:prefab)
(struct @post (address) #:prefab)

;; A Shift can be a signed number, meaning a left or right LOGICAL
;; shift by a constant number of places (negative meaning rightward),
;; a register, meaning a LEFT LOGICAL shift by a variable number of
;; places, or one of the following structs. The n can be a signed
;; number or a register.
(struct @lsr (n) #:prefab) ;; logical shift right; mostly here for shift-by-register
(struct @asr (n) #:prefab)
(struct @ror (n) #:prefab) ;; n must not be 0
(struct @rrx () #:prefab)

(define (@delta-imm? d) (number? d))
(define (@delta-reg? d) (or (register? d) (@shifted? d)))

(define (@delta-reg d)
  (if (register? d)
      d
      (@shifted-reg d)))

(define (@delta-shift d)
  (if (register? d)
      0
      (@shifted-shift d)))

(define (address-mode->address am)
  (cond
   ((@pre? am) (@pre-address am))
   ((@post? am) (@post-address am))
   (else am)))

(define (reg-num reg)
  (case reg
    ((r0) 0)
    ((r1) 1)
    ((r2) 2)
    ((r3) 3)
    ((r4) 4)
    ((r5) 5)
    ((r6) 6)
    ((r7) 7)
    ((r8) 8)
    ((r9) 9)
    ((r10) 10)
    ((r11) 11)
    ((r12) 12)
    ((r13 sp) 13)
    ((r14 lr) 14)
    ((r15 pc) 15)
    (else (error 'reg-num "Invalid register ~v" reg))))

(define (condition-code-num cc)
  (case cc
    ((eq) 0)
    ((ne) 1)
    ((cs hs) 2) ;; hs = unsigned higher or same
    ((cc lo) 3) ;; lo = unsigned lower
    ((mi) 4) ;; negative
    ((pl) 5) ;; zero or positive
    ((vs) 6) ;; overflow
    ((vc) 7) ;; no overflow
    ((hi) 8) ;; unsigned higher
    ((ls) 9) ;; unsigned lower or same
    ((ge) 10) ;; signed
    ((lt) 11) ;; signed
    ((gt) 12) ;; signed
    ((le) 13) ;; signed
    ((al) 14)
    ((nv) 15) ;; plus some other meanings besides "never"
    (else (error 'condition-code-num "Invalid condition-code label ~v" cc))))

(define (bool->bit v)
  (if (boolean? v)
      (if v 1 0)
      v))

(define (u-bit u)
  (case u
    ((1 +) 1)
    ((0 -) 0)
    (else (error 'u-bit "Invalid U-bit value ~v" u))))

;; index = (P == ‘1’);  add = (U == ‘1’);  wback = (P == ‘0’) || (W == ‘1’); 
;; STR<c><q> <Rt>, [<Rn> {, #+/-<imm>}] Offset: index==TRUE, wback==FALSE
;;  - p=1, w=0
;; STR<c><q> <Rt>, [<Rn>, #+/-<imm>]! Pre-indexed: index==TRUE, wback==TRUE 
;;  - p=1, w=1
;; STR<c><q> <Rt>, [<Rn>], #+/-<imm> Post-indexed: index==FALSE, wback==TRUE
;;  - p=0, w=0 (!! if w=1, it's a STRT instead)
;;
;; So p=0 only when post-indexed, and w=1 only when pre-indexed.
(define (address-mode->p-bit a) (if (@post? a) 0 1))
(define (address-mode->w-bit a) (if (@pre? a) 1 0))

(define (reg-u r)
  (case (@reg-op r)
    ((+) 1)
    ((-) 0)))

;; Shift -> Number
(define (shift-type-code s)
  (cond
   ((@lsr? s) 1)
   ((@asr? s) 2)
   ((@ror? s) 3)
   ((@rrx? s) 3)
   ((and (number? s) (negative? s)) 1)
   (else 0))) ;; positive or zero or register

;; Shift -> (U Number Register)
(define (shift-immediate* s)
  (cond ((@lsr? s) (@lsr-n s))
	((@asr? s) (@asr-n s))
	((@ror? s) (@ror-n s))
	((@rrx? s) 0)
	((and (number? s) (negative? s)) (- s))
	(else s)))

;; Shift -> Number
(define (shift-immediate s)
  (define n (shift-immediate* s))
  (if (register? n)
      (bitfield 4 (reg-num n) 1 0)
      n))

;; Shift -> Boolean
(define (shift-by-register? s)
  (register? (shift-immediate* s)))

;; Number -> (Option (Pairof Number Number))
(define (best-rotation* imm0)
  (let loop ((places 0) (imm imm0))
    (cond
     ((= (bitwise-and imm #xff) imm) (cons places imm))
     ((= places 16) #f)
     (else (loop (+ places 1) (ror32 imm -2))))))

;; Number -> Boolean
(define (best-rotation-exists? imm0)
  (best-rotation* imm0))

;; Number -> (Pairof Number Number)
(define (best-rotation imm0)
  (or (best-rotation* imm0)
      (error 'best-rotation "Cannot find suitable rotation for ~v" imm0)))

;; Boolean Delta -> Number
(define (delta-field rotated-immediate? d)
  (if (@delta-imm? d)
      (if rotated-immediate?
	  (let ((r (best-rotation d)))
	    (bitfield 4 (car r) 8 (cdr r)))
	  (bitfield -12 d))
      (bitfield 5 (shift-immediate (@delta-shift d))
		2 (shift-type-code (@delta-shift d))
		1 (bool->bit (shift-by-register? (@delta-shift d)))
		4 (reg-num (@delta-reg d)))))

;; Boolean Boolean Condition Register AddressMode -> MachineCode
(define (ldr-or-str load? byte? cc rt am)
  (define p (address-mode->p-bit am))
  (define w (address-mode->w-bit am))
  (define a (address-mode->address am))
  (define delta (@reg-delta a))
  (define u (reg-u a))
  (imm32* (bitfield 4 (condition-code-num cc)
		    2 1
		    1 (bool->bit (@delta-reg? delta))
		    1 (bool->bit p)
		    1 (u-bit u)
		    1 (bool->bit byte?)
		    1 (bool->bit w)
		    1 (bool->bit load?)
		    4 (reg-num (@reg-register a))
		    4 (reg-num rt)
		    12 (delta-field #f delta))))

(define (*str cc rt am) (ldr-or-str #f #f cc rt am))
(define (*ldr cc rt am) (ldr-or-str #t #f cc rt am))
(define (*strb cc rt am) (ldr-or-str #f #t cc rt am))
(define (*ldrb cc rt am) (ldr-or-str #t #t cc rt am))

(define (reglist->bitmask reglist)
  (cond
   ((null? reglist) 0)
   (else (bitwise-ior (arithmetic-shift 1 (reg-num (car reglist)))
		      (reglist->bitmask (cdr reglist))))))

(define (ldm-or-stm cc before? increment? s writeback? load? rn reglist)
  (imm32* (bitfield 4 (condition-code-num cc)
		    3 4
		    1 (bool->bit before?) ;; P bit
		    1 (bool->bit increment?) ;; U bit
		    1 (bool->bit s)
		    1 (bool->bit writeback?)
		    1 (bool->bit load?) ;; L bit
		    4 (reg-num rn)
		    16 (reglist->bitmask reglist))))

;; PUSH and POP work with Full, Descending stacks: i.e., STMDB and LDMIA
(define (*push cc reglist) (ldm-or-stm cc #t #f 0 #t #f 'sp reglist))
(define (*pop  cc reglist) (ldm-or-stm cc #f #t 0 #t #t 'sp reglist))

;; Flag-setting variant, for use with interrupt/exception handlers
(define (*pops cc reglist) (ldm-or-stm cc #f #t 1 #t #t 'sp reglist))

(define (alu-op opcode cc s rd rn delta)
  (imm32* (bitfield 4 (condition-code-num cc)
		    2 0
		    1 (bool->bit (@delta-imm? delta))
		    4 opcode
		    1 (bool->bit s)
		    4 (reg-num rn)
		    4 (reg-num rd)
		    12 (delta-field #t delta))))

(define (*and cc s rd rn delta) (alu-op  0 cc s  rd  rn delta))
(define (*eor cc s rd rn delta) (alu-op  1 cc s  rd  rn delta))
(define (*sub cc s rd rn delta) (alu-op  2 cc s  rd  rn delta))
(define (*rsb cc s rd rn delta) (alu-op  3 cc s  rd  rn delta))
(define (*add cc s rd rn delta) (alu-op  4 cc s  rd  rn delta))
(define (*adc cc s rd rn delta) (alu-op  5 cc s  rd  rn delta))
(define (*sbc cc s rd rn delta) (alu-op  6 cc s  rd  rn delta))
(define (*rsc cc s rd rn delta) (alu-op  7 cc s  rd  rn delta))
(define (*tst cc      rn delta) (alu-op  8 cc 1 'r0  rn delta))
(define (*teq cc      rn delta) (alu-op  9 cc 1 'r0  rn delta))
(define (*cmp cc      rn delta) (alu-op 10 cc 1 'r0  rn delta))
(define (*cmn cc      rn delta) (alu-op 11 cc 1 'r0  rn delta))
(define (*orr cc s rd rn delta) (alu-op 12 cc s  rd  rn delta))
(define (*mov cc s rd    delta) (alu-op 13 cc s  rd 'r0 delta))
(define (*bic cc s rd rn delta) (alu-op 14 cc s  rd  rn delta))
(define (*mvn cc s rd    delta) (alu-op 15 cc s  rd 'r0 delta))

(define (*mul cc s rd rn rm)
  (imm32* (bitfield 4 (condition-code-num cc)
		    7 0
		    1 (bool->bit s)
		    4 (reg-num rd)
		    4 0
		    4 (reg-num rm)
		    4 9
		    4 (reg-num rn))))

;; NB re +8: branch instruction assembly treats PC as being *the same
;; as the branch instruction's address*, i.e. the assembler
;; automatically compensates for the +8.

;; See note re +8 above.
(define (b-or-bl cc link? loc)
  (if (label-reference? loc)
      (label-linker (label-reference-name loc)
		    4
		    (lambda (delta i)
		      (b-or-bl* cc link? delta)))
      (b-or-bl* cc link? loc)))

;; See note re +8 above.
(define (b-or-bl* cc link? imm24)
  (when (not (zero? (bitwise-and imm24 3)))
    (error 'b-or-bl*
	   "Immediate PC-relative branch target offset must be a multiple of 4: ~v" imm24))
  (imm32* (bitfield 4 (condition-code-num cc)
		    3 5
		    1 (bool->bit link?)
		    -24 (shr (- imm24 8) 2)))) ;; -8 because it's (pc+8)-relative

;; See note re +8 above.
(define (*b cc loc) (b-or-bl cc #f loc))
;; See note re +8 above.
(define (*bl cc loc) (b-or-bl cc #t loc))

(define (*blx cc rm)
  (imm32* (bitfield 4 (condition-code-num cc)
		    8 #b00010010
		    4 15
		    4 15
		    4 15
		    4 #b0011
		    4 (reg-num rm))))

(define (*clz cc rd rm)
  (imm32* (bitfield 4 (condition-code-num cc)
		    8 #b00010110
		    4 15
		    4 (reg-num rd)
		    4 15
		    4 1
		    4 (reg-num rm))))

;; System modes
(define arm-mode-user		#x10)
(define arm-mode-fiq		#x11)
(define arm-mode-irq		#x12)
(define arm-mode-supervisor	#x13) ;; aka SVC mode; the CPU boots into this mode
(define arm-mode-abort		#x17)
(define arm-mode-undefined	#x1b)
(define arm-mode-system		#x1f)

;; CPSR/SPSR -> register
(define (*mrs cc spsr? rd)
  (imm32* (bitfield 4 (condition-code-num cc)
		    5 2
		    1 (bool->bit spsr?) ;; 1 = SPSR, 0 = CPSR
		    2 0
		    4 15
		    4 (reg-num rd)
		    12 0)))

;; register/immediate -> CPSR/SPSR
(define (*msr cc spsr? fields rm-or-imm)
  (when (null? fields)
    (error '*msr "No field flags supplied"))
  (imm32* (bitfield 4 (condition-code-num cc)
		    2 0
		    1 (bool->bit (not (register? rm-or-imm)))
		    2 2
		    1 (bool->bit spsr?) ;; 1 = SPSR, 0 = CPSR
		    2 2
		    1 (bool->bit (and (memq 'f fields) #t))
		    1 (bool->bit (and (memq 's fields) #t))
		    1 (bool->bit (and (memq 'x fields) #t))
		    1 (bool->bit (and (memq 'c fields) #t))
		    4 15
		    12 (if (register? rm-or-imm)
			   (bitfield 4 0
				     4 0
				     4 (reg-num rm-or-imm))
			   (let ((r (best-rotation rm-or-imm)))
			     (bitfield 4 (car r) 8 (cdr r)))))))

(define (*cps enable-or-disable flags mode)
  (when (and (eq? enable-or-disable #f) (eq? mode #f))
    (error '*cps "Must either enable or disable some flag bits, or set a mode"))
  (imm32* (bitfield 4 15
		    8 #b00010000
		    2 (case enable-or-disable
			((enable) 2)
			((disable) 3)
			((#f) 0)
			(else (error '*cps
				     "Invalid value for enable-or-disable: ~v" enable-or-disable)))
		    1 (if mode 1 0)
		    1 0
		    7 0
		    1 (bool->bit (and (memq 'a flags) #t))
		    1 (bool->bit (and (memq 'i flags) #t))
		    1 (bool->bit (and (memq 'f flags) #t))
		    1 0
		    5 (or mode 0))))

(define (*swi cc num)
  (imm32* (bitfield 4 (condition-code-num cc)
		    4 15
		    24 num)))
