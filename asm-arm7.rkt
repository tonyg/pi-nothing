#lang racket/base

(require rackunit)

(require "asm-common.rkt")

(provide (all-from-out "asm-common.rkt")
	 (all-defined-out)) ;; TODO

;; TODO: register-shifted-register Deltas

;; A Delta is either Integer or Register or a (@shifted Register Shift).
(struct @shifted (reg shift) #:prefab)

;; PlusMinus is either '+ or '-

;; An Address is one of
;; (@imm Integer)
;; (@reg Register PlusMinus Delta)
(struct @imm (address) #:prefab)
(struct @reg (register op delta) #:prefab)

;; A AddressMode is either a plain Address ("offset" addressing), or
;; one of the following:
(struct @pre (address) #:prefab)
(struct @post (address) #:prefab)

;; A Shift can be a signed number, meaning a left or right LOGICAL
;; shift by a constant number of places (negative meaning rightward),
;; or one of the following structs:
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
   ((@asr? s) 2)
   ((@ror? s) 3)
   ((@rrx? s) 3)
   ((negative? s) 1)
   (else 0))) ;; positive or zero

;; Shift -> Number
(define (shift-immediate s)
  (cond
   ((@asr? s) (@asr-n s))
   ((@ror? s) (@ror-n s))
   ((@rrx? s) 0)
   ((negative? s) (- s))
   (else s)))

;; Number -> (Option (Pairof Number Number))
(define (best-rotation imm0)
  (let loop ((places 0) (imm imm0))
    (cond
     ((= (bitwise-and imm #xff) imm) (cons places imm))
     ((= places 16) (error 'best-rotation "Cannot find suitable rotation for ~v" imm0))
     (else (loop (+ places 1) (ror32 imm -2))))))

;; Boolean Delta -> Number
(define (delta-field rotated-immediate? d)
  (if (@delta-imm? d)
      (if rotated-immediate?
	  (let ((r (best-rotation d)))
	    (bitfield 4 (car r) 8 (cdr r)))
	  (bitfield 12 d))
      (bitfield 5 (shift-immediate (@delta-shift d))
		2 (shift-type-code (@delta-shift d))
		1 0
		4 (reg-num (@delta-reg d)))))

;; Boolean Condition Register AddressMode -> MachineCode
(define (ldr-or-str load? cc rt am)
  (define p (address-mode->p-bit am))
  (define w (address-mode->w-bit am))
  (define a (address-mode->address am))
  (define delta (@reg-delta a))
  (define u (reg-u a))
  (imm32 (bitfield 4 (condition-code-num cc)
		   2 1
		   1 (bool->bit (@delta-reg? delta))
		   1 (bool->bit p)
		   1 (u-bit u)
		   1 0
		   1 (bool->bit w)
		   1 (bool->bit load?)
		   4 (reg-num (@reg-register a))
		   4 (reg-num rt)
		   12 (delta-field #f delta))))

(define (*str cc rt am) (ldr-or-str #f cc rt am))
(define (*ldr cc rt am) (ldr-or-str #t cc rt am))

(define (alu-op opcode cc s rd rn delta)
  (imm32 (bitfield 4 (condition-code-num cc)
		   2 0
		   1 (bool->bit (@delta-imm? delta))
		   4 opcode
		   1 (bool->bit s)
		   4 (reg-num rn)
		   4 (reg-num rd)
		   12 (delta-field #t delta))))

(define (*and cc s rd rn delta) (alu-op 0 cc s rd rn delta))
(define (*eor cc s rd rn delta) (alu-op 1 cc s rd rn delta))
(define (*sub cc s rd rn delta) (alu-op 2 cc s rd rn delta))
(define (*rsb cc s rd rn delta) (alu-op 3 cc s rd rn delta))
(define (*add cc s rd rn delta) (alu-op 4 cc s rd rn delta))
(define (*adc cc s rd rn delta) (alu-op 5 cc s rd rn delta))
(define (*sbc cc s rd rn delta) (alu-op 6 cc s rd rn delta))
(define (*rsc cc s rd rn delta) (alu-op 7 cc s rd rn delta))

(define (*cmp cc      rn delta) (alu-op 10 cc 1 'r0 rn delta))

(define (*orr cc s rd rn delta) (alu-op 12 cc s rd rn delta))
(define (*mov cc s rd    delta) (alu-op 13 cc s rd 'r0 delta))
(define (*bic cc s rd rn delta) (alu-op 14 cc s rd rn delta))
(define (*mvn cc s rd    delta) (alu-op 15 cc s rd 'r0 delta))

(define (*mul cc s rd rn rm)
  (imm32 (bitfield 4 (condition-code-num cc)
		   7 0
		   1 (bool->bit s)
		   4 (reg-num rd)
		   4 0
		   4 (reg-num rm)
		   4 9
		   4 (reg-num rn))))

(define (b-or-bl cc link? imm24)
  (when (not (zero? (bitwise-and imm24 3)))
    (error '*b "Immediate PC-relative branch target offset must be a multiple of 4: ~v" imm24))
  (imm32 (bitfield 4 (condition-code-num cc)
		   3 5
		   1 (bool->bit link?)
		   -24 (shr imm24 2))))

(define (*b cc imm24) (b-or-bl cc #f imm24))
(define (*bl cc imm24) (b-or-bl cc #t imm24))

(define (internal-link-32 instrs)
  (internal-link 4 imm32* instrs))

;;---------------------------------------------------------------------------

(define (spacer)
  (list (imm64 0)
	(imm64 0)))

(require (only-in racket/list flatten))

(let ()
  (define (loads/stores ***)
    (list (*** 'al 'r0 (@reg 'r0 '+ 0))
	  (*** 'al 'r0 (@reg 'r0 '- 0))
	  (*** 'al 'r0 (@reg 'r0 '+ 'r0))
	  (*** 'al 'r0 (@reg 'r0 '- 'r0))

	  (*** 'eq 'r1 (@reg 'pc '+ 123))
	  (*** 'eq 'r1 (@reg 'pc '- 123))

	  (*** 'gt 'r1 (@reg 'r2 '+ #x0ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #x1ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #x2ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #x3ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #x4ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #x5ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #x6ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #x7ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #x8ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #x9ff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #xaff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #xbff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #xcff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #xdff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #xeff))
	  (*** 'gt 'r1 (@reg 'r2 '+ #xfff))

	  (*** 'gt 'r1 (@reg 'r2 '+ 123))
	  (*** 'gt 'r1 (@reg 'r2 '- 123))
	  (*** 'gt 'r1 (@reg 'r2 '+ #xaaa))
	  (*** 'gt 'r1 (@reg 'r2 '- #xaaa))

	  (*** 'gt 'r1 (@reg 'r2 '+ 'r3))
	  (*** 'gt 'r1 (@reg 'r2 '+ (@shifted 'r3 1)))
	  (*** 'gt 'r1 (@reg 'r2 '+ (@shifted 'r3 -1)))
	  (*** 'gt 'r1 (@reg 'r2 '+ (@shifted 'r3 (@asr 1))))
	  (*** 'gt 'r1 (@reg 'r2 '+ (@shifted 'r3 (@ror 1))))
	  (*** 'gt 'r1 (@reg 'r2 '+ (@shifted 'r3 (@rrx))))

	  (*** 'gt 'r1 (@reg 'r2 '- (@shifted 'r3 0)))
	  (*** 'gt 'r1 (@reg 'r2 '- (@shifted 'r3 1)))
	  (*** 'gt 'r1 (@reg 'r2 '- (@shifted 'r3 -1)))
	  (*** 'gt 'r1 (@reg 'r2 '- (@shifted 'r3 (@asr 1))))
	  (*** 'gt 'r1 (@reg 'r2 '- (@shifted 'r3 (@ror 1))))
	  (*** 'gt 'r1 (@reg 'r2 '- (@shifted 'r3 (@rrx))))))
  (define-values (instrs relocs)
    (internal-link-32
     (flatten
      (list
       ;; (loads/stores *str)
       ;; (spacer)

       ;; (loads/stores *ldr)
       ;; (spacer)

       ;; (*mov 'lt 1 'r6 #x000000ff)
       ;; ;;(*mov 'lt 1 'r6 #x000001ff) -- too wide
       ;; ;;(*mov 'lt 1 'r6 #x000001fe) -- single-bit rotation doesn't fit
       ;; (*mov 'lt 1 'r6 #x000003fc)
       ;; (*mov 'lt 1 'r6 #x00000ff0)
       ;; (*mov 'lt 1 'r6 #x003fc000)
       ;; (*mov 'lt 1 'r6 #x00ff0000)
       ;; (*mov 'lt 1 'r6 #xf000000f)
       ;; (spacer)

       ;; (*mov 'ne 0 'r9 123)
       ;; ;;(*mov 'ne 1 'r9 #xaaa) -- too wide
       ;; (*mov 'ne 0 'r9 'r8)
       ;; (*mov 'ne 1 'r9 (@shifted 'r8 1))
       ;; (*mov 'ne 0 'r9 (@shifted 'r8 -1))
       ;; (*mov 'ne 1 'r9 (@shifted 'r8 (@asr 1)))
       ;; (*mov 'ne 0 'r9 (@shifted 'r8 (@ror 1)))
       ;; (*mov 'ne 1 'r9 (@shifted 'r8 (@rrx)))
       ;; (spacer)

       ;; (*add 'lt 1 'r6 'r11 #x00000ff0)
       ;; (*add 'lt 1 'r6 'r11 #x003fc000)
       ;; (*add 'ne 0 'r9 'r11 123)
       ;; ;; (*add 'ne 1 'r9 'r11 #xaaa) -- too wide
       ;; (*add 'ne 0 'r9 'r11 'r8)
       ;; (*add 'ne 1 'r9 'r11 (@shifted 'r8 1))
       ;; (*add 'ne 0 'r9 'r11 (@shifted 'r8 -1))
       ;; (*add 'ne 1 'r9 'r11 (@shifted 'r8 (@asr 1)))
       ;; (*add 'ne 0 'r9 'r11 (@shifted 'r8 (@ror 1)))
       ;; (*add 'ne 1 'r9 'r11 (@shifted 'r8 (@rrx)))
       ;; (spacer)

       ;; (*b 'al 0)
       ;; (*b 'gt -256)
       ;; (*b 'nv 256)
       ;; (spacer)

       ;; (*bl 'al 0)
       ;; (*bl 'gt -256)
       ;; (*bl 'nv 8)
       ;; (spacer)

       ;; (*b 'al -8)
       ;; (*b 'gt -8)
       ;; (*b 'nv -8)
       ;; (spacer)

       ;; (*cmp 'al 'r0 'r1)
       ;; (*cmp 'al 'r3 'r4)
       ;; (*cmp 'al 'r5 (@shifted 'r8 2))

       ;; (*mul 'al 0 'r0 'r1 'r2)
       ;; (spacer)

       ;; (*ldr 'al 'r0 (@reg 'pc '+ 12)) ;; + 16 - 8 = 8
       ;; (*mov 'al 0 'r1 65) ;; ASCII for capital A
       ;; (*str 'al 'r1 (@reg 'r0 '+ 0)) ;; r1 into r0
       ;; (*add 'al 0 'r1 'r1 1) ;; increment byte
       ;; (*b 'al -16)
       ;; (imm32 #x101f1000) ;; UART0

       (*ldr 'al 'r0 (@reg 'pc '+ 0)) ;; + 16 - 8 = 8
       (*b 'al 0)
       (imm32 #x101f1000) ;; UART0

       (*mov 'al 0 'r2 0)

       (*add 'al 0 'r1 'r2 65) ;; ASCII for capital A
       (*str 'al 'r1 (@reg 'r0 '+ 0))	     ;; r1 into r0
       (*add 'al 0 'r2 'r2 1)		     ;; increment byte
       (*and 'al 0 'r2 'r2 31)		     ;; truncate
       (*b 'al (* (- -4 2) 4))

       ))))
  (write-bytes (list->bytes instrs))
  (void))

;; A division algorithm is a good first test

;; 0x101f1000 is UART0 on versatilepb
