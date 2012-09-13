#lang racket/base

(require rackunit)

(require "asm-common.rkt")

(provide )

;; PlusMinus is either '+ or '-

;; An Address is one of
;; (@imm Integer)
;; (@reg Register PlusMinus Integer 0) or (@reg Register PlusMinus Register Shift).
(struct @imm (address) #:prefab)
(struct @reg (register op offset shift) #:prefab)

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

(define (@reg-imm? r)
  (and (@reg? r)
       (equal? (@reg-shift r) 0)
       (number? (@reg-offset r))))

(define (@reg-reg? r)
  (and (@reg? r)
       (not (@reg-imm? r))))

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

;; Register Shift -> Number
(define (shift-field r s)
  (bitfield 5 (shift-immediate s)
	    2 (shift-type-code s)
	    1 0
	    4 (reg-num r)))

;; Boolean Condition Register AddressMode -> MachineCode
(define (ldr-or-str load? cc rt am)
  (define p (address-mode->p-bit am))
  (define w (address-mode->w-bit am))
  (define a (address-mode->address am))
  (define u (reg-u a))
  (define op (cond ((@reg-imm? a) 2) ((@reg-reg? a) 3)))
  (imm32 (bitfield 4 (condition-code-num cc)
		   3 op
		   1 (bool->bit p)
		   1 (u-bit u)
		   1 0
		   1 (bool->bit w)
		   1 (bool->bit load?)
		   4 (reg-num (@reg-register a))
		   4 (reg-num rt)
		   12 (if (@reg-imm? a)
			  (@reg-offset a)
			  (shift-field (@reg-offset a) (@reg-shift a))))))

(define (*str cc rt am) (ldr-or-str #f cc rt am))
(define (*ldr cc rt am) (ldr-or-str #t cc rt am))

;;---------------------------------------------------------------------------

(define (spacer)
  (list (imm64 0)
	(imm64 0)))

(require (only-in racket/list flatten))

(let ()
  (define (loads/stores ***)
    (list (*** 'al 'r0 (@reg 'r0 '+ 0 0))
	  (*** 'al 'r0 (@reg 'r0 '- 0 0))
	  (*** 'al 'r0 (@reg 'r0 '+ 'r0 0))
	  (*** 'al 'r0 (@reg 'r0 '- 'r0 0))

	  (*** 'eq 'r1 (@reg 'pc '+ 123 0))
	  (*** 'eq 'r1 (@reg 'pc '- 123 0))

	  (*** 'gt 'r1 (@reg 'r2 '+ 123 0))
	  (*** 'gt 'r1 (@reg 'r2 '- 123 0))
	  (*** 'gt 'r1 (@reg 'r2 '+ #xaaa 0))
	  (*** 'gt 'r1 (@reg 'r2 '- #xaaa 0))

	  (*** 'gt 'r1 (@reg 'r2 '+ 'r3 0))
	  (*** 'gt 'r1 (@reg 'r2 '+ 'r3 1))
	  (*** 'gt 'r1 (@reg 'r2 '+ 'r3 -1))
	  (*** 'gt 'r1 (@reg 'r2 '+ 'r3 (@asr 1)))
	  (*** 'gt 'r1 (@reg 'r2 '+ 'r3 (@ror 1)))
	  (*** 'gt 'r1 (@reg 'r2 '+ 'r3 (@rrx)))

	  (*** 'gt 'r1 (@reg 'r2 '- 'r3 0))
	  (*** 'gt 'r1 (@reg 'r2 '- 'r3 1))
	  (*** 'gt 'r1 (@reg 'r2 '- 'r3 -1))
	  (*** 'gt 'r1 (@reg 'r2 '- 'r3 (@asr 1)))
	  (*** 'gt 'r1 (@reg 'r2 '- 'r3 (@ror 1)))
	  (*** 'gt 'r1 (@reg 'r2 '- 'r3 (@rrx)))))
  (define-values (instrs relocs)
    (internal-link 32
		   imm32*
		   (flatten (list (loads/stores *str)
				  (spacer)
				  (loads/stores *ldr)
				  (spacer)))))
  (write-bytes (list->bytes instrs))
  (void))

;; A division algorithm is a good first test
