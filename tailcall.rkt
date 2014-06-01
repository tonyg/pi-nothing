#lang racket/base
;; Calling convention supporting reasonably-efficient tail calls.
;; See http://www.eighty-twenty.org/index.cgi/tech/arm-tail-calling-convention-20121127.html

;; (Originated with the ARM backend, hence the ARM-centricity of the
;; following text.)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The ARM procedure call standard (AAPCS) specifies a convention for
;; using the stack pointer suitable for C-like linkage. Because our
;; setup includes tail calls, we can't quite use it unmodified. So
;; here's what we do instead.
;;
;;  - We keep our stack Full Descending, just like AAPCS.
;;  - We ensure it is 8-byte aligned at all times, just like (a slight
;;    restriction of) AAPCS.
;;  - We make outbound arguments leftmost-low, that is, "pushed from
;;    right to left". This makes us compatible with naive C struct
;;    overlaying of memory.
;;  - Furthermore, we ensure argument 0 in memory is also 8-byte
;;    aligned.
;;
;;  - We do NOT move the stack pointer down over outbound arguments.
;;    Instead, the callee moves the stack pointer as they see fit.
;;    This is totally different to AAPCS. The reason for this is so
;;    that the callee can tail-call someone else without having to do
;;    any hairy adjusting of the frame, and so that the original
;;    caller doesn't have to know anything about what's left to clean
;;    up when they receive control: all the clean-up has already been
;;    completed.
;;
;;  - This bears stating again: just after return from a subroutine,
;;    all clean-up has already been completed.
;;
;; So, with that all out of the way, stack frames need to account for
;;  - inward args (numbered 4 and above; 0-3 are transmitted in
;;    registers)
;;  - space for extra args supplied to tail calls
;;  - saved temporaries
;;  - being aligned to the nearest frame-alignment byte boundary
;;
;; Stacks are full descending.
;;  - Ni = inward-arg-count, the number of arguments we expect
;;  - No = most-tail-args, the largest number of outbound tail args we produce
;;  - Nt = inward-temp-count, the number of temps we require
;;  - Na = outward-arg-count, the current number of arguments we are producing
;;
;; Upon entry to a subroutine, Ni=5, No=7, Nt=3, Na=3:
;;
;;   (low)                                                               (high)
;;       | outbound  |   |   temps   |   |shuffle|      inbound      |
;;       | 0 | 1 | 2 |---| 0 | 1 | 2 |---| - | - | 0 | 1 | 2 | 3 | 4 |---|
;;                       ^                                               ^
;;                     sp for non-leaf                                sp for leaf
;;
;; Note that the first four arguments are transferred in registers,
;; but that stack slots still need to be reserved. Note also the
;; padding after the outbound regs, the temps, and the
;; inbound/shuffle-space.
;;
;; The extra shuffle slots are only required if there's no room in the
;; inbound slots plus padding. For example, if Ni=5 and No=6, then
;; since we expect the inbound arguments to have one slot of padding,
;; that slot can be used as shuffle space.
;;
;; Leaf procedures do NOT move the stack pointer on entry. Nonleaf
;; procedures DO move the stack pointer on entry. This means we have
;; different addressing calculations depending on whether we're a leaf
;; or nonleaf procedure.
;;
;; Pad8(x) = x rounded up to the nearest multiple of 8
;; sp_delta = Pad8(No * 4) + Pad8(Nt * 4), distance SP might move on entry and exit
;;
;; Leaf procedures:
;;   SP does not move
;;   inward(n) = rn, if n < 4
;;             | sp - Pad8(Ni * 4) + (n * 4)
;;   temp(n) = sp - sp_delta + (n * 4)
;;   outward(n) (tail calls only) = rn, if n < 4
;;                                | sp - Pad8(Na * 4) + (n * 4)
;;
;; Nonleaf procedures:
;;   SP moves by sp_delta
;;   inward(n) = rn, if n < 4
;;             | sp + sp_delta - Pad8(Ni * 4) + (n * 4)
;;   temp(n) = sp + (n * 4)
;;   outward(n) (non-tail calls) = rn, if n < 4
;;                               | sp - Pad8(Na * 4) + (n * 4)
;;   outward(n) (tail calls) = rn, if n < 4
;;                           | sp + sp_delta - Pad8(Na * 4) + (n * 4)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require racket/match)

(require "lir.rkt")
(require (only-in "linker.rkt" label-reference))
(require (only-in "asm-common.rkt" round-up-to-nearest))

(provide (struct-out calling-convention)
	 argument-passed-in-register?
	 inward-argument-location
	 outward-argument-location
	 compute-sp-delta
	 make-location-resolver)

(struct calling-convention (argument-regs ;; (Listof Register)
			    stack-slots-for-argument-regs ;; Natural, count of words
			    sp-relative-location ;; (Integer -> Location)
			    word-size ;; Natural, count of bytes
			    frame-alignment ;; Natural, count of bytes
			    linkage-size ;; Natural, count of bytes
			    entry-linkage-padding ;; Natural, count of bytes
			    ) #:prefab)

(define (reg-arg-count cc)
  (length (calling-convention-argument-regs cc)))

(define (arg-stack-index-offset cc)
  (- (reg-arg-count cc)
     (calling-convention-stack-slots-for-argument-regs cc)))

(define (argument-passed-in-register? cc i)
  (< i (reg-arg-count cc)))

(define ((inward-argument-location cc) i)
  (if (argument-passed-in-register? cc i)
      (preg (list-ref (calling-convention-argument-regs cc) i))
      (inward-arg (- i (arg-stack-index-offset cc)))))

(define ((outward-argument-location cc) calltype count i)
  (if (argument-passed-in-register? cc i)
      (preg (list-ref (calling-convention-argument-regs cc) i))
      (outward-arg calltype count (- i (arg-stack-index-offset cc)))))

(define (frame-pad-words cc n)
  (round-up-to-nearest (calling-convention-frame-alignment cc)
		       (* n (calling-convention-word-size cc))))

(define (frame-pad-argc cc n)
  (define o (arg-stack-index-offset cc))
  (if (< n o) 0 (frame-pad-words cc (- n o))))

(define (compute-sp-delta cc most-tail-args temp-count)
  (+ (frame-pad-argc cc most-tail-args)
     (frame-pad-words cc temp-count)))

(define (make-location-resolver cc inward-arg-count most-tail-args temp-count leaf?)
  (define sp-delta (compute-sp-delta cc most-tail-args temp-count))
  (define word-size (calling-convention-word-size cc))
  (define leaf-pad (calling-convention-entry-linkage-padding cc))
  (define sprel (calling-convention-sp-relative-location cc))
  (lambda (v)
    (match v
      [(lit n) n]
      [(label tag) (label-reference tag)]
      [(preg r) r]
      [(temporary n)
       (if leaf?
	   (sprel (- (* n word-size) sp-delta leaf-pad))
	   (sprel (* n word-size)))]
      [(inward-arg n)
       (if leaf?
	   (sprel (- (- (* n word-size) (frame-pad-argc cc inward-arg-count)) leaf-pad))
	   (sprel (+ (- (* n word-size) (frame-pad-argc cc inward-arg-count)) sp-delta)))]
      [(outward-arg 'nontail outward-arg-count n)
       (if leaf?
	   (error 'make-location-resolver "Nontail call in leaf procedure")
	   (sprel (- (- (* n word-size) (frame-pad-argc cc outward-arg-count))
		     (calling-convention-linkage-size cc))))]
      [(outward-arg 'tail outward-arg-count n)
       (if leaf?
	   (sprel (- (- (* n word-size) (frame-pad-argc cc outward-arg-count)) leaf-pad))
	   (sprel (+ (- (* n word-size) (frame-pad-argc cc outward-arg-count)) sp-delta)))]
      )))

(module+ test
  (require rackunit)

  (define ((make-expect-loc cc) inward-arg-count most-tail-args temp-count leaf? v expected)
    (check-equal? ((make-location-resolver cc inward-arg-count most-tail-args temp-count leaf?) v)
		  expected
		  (list 'expect-loc inward-arg-count most-tail-args temp-count leaf? v)))

  (let () ;; ARM calling conventions
    (local-require "asm-arm7.rkt")
    (define cc (calling-convention '(r0 r1 r2 r3)
				   4
				   (lambda (delta)
				     (@reg 'sp
					   (if (negative? delta) '- '+)
					   (if (negative? delta) (- delta) delta)))
				   4
				   8
				   0
				   0))
    (define expect-loc (make-expect-loc cc))

    ;; Non-leaf procedures

    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 7 0) 'r0)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 7 1) 'r1)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 7 2) 'r2)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 7 3) 'r3)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 7 4) (@reg 'sp '+ 32))
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 7 5) (@reg 'sp '+ 36))
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 7 6) (@reg 'sp '+ 40))

    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 2 0) 'r0)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 2 1) 'r1)

    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 5 4) (@reg 'sp '+ 40))
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'tail 6 5) (@reg 'sp '+ 44))

    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 2 0) 'r0)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 2 1) 'r1)

    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 5 4) (@reg 'sp '- 8))
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 6 5) (@reg 'sp '- 4))

    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 7 0) 'r0)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 7 1) 'r1)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 7 2) 'r2)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 7 3) 'r3)
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 7 4) (@reg 'sp '- 16))
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 7 5) (@reg 'sp '- 12))
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 7 6) (@reg 'sp '- 8))

    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 8 7) (@reg 'sp '- 4))
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 69 68) (@reg 'sp '- 8))
    (expect-loc 5 7 3 #f ((outward-argument-location cc) 'nontail 70 69) (@reg 'sp '- 4))

    (expect-loc 5 7 3 #f (temporary 0) (@reg 'sp '+ 0))
    (expect-loc 5 7 3 #f (temporary 1) (@reg 'sp '+ 4))
    (expect-loc 5 7 3 #f (temporary 2) (@reg 'sp '+ 8))
    (expect-loc 5 7 4 #f (temporary 0) (@reg 'sp '+ 0))
    (expect-loc 5 7 4 #f (temporary 1) (@reg 'sp '+ 4))
    (expect-loc 5 7 4 #f (temporary 2) (@reg 'sp '+ 8))
    (expect-loc 5 7 4 #f (temporary 3) (@reg 'sp '+ 12))

    (expect-loc 5 7 3 #f ((inward-argument-location cc) 0) 'r0)
    (expect-loc 5 7 3 #f ((inward-argument-location cc) 1) 'r1)
    (expect-loc 5 7 3 #f ((inward-argument-location cc) 2) 'r2)
    (expect-loc 5 7 3 #f ((inward-argument-location cc) 3) 'r3)
    (expect-loc 5 7 3 #f ((inward-argument-location cc) 4) (@reg 'sp '+ 40))

    ;; Leaf procedures

    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 7 0) 'r0)
    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 7 1) 'r1)
    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 7 2) 'r2)
    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 7 3) 'r3)
    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 7 4) (@reg 'sp '- 16))
    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 7 5) (@reg 'sp '- 12))
    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 7 6) (@reg 'sp '- 8))

    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 2 0) 'r0)
    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 2 1) 'r1)

    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 5 4) (@reg 'sp '- 8))
    (expect-loc 5 7 3 #t ((outward-argument-location cc) 'tail 6 5) (@reg 'sp '- 4))

    (check-exn #px"Nontail call in leaf procedure"
	       (lambda ()
		 (expect-loc 5 7 3 #t ((outward-argument-location cc) 'nontail 7 5) '???)))

    (expect-loc 5 7 3 #t (temporary 0) (@reg 'sp '- 48))
    (expect-loc 5 7 3 #t (temporary 1) (@reg 'sp '- 44))
    (expect-loc 5 7 3 #t (temporary 2) (@reg 'sp '- 40))
    (expect-loc 5 7 4 #t (temporary 0) (@reg 'sp '- 48))
    (expect-loc 5 7 4 #t (temporary 1) (@reg 'sp '- 44))
    (expect-loc 5 7 4 #t (temporary 2) (@reg 'sp '- 40))
    (expect-loc 5 7 4 #t (temporary 3) (@reg 'sp '- 36))

    (expect-loc 5 7 3 #t ((inward-argument-location cc) 0) 'r0)
    (expect-loc 5 7 3 #t ((inward-argument-location cc) 1) 'r1)
    (expect-loc 5 7 3 #t ((inward-argument-location cc) 2) 'r2)
    (expect-loc 5 7 3 #t ((inward-argument-location cc) 3) 'r3)
    (expect-loc 5 7 3 #t ((inward-argument-location cc) 4) (@reg 'sp '- 8))

    )
  )
