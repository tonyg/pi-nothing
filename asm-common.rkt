#lang racket/base
;; Common definitions for machine-code emission.

(require (only-in racket/list flatten make-list))

(provide (struct-out label-reference)
	 (struct-out label-linker)
	 (struct-out label-anchor)

	 immediate?
	 register=?
	 register?

	 bitfield

	 onebyte-immediate?
	 fourbyte-immediate?
	 shr
	 ror32
	 imm-endianness
	 imm8*
	 imm8
	 imm32*
	 imm32
	 imm32-if
	 imm64*
	 imm64
	 imm64-if

	 round-up-to-nearest
	 internal-link
	 )

(struct label-reference (name) #:prefab)
(struct label-linker (name width resolver) #:prefab)
(struct label-anchor (name) #:prefab)

(define (immediate? x)
  (or (number? x)
      (label-reference? x)))

(define (register=? x y)
  (eq? x y))

(define (register? x)
  (symbol? x))

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

(define (onebyte-immediate? n)
  (and (number? n) (< n 128) (>= n -128)))

(define (fourbyte-immediate? n)
  (and (number? n) (< n #x80000000) (>= n #x-80000000)))

(define (shr v amount)
  (arithmetic-shift v (- amount)))

(define (ror32 v amount0)
  (define amount (modulo amount0 32))
  (bitwise-and #xffffffff
	       (bitwise-ior (bitwise-bit-field v amount 32)
			    (arithmetic-shift (bitwise-bit-field v 0 amount) (- 32 amount)))))

(define imm-endianness (make-parameter 'little))

(define (imm8* i)
  (modulo i 256))

(define (imm8 i)
  (if (label-reference? i)
      (label-linker (label-reference-name i) 1 (lambda (delta i) (imm8* (- delta 1))))
      (imm8* i)))

(define (imm32* i)
  (case (imm-endianness)
    ((little)
     (list (modulo i 256)
	   (modulo (shr i 8) 256)
	   (modulo (shr i 16) 256)
	   (modulo (shr i 24) 256)))
    ((big)
     (list (modulo (shr i 24) 256)
	   (modulo (shr i 16) 256)
	   (modulo (shr i 8) 256)
	   (modulo i 256)))))

(define (imm32 i)
  (if (label-reference? i)
      (label-linker (label-reference-name i) 4 (lambda (delta i) (imm32* (- delta 4))))
      (imm32* i)))

(define (imm32-if test-result i)
  (if test-result (imm32 i) (imm8 i)))

(define (imm64* i)
  (case (imm-endianness)
    ((little)
     (append (imm32* i)
	     (imm32* (shr i 32))))
    ((big)
     (append (imm32* (shr i 32))
	     (imm32* i)))))

(define (imm64 i)
  (if (label-reference? i)
      (label-linker (label-reference-name i) 8 (lambda (delta i) (imm64* (- delta 8))))
      (imm64* i)))

(define (imm64-if test-result i)
  (if test-result (imm64 i) (imm8 i)))

(define (round-up-to-nearest n val)
  (let ((temp (+ val n -1)))
    (- temp (remainder temp n))))

(define (internal-link instrs)
  (define positions
    (let loop ((i 0)
	       (instrs instrs)
	       (acc '()))
      (cond
       ((null? instrs) (reverse acc))
       ((label-anchor? (car instrs)) (loop i
					   (cdr instrs)
					   (cons (cons (car instrs) i) acc)))
       ((label-linker? (car instrs)) (loop (+ i (label-linker-width (car instrs)))
					   (cdr instrs)
					   acc))
       (else (loop (+ i 1)
		   (cdr instrs)
		   acc)))))
  (let loop ((i 0)
	     (instrs instrs)
	     (acc '())
	     (relocs '()))
    (cond
     ((null? instrs) (values (reverse acc) (reverse relocs)))
     ((label-anchor? (car instrs)) (loop i (cdr instrs) acc relocs))
     ((label-linker? (car instrs))
      (define l (car instrs))
      (define cell (assoc (label-anchor (label-linker-name l)) positions))
      (define anchor-pos (if cell (cdr cell) i))
      (define delta (- anchor-pos i))
      (define code (flatten ((label-linker-resolver l) delta i)))
      (when (not (= (length code) (label-linker-width l)))
	(error 'internal-link
	       "Generated code ~v does not match promised width ~v"
	       code
	       (label-linker-width l)))
      (loop (+ i (label-linker-width l))
	    (cdr instrs)
	    (append (reverse code) acc)
	    (if cell
		relocs
		(cons (cons i (car instrs)) relocs))))
     (else (loop (+ i 1) (cdr instrs) (cons (car instrs) acc) relocs)))))
