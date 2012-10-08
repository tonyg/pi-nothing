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

;; Common definitions for machine-code emission.

(require (only-in racket/list flatten make-list))
(require "linker.rkt")

(provide immediate?
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
	 imm32-rel
	 imm32-abs
	 imm32-if
	 imm64*
	 imm64-rel
	 imm64-abs
	 imm64-if

	 round-up-to-nearest
	 )

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

(define (imm32-rel i)
  (if (label-reference? i)
      (label-linker (label-reference-name i) 4 (lambda (delta i) (imm32* (- delta 4))))
      (imm32* i)))

(define (imm32-abs i)
  (if (label-reference? i)
      (label-linker (label-reference-name i) 4 (lambda (delta i) (imm32* (+ delta i))))
      (imm32* i)))

(define (imm32-if test-result i)
  (if test-result (imm32-abs i) (imm8 i)))

(define (imm64* i)
  (case (imm-endianness)
    ((little)
     (append (imm32* i)
	     (imm32* (shr i 32))))
    ((big)
     (append (imm32* (shr i 32))
	     (imm32* i)))))

(define (imm64-rel i)
  (if (label-reference? i)
      (label-linker (label-reference-name i) 8 (lambda (delta i) (imm64* (- delta 8))))
      (imm64* i)))

(define (imm64-abs i)
  (if (label-reference? i)
      (label-linker (label-reference-name i) 8 (lambda (delta i) (imm64* (+ delta i))))
      (imm64* i)))

(define (imm64-if test-result i)
  (if test-result (imm64-abs i) (imm8 i)))

(define (round-up-to-nearest n val)
  (let ((temp (+ val n -1)))
    (- temp (remainder temp n))))
