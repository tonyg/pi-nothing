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

;; Port of linear_intervals.erl by Tony Garnock-Jones

(require racket/match)
(require (only-in racket/list last))

(provide empty-interval
	 full-interval
	 singleton-interval ;; the original supported strings too
	 range-interval
         raw-toggles->interval
	 interval->list
	 interval->list*
	 interval-min
	 interval-max
	 interval-subset?
	 interval-member?
	 interval-empty?
	 interval-invert
	 interval-intersection
	 interval-union
	 interval-symmetric-difference
	 interval-subtract)

(define (empty-interval)
  0)

(define (full-interval)
  -1)

;; TODO: disable
(define-syntax-rule (ensure-positive! what n)
  (when (negative? n) (error 'ensure-positive! "Failed for argument to ~a" what)))

(define (singleton-interval n)
  (ensure-positive! 'singleton-interval n)
  (arithmetic-shift 1 n))

;; Half-open range
(define (range-interval lo hi)
  (ensure-positive! 'range-interval lo)
  (ensure-positive! 'range-interval hi)
  (- (arithmetic-shift 1 hi)
     (arithmetic-shift 1 lo)))

(define (raw-toggles->interval ts [initial #f])
  (when initial (error 'raw-toggles->interval "unsupported"))
  (let loop ((bias 0) (ts ts))
    (match ts
      ['() 0]
      [(list on) (arithmetic-shift -1 (+ bias on))]
      [(list* on off rest) (bitwise-ior (loop off rest) (range-interval on off))])))

(define (nonfinite proc i)
  (error proc "Can only handle finite intervals: ~v" i))

(define (count-low-zeros r)
  (let loop ((r r) (n 0))
    (if (odd? r)
        (values r n)
        (loop (arithmetic-shift r -1) (+ n 1)))))

(define (count-low-ones r)
  (let loop ((r r) (n 0))
    (if (even? r)
        (values r n)
        (loop (arithmetic-shift r -1) (+ n 1)))))

(define (uncons-toggles bias r)
  (if (zero? r)
      '()
      (let-values (((r zero-count) (count-low-zeros r)))
        (if (= r -1)
            (list (+ bias zero-count))
            (let-values (((r one-count) (count-low-ones r)))
              (list* (+ bias zero-count)
                     (+ bias zero-count one-count)
                     r))))))

(define (interval->list i)
  (let loop ((acc '())
             (bias 0)
	     (remaining i))
    (match (uncons-toggles bias remaining)
      ['() (reverse acc)]
      [(list* lo hi rest) (loop (cons (cons lo hi) acc) hi rest)]
      [(list _) (nonfinite 'interval->list i)])))

(define (interval->list* i
                         #:negative-infinity [negative-infinity #f]
                         #:positive-infinity [positive-infinity #f])
  (let loop ((acc '())
             (bias 0)
	     (remaining i))
    (match (uncons-toggles bias remaining)
      ['() (reverse acc)]
      [(list* lo hi rest) (loop (cons (cons lo hi) acc) hi rest)]
      [(list lo) (reverse (cons (cons lo positive-infinity) acc))])))

;; Returns lowest value in the interval
(define (interval-min i)
  (when (zero? i) (nonfinite 'interval-min i))
  (define-values (_i c) (count-low-zeros i))
  c)

;; Returns *lowest* value such that the value and any greater values are not in the interval
(define (interval-max i)
  (when (negative? i) (nonfinite 'interval-max i))
  (integer-length i))

;; Is i1 a subset of i2?
(define (interval-subset? i1 i2)
  (= i1 (bitwise-and i1 i2)))

(define (interval-member? i x)
  (bitwise-bit-set? i x))

(define (interval-empty? i)
  (zero? i))

(define (interval-invert i)
  (bitwise-not i))

(define (interval-intersection i1 i2) (bitwise-and i1 i2))
(define (interval-union i1 i2) (bitwise-ior i1 i2))
(define (interval-symmetric-difference i1 i2) (bitwise-xor i1 i2))
(define (interval-subtract i1 i2) (bitwise-and i1 (bitwise-not i2)))

