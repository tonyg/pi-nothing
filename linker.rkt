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

;; Linking of machine code.

(require (only-in racket/list flatten))
(require racket/match)

(provide (struct-out label-reference)
	 (struct-out label-linker)
	 (struct-out label-anchor)

	 machine-code-length
	 link
	 )

(struct label-reference (name) #:prefab)
(struct label-linker (name width resolver) #:prefab)
(struct label-anchor (name) #:prefab)

(define (machine-code-length x)
  (let loop ((x x)
	     (acc 0))
    (match x
      ['() acc]
      [(cons l r) (loop l (loop r acc))]
      [(? label-anchor?) acc]
      [(? label-linker? ll) (+ acc (label-linker-width ll))]
      [(? bytes? bs) (+ acc (bytes-length bs))]
      [(? number?) (+ acc 1)])))

(define (link raw-bs base-address)
  (define bs (flatten raw-bs))
  (define positions
    (let loop ((i base-address)
	       (bs bs)
	       (acc '()))
      (cond
       ((null? bs) (reverse acc))
       ((label-anchor? (car bs)) (loop i
				       (cdr bs)
				       (cons (cons (car bs) i) acc)))
       ((label-linker? (car bs)) (loop (+ i (label-linker-width (car bs)))
				       (cdr bs)
				       acc))
       ((bytes? (car bs)) (loop (+ i (bytes-length (car bs)))
				(cdr bs)
				acc))
       (else (loop (+ i 1)
		   (cdr bs)
		   acc)))))
  (let loop ((i base-address)
	     (bs bs)
	     (acc '())
	     (relocs '()))
    (cond
     ((null? bs) (values (reverse acc) (reverse relocs) positions))
     ((label-anchor? (car bs)) (loop i (cdr bs) acc relocs))
     ((label-linker? (car bs))
      (define l (car bs))
      (define cell (assoc (label-anchor (label-linker-name l)) positions))
      (define anchor-pos (if cell (cdr cell) i))
      (define delta (- anchor-pos i))
      (define code (flatten ((label-linker-resolver l) delta i)))
      ;; TODO: Iterate to fixpoint in cases where the linker needs to
      ;; change its mind about the length of the generated binary.
      (when (not (= (length code) (label-linker-width l)))
	(error 'link
	       "Generated code ~v does not match promised width ~v"
	       code
	       (label-linker-width l)))
      (loop (+ i (label-linker-width l))
	    (cdr bs)
	    (append (reverse code) acc)
	    (if cell
		relocs
		(cons (cons i (car bs)) relocs))))
     ((bytes? (car bs))
      (loop (+ i (bytes-length (car bs)))
	    (cdr bs)
	    (append (reverse (bytes->list (car bs))) acc)
	    relocs))
     (else (loop (+ i 1)
		 (cdr bs)
		 (cons (car bs) acc)
		 relocs)))))
