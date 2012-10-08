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

(provide (struct-out machine-description)

	 available-regs
	 inward-argument-location
	 outward-argument-location
	 expand-instructions
	 expand-temporary-loads-and-stores
	 assemble)

(struct machine-description (architecture
			     word-size-bytes
			     word-ctype
			     available-regs
			     inward-argument-location
			     outward-argument-location
			     expand-instructions
			     expand-temporary-loads-and-stores
			     assemble)
	#:prefab)

(define (available-regs md)
  (machine-description-available-regs md))

(define (inward-argument-location md i)
  ((machine-description-inward-argument-location md) i))

(define (outward-argument-location md calltype count i)
  ((machine-description-outward-argument-location md) calltype count i))

(define (expand-instructions md init-arg-instrs instrs)
  ((machine-description-expand-instructions md) init-arg-instrs instrs))

(define (expand-temporary-loads-and-stores md instrs)
  ((machine-description-expand-temporary-loads-and-stores md) instrs))

(define (assemble md inward-arg-count temp-count leaf? instrs)
  ((machine-description-assemble md) inward-arg-count temp-count leaf? instrs))
