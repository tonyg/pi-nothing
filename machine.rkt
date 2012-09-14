#lang racket/base

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

(define (assemble md inward-arg-count temp-count instrs)
  ((machine-description-assemble md) inward-arg-count temp-count instrs))
