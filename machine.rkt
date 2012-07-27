#lang racket/base

(provide (struct-out machine-description)

	 available-regs
	 expand-instructions
	 expand-temporary-loads-and-stores
	 assemble)

(struct machine-description (architecture
			     available-regs
			     expand-instructions
			     expand-temporary-loads-and-stores
			     assemble)
	#:prefab)

(define (available-regs md)
  (machine-description-available-regs md))

(define (expand-instructions md instrs)
  ((machine-description-expand-instructions md) instrs))

(define (expand-temporary-loads-and-stores md instrs)
  ((machine-description-expand-temporary-loads-and-stores md) instrs))

(define (assemble md inward-arg-count instrs)
  ((machine-description-assemble md) inward-arg-count instrs))
