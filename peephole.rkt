#lang racket/base

(require racket/match)

(require "lir.rkt")

(provide peephole)

;; Stupidest ever
(define (peephole instrs)
  (filter (lambda (i)
	    (match i
	      [`(move-word ,_ ,(junk)) #f]
	      [`(move-word ,x ,y) (not (equal? x y))]
	      [`(use ,_) #f]
	      [else #t]))
	  instrs))
