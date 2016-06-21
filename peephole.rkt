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

(require racket/match)

(require "lir.rkt")

(provide peephole)

(define (discard-until-label instrs)
  (match instrs
    ['() '()]
    [(list* (? label?) rest) instrs]
    [(list* other rest) (discard-until-label rest)]))

;; Stupidest ever
(define (peephole instrs)
  (match instrs
    ['() '()]
    [(list* `(move-word ,_ ,(junk)) rest)
     (peephole rest)]
    [(list* (and move-instr `(move-word ,x ,y)) rest)
     (if (equal? x y)
	 (peephole rest)
	 (cons move-instr (peephole rest)))]
    [(list* `(use ,_) rest)
     (peephole rest)]
    [(list* (and call-instr `(tailcall ,_ ,_)) rest)
     (cons call-instr
	   (peephole (discard-until-label rest)))]
    [(list* instr rest)
     (cons instr (peephole rest))]))
