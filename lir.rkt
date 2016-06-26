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

;; Low-level Intermediate Representation.
;;  - a register-transfer language with infinite registers and no
;;    consideration of concurrent memory access

;; Certain aspects of the design (hton, ntoh) owe a debt to GNU
;; Lightning.

(require racket/set)
(require racket/match)

(require "intervals.rkt")
(require "unsigned.rkt")

(provide (struct-out lit)
	 (struct-out junk)
	 (struct-out reg)
	 (struct-out label)

	 fresh-reg
	 fresh-label

	 (struct-out preg)
	 (struct-out temporary)
	 (struct-out inward-arg)
	 (struct-out outward-arg)

	 location?
	 memory-location?
	 reg-or-preg?
	 non-reg?

         current-location-sanitizer
         lir-value-var
         sanitize-location
	 def-use

	 compute-live-intervals

	 evaluate-cmpop32
	 negate-cmpop
	 )

(struct lit (val) #:prefab)
(struct junk () #:prefab) ;; marks a dead register
(struct reg (tag var) #:prefab) ;; tag is a gensym. TODO: is this sensible?
(struct label (tag) #:prefab) ;; tag is a gensym. TODO: is this sensible?

(define (fresh-reg [var #f]) (reg (gensym 'R) var))
(define (fresh-label [suffix #f]) (label (gensym (if suffix (format "L~a" suffix) 'L))))

(struct preg (name var) #:prefab) ;; physical registers
(struct temporary (index var) #:prefab) ;; spill location

(struct inward-arg (index) #:prefab)
(struct outward-arg (calltype count index) #:prefab)

(define (location? x)
  (not (or (lit? x)
	   (label? x)
	   (junk? x))))

(define (memory-location? x)
  (or (temporary? x)
      (inward-arg? x)
      (outward-arg? x)))

(define (reg-or-preg? x)
  (or (reg? x) (preg? x)))

(define (non-reg? x)
  (not (reg-or-preg? x)))

(define (lir-value-var loc)
  (match loc
    [(preg name var) var]
    [(temporary index var) var]
    [(reg name var) var]
    [_ #f]))

;; Strip out any provenance/debug information from a location.
;; Used to make equivalences line up properly during register allocation.
(define (sanitize-location loc)
  (match loc
    [(preg name _) (preg name #f)]
    [(temporary index _) (temporary index #f)]
    [(? reg?) loc]
    [(? inward-arg?) loc]
    [(? outward-arg?) loc]))

(define (def-use* instr)
  (match instr
    [`(move-word ,target ,source)	(values #t (list target) (list source))]
    [`(load-word ,target ,source ,_)	(values #t (list target) (list source))]
    [`(load-byte ,target ,source ,_)	(values #t (list target) (list source))]
    [`(store-word ,target ,source)	(values #f (list) (list target source))]
    [`(store-byte ,target ,source)	(values #f (list) (list target source))]
    [`(w+ ,target ,s1 ,s2)		(values #t (list target) (list s1 s2))]
    [`(w- ,target ,s1 ,s2)		(values #t (list target) (list s1 s2))]
    [`(w* ,target ,s1 ,s2)		(values #t (list target) (list s1 s2))]
    [`(w*/extended ,t1 ,t2 ,s1 ,s2)     (values #t (list t1 t2) (list s1 s2))]
    [`(wand ,target ,s1 ,s2)		(values #t (list target) (list s1 s2))]
    [`(wor ,target ,s1 ,s2)		(values #t (list target) (list s1 s2))]
    [`(wxor ,target ,s1 ,s2)		(values #t (list target) (list s1 s2))]
    [`(wnot ,target ,source)		(values #t (list target) (list source))]
    [`(wdiv ,target ,s1 ,s2)		(values #t (list target) (list s1 s2))]
    [`(wmod ,target ,s1 ,s2)		(values #t (list target) (list s1 s2))]
    [`(wshift ,_ ,target ,s1 ,s2)	(values #t (list target) (list s1 s2))]
    [`(compare/set ,_ ,target ,s1 ,s2)	(values #t (list target) (list s1 s2))]
    [`(compare/jmp ,_ ,target ,s1 ,s2)	(values #f (list) (list s1 s2 target))]

    [`(use ,source)			(values #f (list) (list source))]

    [(? label?)				(values #f (list) (list))]
    [`(jmp ,target)			(values #f (list) (list target))]
    [`(ret ,r)				(values #f (list) (list r))]
    [`(call ,target ,label (,arg ...))  (values #f (list target) (cons label arg))]
    [`(tailcall ,label (,arg ...))      (values #f (list) (cons label arg))]))

(define current-location-sanitizer (make-parameter sanitize-location))

(define (def-use instr)
  (define-values (killable defs uses) (def-use* instr))
  (define san (current-location-sanitizer))
  (values killable
	  (for/list [(d defs) #:when (location? d)] (san d))
	  (for/list [(u uses) #:when (location? u)] (san u))))

;; Instructions are numbered sequentially starting from zero.
;; Registers are technically live on the edges *between* instructions,
;; but a safe conservative approximation of this is to think of them
;; as live *during* instructions. Live intervals [a,b] are closed
;; intervals.

(define (local-labels instrs-vec)
  (for/hash [(counter (in-naturals))
             (instr (in-vector instrs-vec))
             #:when (label? instr)]
    (values instr counter)))

(define (all-defs-and-uses instrs-vec)
  (define defs (make-vector (vector-length instrs-vec)))
  (define uses (make-vector (vector-length instrs-vec)))
  (for [(counter (in-naturals)) (instr (in-vector instrs-vec))]
    (define-values (_k ds us) (def-use instr))
    (vector-set! defs counter ds)
    (vector-set! uses counter us))
  (values defs uses))

(define (raw-live-ranges instrs)
  (define instrs-vec (list->vector instrs))
  (define-values (defs uses) (all-defs-and-uses instrs-vec))

  (define max-pos (vector-length instrs-vec))
  (define in (make-vector max-pos (set)))

  (define labels (local-labels instrs-vec))
  (define (live-at-label label)
    (define pos (hash-ref labels label #f))
    (if pos (vector-ref in pos) (set)))

  (define (live-out pos)
    (match (vector-ref instrs-vec pos)
      [`(compare/jmp ,_ ,target ,_ ,_) (set-union (live-at-label target) (vector-ref in (+ pos 1)))]
      [`(jmp ,target)                  (live-at-label target)]
      [`(ret ,_)                       (set)]
      [`(tailcall ,_ ,_)               (set)]
      [_                               (vector-ref in (+ pos 1))]))

  (define (propagate-liveness)
    (for/fold [(changed? #f)] [(counter-rev (in-range max-pos))]
      (define counter (- max-pos counter-rev 1))
      (define instr (vector-ref instrs-vec counter))
      (define old-set (vector-ref in counter))
      ;; Avoid set-union and set-subtract; the generic dispatch overhead is large
      (define new-set (for/fold [(s (for/fold [(s (live-out counter))]
                                              [(d (in-list (vector-ref defs counter)))]
                                      (set-remove s d)))]
                                [(u (in-list (vector-ref uses counter)))]
                        (set-add s u)))
      (vector-set! in counter new-set)
      (or changed? (not (equal? old-set new-set)))))
  (let loop () (when (propagate-liveness) (loop)))
  (for/vector [(counter (in-range max-pos))]
    (live-out counter)))

(define (extract-live-ranges instrs raw-live-map)
  ;; Optimized to avoid hash-update and interval-union where one
  ;; argument is singleton-interval.
  (define rs
    (for/fold [(live-map (hash))]
              [(counter (in-range (length instrs)))]
      (for/fold [(live-map live-map)]
                [(reg (in-set (vector-ref raw-live-map counter)))]
        (hash-set live-map
                  reg
                  (match (hash-ref live-map reg '())
                    [(list* stop rest) #:when (= stop counter) (list* (+ counter 1) rest)]
                    [ts (list* (+ counter 1) counter ts)])))))
  (for/hash [((r ts) (in-hash rs))]
    (values r (raw-toggles->interval (reverse ts)))))

(define (print-raw-live-map instrs raw-live-map)
  (local-require (only-in srfi/13 string-pad string-pad-right))
  (printf "(raw-live-map\n")
  (for [(k (in-naturals)) (instr (in-list instrs))]
    (printf "~a ~a "
            (string-pad (number->string k) 5)
            (string-pad-right (format "~a" instr) 54))
    (define reg-strings
      (for/list [(r (in-set (vector-ref raw-live-map k)))]
        (match r
          [(reg s #f) (symbol->string s)]
          [(reg s var) (format "~a(~a)" s var)]
          [(preg s #f) (symbol->string s)]
          [(preg s var) (format "~a(~a)" s var)]
          [(temporary n #f) (format "t~a" n)]
          [(temporary n var) (format "t~a(~a)" n var)]
          [(inward-arg n) (format "i~a" n)]
          [(outward-arg _ _ n) (format "o~a" n)]
          [other (format "~a" other)])))
    (display (sort reg-strings string<?))
    (newline))
  (printf ")\n"))

(define (compute-live-intervals instrs)
  (define raw-live-map (raw-live-ranges instrs))
  ;; (print-raw-live-map instrs raw-live-map)
  (define live-ranges (extract-live-ranges instrs raw-live-map))
  ;; (local-require racket/pretty)
  ;; (pretty-print `(live-ranges ,live-ranges))
  live-ranges)

;; TODO: Do constant-folding more generally.
(define (evaluate-cmpop32 cmpop n m)
  (define opfn (case cmpop
		 ((<=s) <=)
		 ((<s) <)
		 ((<=u) <=u32)
		 ((<u) <u32)
		 ((=) =)
		 ((<>) (lambda (a b) (not (= a b))))
		 ((>s) >)
		 ((>=s) >=)
		 ((>u) >u32)
		 ((>=u) >=u32)))
  (opfn n m))

(define (negate-cmpop cmpop)
  (case cmpop
    ((<=s) '>s)
    ((<s) '>=s)
    ((<=u) '>u)
    ((<u) '>=u)
    ((=) '<>)
    ((<>) '=)
    ((>s) '<=s)
    ((>=s) '<s)
    ((>u) '<=u)
    ((>=u) '<u)))
