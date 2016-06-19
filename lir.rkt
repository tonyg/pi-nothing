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

	 def-use

	 compute-live-intervals

	 evaluate-cmpop32
	 negate-cmpop
	 )

(struct lit (val) #:prefab)
(struct junk () #:prefab) ;; marks a dead register
(struct reg (tag) #:prefab) ;; tag is a gensym. TODO: is this sensible?
(struct label (tag) #:prefab) ;; tag is a gensym. TODO: is this sensible? 

(define (fresh-reg) (reg (gensym 'R)))
(define (fresh-label) (label (gensym 'L)))

(struct preg (name) #:prefab) ;; physical registers
(struct temporary (index) #:prefab) ;; spill location
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
    [`(,(or 'call 'tailcall) ,target ,label (,arg ...))
     (values #f (list target) (cons label arg))]))

(define (def-use instr)
  (define-values (killable defs uses) (def-use* instr))
  (values killable
	  (for/set [(d defs) #:when (location? d)] d)
	  (for/set [(u uses) #:when (location? u)] u)))

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

(define (forward-control-transfer-edges instrs-vec)
  (define labels (local-labels instrs-vec))
  (for/fold [(edges (hash))]
            [(counter (in-naturals)) (instr (in-vector instrs-vec))]
    (define dest-instrs
      (match instr
        [`(compare/jmp ,_ ,target ,_ ,_)  (list (hash-ref labels target #f) (+ counter 1))]
        [`(jmp ,target)                   (list (hash-ref labels target #f))]
        [`(ret ,_)                        (list)]
        [_                                #f]))
    (if dest-instrs
        (hash-set edges counter (filter values dest-instrs))
        edges)))

(define (raw-live-ranges instrs)
  (define instrs-vec (list->vector instrs))
  (define max-pos (vector-length instrs-vec))
  (define edges (forward-control-transfer-edges instrs-vec))
  (define in (make-vector max-pos (set)))
  (define (target-instructions pos) (hash-ref edges pos (lambda () (if (< pos max-pos)
                                                                       (list (+ pos 1))
                                                                       '()))))
  (define (live-out pos) (apply set-union
                                (set) ;; to pick the type of set
                                ;; we're interested in in the
                                ;; 0-arg case!
                                (map (lambda (dest) (vector-ref in dest))
                                     (target-instructions pos))))
  (define (propagate-liveness)
    (for/fold [(changed? #f)] [(counter-rev (in-range max-pos))]
      (define counter (- max-pos counter-rev 1))
      (define instr (vector-ref instrs-vec counter))
      (define-values (killable defs uses) (def-use instr))
      (define old-set (vector-ref in counter))
      (define new-set (set-union (set-subtract (live-out counter) defs) uses))
      (vector-set! in counter new-set)
      (or changed? (not (equal? old-set new-set)))))
  (let loop () (when (propagate-liveness) (loop)))
  (for/vector [(counter (in-range max-pos))]
    (live-out counter)))

;; (define (raw-live-ranges instrs)
;;   (define max-pos (length instrs))
;;   (define edges (forward-control-transfer-edges instrs))
;;   (define (target-instructions pos) (hash-ref edges pos (lambda () (if (< pos max-pos)
;;                                                                        (list (+ pos 1))
;;                                                                        '()))))
;;   (define (live-out in pos) (apply set-union
;; 				   (set) ;; to pick the type of set
;; 					 ;; we're interested in in the
;; 					 ;; 0-arg case!
;; 				   (map (lambda (dest) (hash-ref in dest set))
;; 					(target-instructions pos))))
;;   (define (propagate-liveness in)
;;     (for/fold [(in in)]
;;               [(counter-rev (in-naturals)) (instr (in-list (reverse instrs)))]
;;       (define counter (- max-pos counter-rev 1))
;;       (define-values (killable defs uses) (def-use instr))
;;       (hash-set in counter (set-union (set-subtract (live-out in counter) defs) uses))))
;;   (define (in->out in)
;;     (for/hash [(counter (in-range max-pos))]
;;       (values counter (live-out in counter))))
;;   (define (iterate-to-fixpoint f . seeds)
;;     (define next-seeds (call-with-values (lambda () (apply f seeds)) list))
;;     (if (equal? next-seeds seeds) (apply values seeds) (apply iterate-to-fixpoint f next-seeds)))
;;   (in->out (iterate-to-fixpoint propagate-liveness (hash))))

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

;; (define (extract-live-ranges instrs raw-live-map)
;;   (for/fold [(live-map (hash))]
;;             [(counter (in-range (length instrs)))]
;;     (for/fold [(live-map live-map)]
;;               [(reg (in-set (hash-ref raw-live-map counter set)))]
;;       (hash-update live-map
;;                    reg
;;                    (lambda (old)
;;                      (interval-union (singleton-interval counter) old))
;;                    empty-interval))))

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
          [(reg s) (symbol->string s)]
          [(preg s) (symbol->string s)]
          [(temporary n) (format "t~a" n)]
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
