#lang racket/base
;; Low-level Intermediate Representation.
;;  - a register-transfer language with infinite registers and no
;;    consideration of concurrent memory access

;; Certain aspects of the design (hton, ntoh) owe a debt to GNU
;; Lightning.

(require racket/set)
(require racket/match)

(require "intervals.rkt")

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

	 def-use
	 instr-fold
	 instr-fold-rev

	 iterate-to-fixpoint
	 local-labels
	 forward-control-transfer-edges

	 compute-live-intervals
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

(define (def-use* instr)
  (match instr
    [`(move-word ,target ,source)	(values #t (set target) (set source))]
    [`(load-word ,target ,source ,_)	(values #t (set target) (set source))]
    [`(load-byte ,target ,source ,_)	(values #t (set target) (set source))]
    [`(store-word ,target ,source)	(values #f (set) (set target source))]
    [`(store-byte ,target ,source)	(values #f (set) (set target source))]
    [`(w+ ,target ,s1 ,s2)		(values #t (set target) (set s1 s2))]
    [`(w- ,target ,s1 ,s2)		(values #t (set target) (set s1 s2))]
    [`(w* ,target ,s1 ,s2)		(values #t (set target) (set s1 s2))]
    [`(wdiv ,target ,s1 ,s2)		(values #t (set target) (set s1 s2))]
    [`(wmod ,target ,s1 ,s2)		(values #t (set target) (set s1 s2))]
    [`(compare ,_ ,target ,s1 ,s2)	(values #t (set target) (set s1 s2))]

    [`(use ,source)			(values #f (set) (set source))]
    [`(prepare-call ,_ ,_)		(values #f (set) (set))]
    [`(cleanup-call ,_ ,_)		(values #f (set) (set))]

    [(? label?)				(values #f (set) (set))]
    [`(jmp-false ,condition ,target)	(values #f (set) (set condition target))]
    [`(jmp ,target)			(values #f (set) (set target))]
    [`(ret ,r)				(values #f (set) (set r))]
    [`(,(or 'call 'tailcall) ,target ,label (,arg ...))
     (values #f (set target) (set-add (list->set arg) label))]))

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

(define (instr-fold f seed instrs)
  (let loop ((counter 0)
	     (instrs instrs)
	     (seed seed))
    (if (null? instrs)
	seed
	(loop (+ counter 1) (cdr instrs) (f counter (car instrs) seed)))))

(define (instr-fold-rev f seed instrs)
  (define max-pos (length instrs))
  (instr-fold (lambda (counter instr seed) (f (- max-pos counter 1) instr seed))
	      seed
	      (reverse instrs)))

(define (iterate-to-fixpoint f . seeds)
  (define next-seeds (call-with-values (lambda () (apply f seeds)) list))
  (if (equal? next-seeds seeds) (apply values seeds) (apply iterate-to-fixpoint f next-seeds)))

(define (local-labels instrs)
  (instr-fold (lambda (counter instr locs) (if (label? instr) (hash-set locs instr counter) locs))
	      (hash)
	      instrs))

(define (forward-control-transfer-edges instrs)
  (define labels (local-labels instrs))
  (define (add-edge edges dest-instr source-instr)
    (if dest-instr
	(hash-set edges source-instr (cons dest-instr (hash-ref edges source-instr '())))
	edges))
  (instr-fold (lambda (counter instr edges)
		(match instr
		  [`(jmp-false ,_ ,target)	(add-edge (add-edge edges (+ counter 1) counter)
							  (hash-ref labels target #f)
							  counter)]
		  [`(jmp ,target)	(add-edge edges (hash-ref labels target #f) counter)]
		  [`(ret ,_)		edges]
		  [_			(add-edge edges (+ counter 1) counter)]))
	      (hash)
	      instrs))

(define (raw-live-ranges instrs)
  (define edges (forward-control-transfer-edges instrs))
  (define (target-instructions pos) (hash-ref edges pos '()))
  (define (live-out in pos) (apply set-union
				   (set) ;; to pick the type of set
					 ;; we're interested in in the
					 ;; 0-arg case!
				   (map (lambda (dest) (hash-ref in dest set))
					(target-instructions pos))))
  (define (propagate-liveness in)
    (instr-fold-rev (lambda (counter instr in)
		      (define-values (killable defs uses) (def-use instr))
		      (hash-set in counter (set-union (set-subtract (live-out in counter) defs)
						      uses)))
		    in
		    instrs))
  (define (in->out in)
    (do ((counter (- (length instrs) 1) (- counter 1))
	 (acc (hash) (hash-set acc counter (live-out in counter))))
	((< counter 0) acc)))
  (in->out (iterate-to-fixpoint propagate-liveness (hash))))

(define (extract-live-ranges instrs raw-live-map)
  (instr-fold (lambda (counter instr live-map)
		(foldl (lambda (reg live-map)
			 (hash-update live-map
				      reg
				      (lambda (old)
					(interval-union (singleton-interval counter) old))
				      empty-interval))
		       live-map
		       (set->list (hash-ref raw-live-map counter set))))
	      (hash)
	      instrs))

(define (compute-live-intervals instrs)
  (define raw-live-map (raw-live-ranges instrs))
  ;; (for ([k (in-range (length instrs))])
  ;;   (write `(,k = ,(list-ref instrs k) -> ,(hash-ref raw-live-map k)))
  ;;   (newline))
  (define live-ranges (extract-live-ranges instrs raw-live-map))
  ;;(pretty-print `(live-ranges ,live-ranges))
  live-ranges)
