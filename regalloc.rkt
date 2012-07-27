#lang racket/base

(require racket/set)
(require racket/match)

(require racket/pretty)

(require "intervals.rkt")
(require "lir.rkt")
(require "machine.rkt")

(provide allocate-registers)

(define (general-subst x mapping)
  (let walk ((x x))
    (if (hash-has-key? mapping x)
	(hash-ref mapping x)
	(match x
	  [(cons a d) (cons (walk a) (walk d))]
	  [(? struct? x)
	   (define key (prefab-struct-key x))
	   (when (not key) (error 'general-subst "Cannot substitute through ~v" x))
	   (apply make-prefab-struct key (map walk (cdr (vector->list (struct->vector x)))))]
	  [_ x]))))

(define (dead-instr? instr live-map)
  (define-values (killable defs uses) (def-use instr))
  (and killable
       (andmap (lambda (r) (not (hash-has-key? live-map r)))
	       (set->list defs))))

(define (omit-dead-instrs instrs live-ranges)
  (filter (lambda (i) (not (dead-instr? i live-ranges))) instrs))

(define (good-candidate-locations temp-reg instrs-vec live-interval mapping)
  (define def-positions (map car (interval->list live-interval)))
  (define def-instrs (map (lambda (i) (vector-ref instrs-vec i)) def-positions))
  (define def-uses (map (lambda (i)
			  (define-values (killable defs uses) (def-use i))
			  (for/set ((r (in-set uses))) (hash-ref mapping r r)))
			def-instrs))
  (define candidates (apply set-union (set) def-uses))
  ;; (pretty-write `(good-candidate-locations ,temp-reg
  ;; 					   ,def-instrs
  ;; 					   ,candidates))
  candidates)

(define (find-available-register availability requirement-interval good-candidates)
  (match availability
    ['() (values #f availability)]
    [(cons (cons reg available-interval) rest)
     (if (interval-subset? requirement-interval available-interval)
	 (let ((return-this-one
		(lambda ()
		  (values reg (cons (cons reg (interval-subtract available-interval
								 requirement-interval))
				    rest)))))
	   (if (set-member? good-candidates reg)
	       (return-this-one)
	       (let-values (((found-reg remaining-availability)
			     (find-available-register rest requirement-interval good-candidates)))
		 (if found-reg
		     (values found-reg (cons (cons reg available-interval) remaining-availability))
		     (return-this-one)))))
	 (let-values (((found-reg remaining-availability)
		       (find-available-register rest requirement-interval good-candidates)))
	   (values found-reg (cons (cons reg available-interval) remaining-availability))))]))

(define (update-availability availability reg proc)
  (match availability
    ['()
     (error 'update-availability "Could not find availability for register ~v" reg)]
    [(cons (cons (== reg) available-interval) rest)
     (cons (cons reg (proc available-interval)) rest)]
    [(cons other rest)
     (cons other (update-availability rest reg proc))]))

(define (find-spillable-registers live-ranges mapping requirement-interval)
  (filter (lambda (reg)
	    (and (interval-subset? requirement-interval (hash-ref live-ranges reg))
		 (preg? (hash-ref mapping reg))))
	  (hash-keys mapping)))

(define (best-spillable-register live-ranges mapping requirement-interval)
  (define regs
    (sort (find-spillable-registers live-ranges mapping requirement-interval)
	  > ;; TODO: better spill heuristic?
	  #:key (lambda (r) (interval-max (hash-ref live-ranges r)))))
  ;;(pretty-print `(best-spillable-registers (regs ,regs) (live-ranges ,live-ranges)))
  (and (pair? regs)
       (car regs)))

(define (reserve-fixed-registers availability live-ranges)
  (foldl (lambda (r a)
	   (update-availability a r (lambda (old) (interval-subtract old
								     (hash-ref live-ranges r)))))
	 availability
	 (filter preg? (hash-keys live-ranges))))

;; Some kind of hybrid linear-scan/binpacking algorithm, after Poletto
;; & Sarkar 1999 and Traub, Holloway & Smith 1998. Also influenced by
;; ideas from Christian Wimmer's 2004 Master's Thesis, "Linear Scan
;; Register Allocation for the Java HotSpot Client Compiler".
(define (allocate-registers-once starting-temp-count instrs initial-availability)
  (define live-ranges (compute-live-intervals instrs))
  (define instrs-vec (list->vector instrs))
  (let loop ((temp-count starting-temp-count)
	     (ranges (sort (filter (lambda (x) (reg? (car x))) (hash->list live-ranges))
			   <
			   #:key (lambda (e) (interval-min (cdr e)))))
	     (mapping (hash))
	     (availability (reserve-fixed-registers initial-availability live-ranges)))
    (match ranges
      ['()
       ;;(pretty-print `(mapping ,mapping))
       (values temp-count
	       (omit-dead-instrs instrs live-ranges)
	       mapping)]
      [(cons (cons temp-reg live-interval) remaining-ranges)
       (let-values (((found-reg remaining-availability)
		     (find-available-register availability
					      live-interval
					      (good-candidate-locations temp-reg
									instrs-vec
									live-interval
									mapping))))
	 ;; (pretty-print `(loop (temp-count ,temp-count)
	 ;; 		      (ranges ,ranges)
	 ;; 		      (mapping ,mapping)
	 ;; 		      (availability ,availability)))
	 (cond
	  [found-reg
	   (loop temp-count
		 remaining-ranges
		 (hash-set mapping temp-reg found-reg)
		 remaining-availability)]
	  [(best-spillable-register live-ranges mapping live-interval)
	   => (lambda (reg-to-spill)
		(define spilled-live-interval (hash-ref live-ranges reg-to-spill))
		(define new-availability
		  (append (update-availability
			   availability
			   (hash-ref mapping reg-to-spill)
			   (lambda (old) (interval-union old spilled-live-interval)))
			  (list (cons (temporary temp-count)
				      (interval-invert spilled-live-interval)))))
		(loop (+ temp-count 1)
		      ranges
		      (hash-set mapping reg-to-spill (temporary temp-count))
		      new-availability))]
	  [else ;; no spillable. New temp.
	   (loop (+ temp-count 1)
		 remaining-ranges
		 (hash-set mapping temp-reg (temporary temp-count))
		 (append remaining-availability
			 (list (cons (temporary temp-count)
				     (interval-invert live-interval)))))]))])))

(define (allocate-registers md surplus-tail-args instrs)
  (define starting-reg-availability (map (lambda (r) (cons r (full-interval)))
					 (available-regs md)))
  (let loop ((prev-temp-count surplus-tail-args)
	     ;; ^ this effectively reserves the first few temp slots
	     ;; for use in moving around arguments during frame size
	     ;; adjustment in a tail call.
	     (prev-instrs instrs))
    (pretty-print `(allocation-iteration ,prev-temp-count ,prev-instrs))
    (define-values (new-temp-count remaining-instrs mapping)
      (allocate-registers-once prev-temp-count prev-instrs starting-reg-availability))
    (define new-temps-only
      (make-hash (filter (lambda (e) (temporary? (cdr e))) (hash->list mapping))))
    (define mapped-instrs (general-subst remaining-instrs new-temps-only))
    (define new-instrs (expand-temporary-loads-and-stores md mapped-instrs))
    (if (and (= new-temp-count prev-temp-count)
	     (equal? prev-instrs new-instrs))
	(values new-temp-count (general-subst new-instrs mapping))
	(loop new-temp-count new-instrs))))
