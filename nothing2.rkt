#lang racket/base
;; After "Nothing", the BCPL-like language from VPRI

(require racket/set)
(require racket/match)
(require racket/list)
(require (only-in srfi/1 iota))

(require "intervals.rkt")
(require "dump-bytes.rkt")
(require "disasm.rkt")

;; Two languages:
;;  - a register-transfer language with infinite registers and no
;;    consideration of concurrent memory access
;;  - an expression language with support for calls and tail calls

;; Certain aspects of the design (hton, ntoh) owe a debt to GNU
;; Lightning.

;;---------------------------------------------------------------------------
;; Register-transfer language

(struct lit (val) #:prefab)
(struct junk () #:prefab) ;; marks a dead register
(struct reg (tag) #:prefab) ;; tag is a gensym. TODO: is this sensible?

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
    [`(load ,target ,source ,_)		(values #t (set target) (set source))]
    [`(store ,target ,source)		(values #f (set target) (set source))]
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
  (define raw-live-map (raw-live-ranges instrs))
  ;; (for ([(k v) (in-hash raw-live-map)])
  ;;   (write `(,k = ,(list-ref instrs k) -> ,v))
  ;;   (newline))
  (define live-ranges (extract-live-ranges instrs raw-live-map))
  ;;(pretty-print `(live-ranges ,live-ranges))
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

(define (allocate-registers surplus-tail-args instrs)
  (define starting-reg-availability (map (lambda (r) (cons r (full-interval))) available-regs))
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
    (define new-instrs (expand-temporary-loads-and-stores mapped-instrs))
    (if (and (= new-temp-count prev-temp-count)
	     (equal? prev-instrs new-instrs))
	(values new-temp-count (general-subst new-instrs mapping))
	(loop new-temp-count new-instrs))))

;; Stupidest ever
(define (peephole instrs)
  (filter (lambda (i)
	    (match i
	      [`(move-word ,_ ,(junk)) #f]
	      [`(move-word ,x ,y) (not (equal? x y))]
	      [`(use ,_) #f]
	      [else #t]))
	  instrs))

(define (compile-procesure arg-names body-exp env)
  (define argcount (length arg-names))
  (define rib (map (lambda (a) (list a (fresh-reg))) arg-names))
  (define target-reg (fresh-reg))
  (match-define (snippet body-instrs val) (translate-exp #t target-reg body-exp (append rib env)))
  (define most-tail-args (apply max (map (match-lambda
					  [`(tailcall ,_ ,_ ,args) (length args)]
					  [_ 0])
					 body-instrs)))
  (define surplus-tail-args (max 0 (- most-tail-args argcount)))
  (pretty-print `(most-tail-args ,most-tail-args))
  (pretty-print `(surplus-tail-args ,surplus-tail-args))
  (pretty-print `(pre-expansion ,body-instrs))
  (define init-arg-instrs (do ((i 0 (+ i 1))
			       (rib rib (cdr rib))
			       (prolog '() (cons `(move-word ,(cadr (car rib)) ,(inward-arg i))
						 prolog)))
			      ((null? rib) (reverse prolog))))
  (define instrs (expand-instructions (append init-arg-instrs
					      body-instrs
					      (list `(ret ,target-reg)))))
  (pretty-print `(post-expansion ,instrs))
  (define-values (temp-count final-instrs) (allocate-registers surplus-tail-args instrs))
  (append (list `(enter ,temp-count))
	  (peephole final-instrs)))

;;---------------------------------------------------------------------------
;; Expression language

;; TODO: separate statements from expressions?

(define (field-type? x)
  (memq x '(word byte)))

(struct layout (fields) #:prefab)
(struct layout-field (name type) #:prefab)

(struct label (tag) #:prefab) ;; tag is a gensym. TODO: is this sensible? 

(define (fresh-label) (label (gensym 'L)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (fresh-reg) (reg (gensym 'R)))

(struct snippet (instrs val) #:prefab)
(define (snip val . instrs) (snippet instrs val))

(define-syntax seq
  (syntax-rules ()
    [(seq () final ...)
     (let () final ...)]
    [(seq ([valname v] rest ...) final ...)
     (match v
       [(snippet instrs1 valname)
	(match (seq (rest ...) final ...)
	  [(snippet instrs2 finalval)
	   (snippet (append instrs1 instrs2) finalval)])])]))

(define (real-dest? dest)
  (not (void? dest)))

(define (store-result dest val)
  (if (real-dest? dest)
      (snip val `(move-word ,dest ,val))
      (snip val)))

(define (op2 tail? dest env instr-op identity rands)
  (match rands
    ['()
     (snip (lit identity))]
    [(list rand)
     (translate-exp tail? dest rand env)]
    [_ ;; otherwise more than one
     (foldl (lambda (right-rand left-snippet)
	      (match-define (snippet left-instrs left-val) left-snippet)
	      (match-define (snippet right-instrs right-val)
		(translate-exp #f (fresh-reg) right-rand env))
	      (snippet (append left-instrs
			       right-instrs
			       (if (real-dest? dest)
				   (list `(,instr-op ,dest ,left-val ,right-val))
				   (list)))
		       dest))
	    (translate-exp #f (fresh-reg) (car rands) env)
	    (cdr rands))]))

(define (cmp2 dest env rator a b)
  (seq ([av (translate-exp #f (fresh-reg) a env)]
	[bv (translate-exp #f (fresh-reg) b env)])
       (snip dest `(compare ,rator ,dest ,av ,bv))))

(define (translate-exp tail? dest exp env)
  (match exp
    [(? number? val)
     (store-result dest (lit val))]

    [(? symbol? varname)
     (store-result dest (cond [(assq varname env) => cadr]
			      [else (error 'translate "Unbound variable ~a" varname)]))]

    [`(let ,bindings ,body ...)
     (define rib (map (lambda (b)
			(define-values (mutable? name init-exp)
			  (match b
			    [`(mutable ,name ,init-exp) (values #t name init-exp)]
			    [`(,name ,init-exp) (values #f name init-exp)]))
			(define r (fresh-reg))
			(match-define (snippet instrs v) (translate-exp #f r init-exp env))
			(if (and (lit? v) (not mutable?))
			    (list name v instrs mutable?)
			    (list name r instrs mutable?)))
		      bindings))
     (match-define (snippet instrs val) (translate-exp tail? dest `(begin ,@body) (append rib env)))
     (snippet (append (append* (map caddr rib))
		      instrs)
	      val)]

    [`(begin)
     (store-result dest (lit 0))]

    [`(begin ,exp)
     (translate-exp tail? dest exp env)]

    [`(begin ,exp ,exps ...)
     (seq ([v (translate-exp #f (void) exp env)])
	  (translate-exp tail? dest `(begin ,@exps) env))]

    [`(? ,exp)
     (seq ([v (translate-exp #f (fresh-reg) exp env)])
	  (snip dest `(load ,dest ,v 0)))]

    [`(! ,locexp ,valexp)
     (seq ([locv (translate-exp #f (fresh-reg) locexp env)]
	   [valv (translate-exp #f dest valexp env)])
	  (snip dest `(store ,locv ,dest)))]

    [`(+ ,rands ...) (op2 tail? dest env 'w+ 0 rands)]
    [`(* ,rands ...) (op2 tail? dest env 'w* 1 rands)]

    [`(-)
     (error 'translate-exp "(-) needs arguments")]
    [`(- ,rand)
     (seq ([v (translate-exp #f dest rand env)])
	  (snip dest `(wneg ,dest ,dest)))]
    [`(- ,rands ...) (op2 tail? dest env 'w- (void) rands)]

    [`(/)
     (error 'translate-exp "(-) needs arguments")]
    [`(/ ,rand)
     (seq ([v (translate-exp #f dest rand env)])
	  (snip dest `(wdiv ,dest ,(lit 1) ,dest)))]
    [`(/ ,rands ...) (op2 tail? dest env 'wdiv (void) rands)]

    [(or `(%) `(% ,_))
     (error 'translate-exp "(-) needs two or more arguments")]
    [`(% ,rands ...) (op2 tail? dest env 'wmod (void) rands)]

    [`(<= ,a ,b) (cmp2 dest env '<= a b)]
    [`(< ,a ,b) (cmp2 dest env '< a b)]
    [`(= ,a ,b) (cmp2 dest env '= a b)]
    [`(<> ,a ,b) (cmp2 dest env '<> a b)]
    [`(> ,a ,b) (cmp2 dest env '> a b)]
    [`(>= ,a ,b) (cmp2 dest env '>= a b)]

    [`(and ,rands ...) (op2 tail? dest env 'wand -1 rands)]
    [`(or ,rands ...) (op2 tail? dest env 'wor 0 rands)]
    [`(xor ,rands ...) (op2 tail? dest env 'wxor 0 rands)]

    [`(not ,rand)
     (seq ([v (translate-exp #f dest rand env)])
	  (snip dest `(wnot ,dest ,dest)))]

    [`(if ,test ,texp ,fexp)
     (define Lfalse (fresh-label))
     (define Ldone (fresh-label))
     (seq ([testv (translate-exp #f (fresh-reg) test env)])
	  (match-define (snippet ti tv) (translate-exp tail? dest texp env))
	  (match-define (snippet fi fv) (translate-exp tail? dest fexp env))
	  (snippet (append (list `(jmp-false ,testv ,Lfalse))
			   ti
			   (list (if tail? `(ret ,dest) `(jmp ,Ldone))
				 Lfalse)
			   fi
			   (if tail? (list) (list Ldone)))
		   dest))]

    [`(cond)
     (store-result dest (lit 0))]

    [`(cond [,t ,e ...] ,rest ...)
     (translate-exp tail? dest `(if ,t (begin ,@e) (cond ,@rest)) env)]

    [`(while ,test ,body ...)
     (define Ltop (fresh-label))
     (define Ldone (fresh-label))
     (match-define (snippet testi testv) (translate-exp #f (fresh-reg) test env))
     (match-define (snippet bodyi bodyv) (translate-exp #f (fresh-reg) `(begin ,@body) env))
     (snippet (append (list Ltop)
		      testi
		      (list `(jmp-false ,testv ,Ldone))
		      bodyi
		      (list `(jmp ,Ltop)
			    Ldone))
	      (lit 0))]

    [`(set! ,varname ,val)
     (seq ([valv (translate-exp #f (fresh-reg) val env)])
	  (match (assq varname env)
	    [`(,_ ,reg ,_ #t)
	     (snip reg `(move-word ,reg ,valv))]
	    [#f
	     (error 'translate "Unbound variable ~a in set!" varname)]
	    [_
	     (error 'translate "Immutable variable ~a in set!" varname)]))]

    ;;---------------------------------------------------------------------------

    [`(,rator ,rands ...)
     (define rand-snips (do ((i 0 (+ i 1))
			     (rands rands (cdr rands))
			     (snips '() (cons (translate-exp #f (fresh-reg) (car rands) env)
					      snips)))
			    ((null? rands) (reverse snips))))
     (seq ([rator-v (translate-exp #f (fresh-reg) rator env)])
	  (cond
	   [tail?
	    ;; Tail call
	    (snippet (append (append* (map snippet-instrs rand-snips))
			     (list `(tailcall ,dest ,rator-v ,(map snippet-val rand-snips))))
		     dest)]
	   [(real-dest? dest)
	    ;; Nontail call and we care about the result
	    (snippet (append (append* (map snippet-instrs rand-snips))
			     (list `(call ,dest ,rator-v ,(map snippet-val rand-snips))))
		     dest)]
	   [else
	    ;; Nontail call and we don't care about the result
	    (snippet (append (append* (map snippet-instrs rand-snips))
			     (list `(call ,(fresh-reg) ,rator-v ,(map snippet-val rand-snips))))
		     (lit 0))]))]

    ))

;;---------------------------------------------------------------------------
;; Concrete machine: i386.

;; At the moment putting the preferred register later in the list
;; makes it tried first. See the details of how the recursion in
;; find-available-register works.
(define available-regs (map preg (list 'ebx 'ecx 'edx 'esi 'edi 'eax)))

(define word-size-bytes 4)
(define frame-alignment 16) ;; must be a power of two
(define linkage-size 8) ;; ebp + eip

(define (expand-instructions instrs)
  (define killed-regs '(eax edx ecx))
  (define saved-regs '(ebx esi edi))
  (define saved-locs (map (lambda (r) (fresh-reg)) saved-regs))
  (append
   (map (lambda (loc name) `(move-word ,loc ,(preg name))) saved-locs saved-regs)
   (append-map (match-lambda
		[`(wdiv ,target ,s1 ,s2)
		 (list `(move-word ,(preg 'edx) ,(lit 0))
		       `(move-word ,(preg 'eax) ,s1)
		       `(move-word ,(preg 'ecx) ,s2)
		       `(wdiv ,(preg 'eax) ,(preg 'eax) ,(preg 'ecx))
		       `(use ,(preg 'edx))
		       `(move-word ,target ,(preg 'eax)))]
		[`(ret ,target)
		 (append
		  (map (lambda (loc name) `(move-word ,(preg name) ,loc)) saved-locs saved-regs)
		  (map (lambda (name) `(use ,(preg name))) saved-regs)
		  (list `(move-word ,(preg 'eax) ,target)
			`(ret ,(preg 'eax))))]
		[`(,(and op (or 'call 'tailcall)) ,target ,label (,arg ...))
		 (define argcount (length arg))
		 (define calltype (if (eq? op 'tailcall) 'tail 'nontail))
		 (define (mkarg i) (outward-arg calltype argcount i))
		 (append (if (eq? calltype 'tail)
			     (list `(use ,(preg 'eax))) ;; need a scratch reg
			     (list))
			 (list `(prepare-call ,calltype ,argcount))
			 (do ((i 0 (+ i 1))
			      (arg arg (cdr arg))
			      (acc '() (cons `(move-word ,(mkarg i) ,(car arg))
					     acc)))
			     ((null? arg) (reverse acc)))
			 (list `(,op ,(preg 'eax) ,label ,(map mkarg (iota argcount)))
			       `(cleanup-call ,calltype ,argcount))
			 (map (lambda (name) `(move-word ,(preg name) ,(junk))) killed-regs)
			 (map (lambda (name) `(use ,(preg name))) killed-regs)
			 (list`(move-word ,target ,(preg 'eax))))]
		[i
		 (list i)])
	       instrs)))

(define (expand-temporary-loads-and-stores instrs)
  (define (shuffle-for-two-args make-instr target s1 s2)
    (cond
     [(and (equal? target s1) (not (and (memory-location? s1) (memory-location? s2))))
      (list (make-instr target s1 s2))]
     [(or (reg? s2) (lit? s2))
      (list `(move-word ,target ,s1)
	    (make-instr target target s2))]
     [else
      (define r2 (fresh-reg))
      (list `(move-word ,target ,s1)
	    `(move-word ,r2 ,s2)
	    (make-instr target target r2))]))
  (append-map (match-lambda
	       [(and i `(move-word ,(? memory-location? n) ,(? memory-location? m)))
		(if (equal? n m)
		    (list i) ;; it'll be eliminated later
		    (let ((r (fresh-reg)))
		      (list `(move-word ,r ,m)
			    `(move-word ,n ,r))))]
	       [`(,(and op (or 'w+ 'w- 'w* 'wdiv 'wmod)) ,target ,s1 ,s2)
		(shuffle-for-two-args (lambda (o i1 i2) `(,op ,o ,i1 ,i2))
				      target
				      s1
				      s2)]
	       [`(compare ,cmpop ,target ,s1 ,s2)
		(shuffle-for-two-args (lambda (o i1 i2) `(compare ,cmpop ,o ,i1 ,i2))
				      target
				      s1
				      s2)]
	       [`(load ,(temporary n) ,source ,offset)
		(define r (fresh-reg))
		(list `(load ,r ,source ,offset)
		      `(move-word ,(temporary n) ,r))]
	       [i
		(list i)])
	      instrs))

(define ((assemble-instr inward-arg-count) i)
  (local-require "i386.rkt")
  (define (xs v)
    (match v
      [(lit n) n]
      [(preg r) r]
      [(temporary n) (@reg 'ebp (- (* word-size-bytes (+ n 1))))]
      [(inward-arg n) (@reg 'ebp (* word-size-bytes (+ n 2)))]
      [(outward-arg 'nontail _ n) (@reg 'esp (* word-size-bytes n))]
      [(outward-arg 'tail outward-arg-count n)
       (@reg 'ebp (* word-size-bytes (- (+ n 2) (- outward-arg-count inward-arg-count))))]
      ))
  (match i
    [`(enter ,n)
     (define temp-size (* n word-size-bytes))
     (define total-requirement (+ temp-size linkage-size))
     (define frame-size (round-up-to-nearest frame-alignment total-requirement))
     (define delta (- frame-size linkage-size))
     (list (*push32 'ebp)
	   (*mov 'esp 'ebp)
	   (*op 'sub delta 'esp))]
    [`(move-word ,target ,source)			(*mov (xs source) (xs target))]
    [`(load ,(preg target) ,(lit n) ,ofs)		(*mov (@imm (+ n ofs)) target)]
    [`(w+ ,target ,target ,source)			(*op 'add (xs source) (xs target))]
    [`(w- ,target ,target ,source)			(*op 'sub (xs source) (xs target))]
    [`(w* ,target ,target ,source)			(*imul (xs source) (xs target))]
    [`(wdiv ,(preg 'eax) ,(preg 'eax) ,(preg r))	(*div r)]
    [`(compare ,cmpop ,(preg target) ,(preg target) ,source)
     (define cc (case cmpop ((<=) 'le) ((<) 'l) ((=) 'e) ((<>) 'ne) ((>) 'g) ((>=) 'ge)))
     (define skip (gensym 'skip))
     (list (*op 'xor target target)
	   (*op 'cmp (xs source) target)
	   (*jmp-cc (invert-condition-code cc) (label-reference skip #t))
	   (*inc target)
	   (label-anchor skip))]
    [`(prepare-call nontail ,arg-count)
     (if (zero? arg-count)
	 '()
	 (*op 'sub (round-up-to-nearest frame-alignment (* arg-count word-size-bytes)) 'esp))]
    [`(prepare-call tail ,arg-count)
     (define delta (- arg-count inward-arg-count))
     ;; move saved ebp and saved eip DOWN in memory by delta words
     ;; because ebp is lower in memory, move it first
     ;; eax is our scratch reg by convention - see expand-instructions
     (if (zero? delta)
	 '()
	 (list (*mov (@reg 'ebp 0) 'eax)
	       (*mov 'eax (@reg 'ebp (- (* delta word-size-bytes))))
	       (*mov (@reg 'ebp 4) 'eax)
	       (*mov 'eax (@reg 'ebp (+ 4 (- (* delta word-size-bytes)))))))]
    [`(cleanup-call nontail ,arg-count)
     (if (zero? arg-count)
	 '()
	 (*op 'add (round-up-to-nearest frame-alignment (* arg-count word-size-bytes)) 'esp))]
    [`(cleanup-call tail ,_)				'()]
    [(label tag)					(label-anchor tag)]
    [`(jmp-false ,(preg val) ,(label tag))
     (list (*op 'cmp 0 val)
	   (*jmp-cc 'z (label-reference tag #f)))]
    [`(jmp ,(label tag))				(*jmp (label-reference tag #f))]
    [`(ret ,(preg 'eax))				(list (*leave) (*ret))]
    [`(call ,(preg 'eax) ,(label tag) ,_)		(*call (label-reference tag #f))]
    [`(tailcall ,(preg 'eax) ,(label tag) ,args)
     (define delta (- (length args) inward-arg-count))
     (list (if (zero? delta)
	       '()
	       (*op 'sub (* delta word-size-bytes) 'ebp))
	   (*leave)
	   (*jmp (label-reference tag #f)))]
    [_ (error 'assemble-instr "Cannot assemble ~v" i)]))

(define ((assemble-instr* inward-arg-count) i)
  (define bs ((assemble-instr inward-arg-count) i))
  (write `(,i -> ,bs))
  (newline)
  (flush-output)
  bs)

(define (assemble inward-arg-count instrs)
  (local-require "i386.rkt")
  (define pre-linking (flatten (map (assemble-instr* inward-arg-count) instrs)))
  (write `(pre-linking ,pre-linking)) (newline) (flush-output)
  (define-values (linked relocs) (internal-link pre-linking))
  (write `(relocations ,relocs)) (newline) (flush-output)
  (list->bytes linked))

;;---------------------------------------------------------------------------
;; Other machines

;; (define available-regs (map preg (list 'rax 'rbx 'rcx 'rdx 'rsi 'rdi
;; 				       'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15)))
;;(define available-regs (map preg (list 'r0 'r1 'r2 'r3 'r4 'r5 'r6 'r7)))
;;(define available-regs (map preg (list 'r0 'r1)))
;;(define available-regs (map preg (list)))

;; (define (expand-instructions instrs)
;;   instrs)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require racket/trace)
;;(trace translate-exp)
;;(trace expand-temporary-loads-and-stores)

(define (te args exp env)
  (display "===========================================================================")
  (newline)
  (pretty-print exp)
  (define final-instrs (compile-procesure args exp env))
  (pretty-print `(final-instrs ,final-instrs))
  (define assembled (assemble (length args) final-instrs))
  (dump-bytes! assembled)
  (disassemble-bytes! assembled #:arch 'i386)
  (display "===========================================================================")
  (newline)
  (newline))

(require racket/pretty)

(te '() `(+ 1 2 3) '())
(te '() `(let ((a (? 123))) (+ a a a)) '())

(te '() '(/ 99 11) '())

(te '() `(/ (? 123) (? 234)) '())

(te '() `(let ((mutable a 0)) (while (< a 10) (set! a (+ a 1))) a) '())

(te '()
    `(let ((a (? 123))
	   (b (? 234)))
       (+ a 90 9 b))
    '())

(te '()
    `(+ (? 123) (- 99 9) 9 (? 234))
    '())

(te '()
    `(+ (fib 2) (fib 1))
    `((fib ,(label 'FIB))))

(te '() `(if (if (< 11 22) 33 44) 55 66) '())
(te '()
    `(cond [(A) 11] [(B) 22] [(C) 33])
    `((A ,(label 'A))
      (B ,(label 'B))
      (C ,(label 'C))))

(te '(arg)
    `(if (< arg 2)
	 arg
	 (+ (fib (- arg 1)) (fib (- arg 2))))
    `((fib ,(label 'FIB))))

(te '() `(x (x (x))) `((x ,(label 'X))))

(te '(cx cy)
    '(let ((mutable zx 0)
	   (mutable zy 0)
	   (mutable i 0))
       (while (< (+ (* zx zx) (* zy zy)) 4)
	 (let ((tx (+ cx (- (* zx zx) (* zy zy))))
	       (ty (+ cy (* 2 zx zy))))
	   (set! i (+ i 1))
	   (set! zx tx)
	   (set! zy ty)))
       i)
    `())

(te '(cx cy)
    '(let ((mutable zx 0)
	   (mutable zy 0)
	   (mutable i 0))
       (while (< (+ (* zx zx) (* zy zy)) 4)
	 (let ((tx zx) (ty zy))
	   (set! zx (+ cx (- (* tx tx) (* ty ty))))
	   (set! zy (+ cy (* 2 tx ty)))
	   (set! i (+ i 1))))
       i)
    `())

(te '()
    '(let ((v20 (? 20)) (v21 (? 21)) (v22 (? 22)) (v23 (? 23)) (v24 (? 24))
	   (v25 (? 25)) (v26 (? 26)) (v27 (? 27)) (v28 (? 28)) (v29 (? 29)))
       (+ v20 v21 v22 v23 v24 v25 v26 v27 v28 v29))
    '())
