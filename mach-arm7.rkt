#lang racket/base
;; Concrete machine: ARMv7.

(require racket/match)
(require (only-in racket/list append-map))
(require (only-in srfi/1 iota))
(require (only-in '#%foreign _int32))

(require "lir.rkt")
(require "linker.rkt")
(require "asm-arm7.rkt")
(require (only-in "machine.rkt" machine-description))
(require "unsigned.rkt")

(provide machine-arm7)

;; r0-r11
;; r12 - scratch reg, never made available to the register allocator so free for use
;; r13 - stack
;; r14 - lr
;; r15 - pc

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Calling conventions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; The ARM procedure call standard (AAPCS) specifies a convention for
;; using the stack pointer suitable for C-like linkage. Because our
;; setup includes tail calls, we can't quite use it unmodified. So
;; here's what we do instead.
;;
;;  - We keep our stack Full Descending, just like AAPCS.
;;  - We ensure it is 8-byte aligned at all times, just like (a slight
;;    restriction of) AAPCS.
;;  - We make outbound arguments leftmost-low, that is, "pushed from
;;    right to left". This makes us compatible with naive C struct
;;    overlaying of memory.
;;
;;  - We do NOT move the stack pointer down over outbound arguments.
;;    Instead, the callee moves the stack pointer as they see fit.
;;    This is totally difference from AAPCS. The reason for this is
;;    so that the callee can tail-call someone else without having to
;;    do any hairy adjusting of the frame, and so that the original
;;    caller doesn't have to know anything about what's left to clean
;;    up when they receive control: all the clean-up has already been
;;    completed.
;;
;;  - This bears stating again: just after return from a subroutine,
;;    all clean-up has already been completed.
;;
;; So, with that all out of the way, stack frames need to account for
;;  - inward args (numbered 4 and above; 0-3 are transmitted in
;;    registers)
;;  - saved temporaries
;;  - being aligned to the nearest frame-alignment byte boundary
;;
;; Stacks are full descending.
;;  - Ni = inward-arg-count
;;  - Nt = inward-temp-count
;;  - Na = outward-arg-count
;;  - Af = frame-alignment
;;
;; Upon entry to a subroutine, Ni=4, Nt=5:
;;
;;   (high addresses)
;;   ...
;;   caller's private information
;;   ...
;;   caller's lowest-addressed temp	<--- sp, at 8-byte boundary
;;   padding
;;   inbound 4
;;   inbound 3 (virtual, r3)
;;   inbound 2 (virtual, r2)
;;   inbound 1 (virtual, r1)
;;   inbound 0 (virtual, r0)
;;   padding
;;   temp 4
;;   temp 3
;;   temp 2
;;   temp 1
;;   temp 0				<--- potential new location for sp
;;   (low addresses)
;;
;; Leaf procedures do NOT move the stack pointer on entry. Nonleaf
;; procedures DO move the stack pointer on entry. This means we have
;; different addressing calculations depending on whether we're a leaf
;; or nonleaf procedure.
;;
;; Pad8(x) = x rounded up to the nearest multiple of 8
;; sp_delta = Pad8(Ni * 4) + Pad8(Nt * 4), distance SP might move on entry and exit
;;
;; Leaf procedures:
;;   SP does not move
;;   inward(n) = rn, if n < 4
;;             | sp - Pad8(Ni * 4) + (n * 4)
;;   temp(n) = sp - sp_delta + (n * 4)
;;   outward(n) (tail calls only) = rn, if n < 4
;;                                | sp - Pad8(Na * 4) + (n * 4)
;;
;; Nonleaf procedures:
;;   SP moves by sp_delta
;;   inward(n) = rn, if n < 4
;;             | sp + Pad8(Nt * 4) + (n * 4)
;;   temp(n) = sp + (n * 4)
;;   outward(n) (non-tail calls) = rn, if n < 4
;;                               | sp - Pad8(Na * 4) + (n * 4)
;;   outward(n) (tail calls) = rn, if n < 4
;;                           | sp + sp_delta - Pad8(Na * 4) + (n * 4)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define available-regs (map preg (list 'lr
				       'r11 'r10 'r9 'r8
				       'r7 'r6 'r5 'r4
				       'r3 'r2 'r1 'r0)))

(define word-size-bytes 4)
(define frame-alignment 8)
(define linkage-size 0)

(define killed-regs '(r0 r1 r2 r3 lr))
(define saved-regs '(r4 r5 r6 r7 r8 r9 r10 r11 lr))

(define (inward-argument-location i)
  (if (< i 4)
      (preg (list-ref '(r0 r1 r2 r3) i))
      (inward-arg i)))

(define (outward-argument-location calltype count i)
  (if (< i 4)
      (preg (list-ref '(r0 r1 r2 r3) i))
      (outward-arg calltype count i)))

(define (reg-or-preg? x)
  (or (reg? x) (preg? x)))

(define (non-reg? x)
  (not (reg-or-preg? x)))

(define ((expand-instruction saved-locs) instr)
  (match instr
    [`(wdiv ,target ,s1 ,s2)
     (list `(move-word ,(preg 'r0) ,s1)
	   `(move-word ,(preg 'r1) ,s2)
	   `(call ,(preg 'r0) ,(label '__udivsi3) (,(preg 'r0) ,(preg 'r1)))
	   `(use ,(preg 'r2))
	   `(use ,(preg 'r3))
	   `(use ,(preg 'lr))
	   `(move-word ,target ,(preg 'r0)))]
    [`(wmod ,target ,s1 ,s2)
     (list `(move-word ,(preg 'r0) ,s1)
	   `(move-word ,(preg 'r1) ,s2)
	   `(call ,(preg 'r0) ,(label '__udivsi3) (,(preg 'r0) ,(preg 'r1)))
	   `(use ,(preg 'r2))
	   `(use ,(preg 'r3))
	   `(use ,(preg 'lr))
	   `(move-word ,target ,(preg 'r1)))]
    [`(ret ,target)
     (append (list `(move-word ,(preg 'r0) ,target))
	     (map (lambda (loc name) `(move-word ,(preg name) ,loc)) saved-locs saved-regs)
	     (map (lambda (name) `(use ,(preg name))) saved-regs)
	     (list `(ret ,(preg 'r0))))]
    [`(,(and op (or 'call 'tailcall)) ,target ,label (,arg ...))
     (define argcount (length arg))
     (define calltype (if (eq? op 'tailcall) 'tail 'nontail))
     (define (mkarg i) (outward-argument-location calltype argcount i))
     (append ;; Note no mention of r12 here, unlike the i386/x86_64 backends.
	     (do ((i 0 (+ i 1))
		  (arg arg (cdr arg))
		  (acc '() (cons `(move-word ,(mkarg i) ,(car arg))
				 acc)))
		 ((null? arg) (reverse acc)))
	     (if (eq? calltype 'tail)
		 (append
		  (map (lambda (loc name) `(move-word ,(preg name) ,loc)) saved-locs saved-regs)
		  ;;(map (lambda (name) `(use ,(preg name))) saved-regs)
		  )
		 (list))
	     (list `(,op ,(preg 'r0) ,label ,(map mkarg (iota argcount))))
	     (map (lambda (name) `(move-word ,(preg name) ,(junk))) killed-regs)
	     (map (lambda (name) `(use ,(preg name))) killed-regs)
	     (list`(move-word ,target ,(preg 'r0))))]
    [`(,(and op (or 'store-word 'store-byte)) ,(? non-reg? target) ,source)
     (define r (fresh-reg))
     (list `(move-word ,r ,target)
	   `(,op ,r ,source))]
    [i
     (list i)]))

(define (expand-instructions init-arg-instrs instrs)
  (define saved-locs (map (lambda (r) (fresh-reg)) saved-regs))
  (define expander (expand-instruction saved-locs))
  (append (map (lambda (loc name) `(move-word ,loc ,(preg name))) saved-locs saved-regs)
	  (append-map expander init-arg-instrs)
	  (append-map expander instrs)))

;; TODO: lift this away from being machine specific. Generally, do
;; constant-folding.
(define (evaluate-cmpop cmpop n m)
  (define opfn (case cmpop
		 ((<=s) <=)
		 ((<s) <)
		 ((<=u) <=u32)
		 ((>u) >u32)
		 ((=) =)
		 ((<>) (lambda (a b) (not (= a b))))
		 ((>s) >)
		 ((>=s) >=)
		 ((>u) >u32)
		 ((>=u) >=u32)))
  (bool->bit (opfn n m)))

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
	       [`(,(and op (or 'w+ 'w- 'w* 'wand 'wor 'wxor 'wdiv 'wmod))
		  ,target
		  ,(? non-reg? s1)
		  ,s2)
		;; TODO: separate out commutative operators here and
		;; try flipping the arguments to see if that is an option
		(define r (fresh-reg))
		(list `(move-word ,r ,s1)
		      `(,op ,target ,r ,s2))]
	       [`(compare ,cmpop ,target ,(? lit? n) ,(? lit? m))
		(list `(move-word ,target ,(lit (evaluate-cmpop cmpop (lit-val n) (lit-val m)))))]
	       [`(compare ,cmpop ,target ,(? memory-location? n) ,(? memory-location? m))
		(define r (fresh-reg))
		(list `(move-word ,r ,m)
		      `(compare ,cmpop ,target ,n ,r))]
	       [`(,(and op (or 'load-word 'load-byte)) ,(temporary n) ,source ,offset)
		(define r (fresh-reg))
		(list `(,op ,r ,source ,offset)
		      `(move-word ,(temporary n) ,r))]
	       [`(,(and op (or 'store-word 'store-byte)) ,target ,(temporary n))
		(define r (fresh-reg))
		(list `(move-word ,r ,(temporary n))
		      `(,op ,target ,r))]
	       [i
		(list i)])
	      instrs))

(define (nodata code)
  (values code '()))

(define (code/data code data)
  (values code data))

;; For loading immediate values too large to fit in a single instruction.
(define (indirect-immediate target-reg immediate more-code)
  (if (label-reference? immediate)
      (nodata (label-linker (label-reference-name immediate)
			    4
			    (lambda (delta i)
			      (define final-delta (- delta 8))
			      (if (negative? final-delta)
				  (*sub 'al 0 target-reg 'pc (- final-delta))
				  (*add 'al 0 target-reg 'pc final-delta)))))
      (let ((L (fresh-label)))
	(code/data (list (label-linker (label-tag L)
				       4
				       (lambda (delta i)
					 (*ldr 'al target-reg (@reg 'pc '+ (- delta 8)))))
			 more-code)
		   (list (label-anchor (label-tag L)) (imm32* immediate))))))

(define (sprel delta)
  (@reg 'sp
	(if (negative? delta) '- '+)
	(if (negative? delta) (- delta) delta)))

(define (frame-pad-words n)
  (round-up-to-nearest frame-alignment (* n word-size-bytes)))

(define (compute-sp-delta inward-arg-count temp-count)
  (+ (frame-pad-words inward-arg-count) (frame-pad-words temp-count)))

(define ((assemble-instr inward-arg-count temp-count leaf?) i)
  (define sp-delta (compute-sp-delta inward-arg-count temp-count))
  (define (xs v)
    (match v
      [(lit n) n]
      [(label tag) (label-reference tag)]
      [(preg r) r]
      [(temporary n)
       (if leaf?
	   (sprel (- (* n word-size-bytes) sp-delta))
	   (sprel (* n word-size-bytes)))]
      [(inward-arg n)
       (if (< n 4)
	   (list-ref '(r0 r1 r2 r3) n)
	   (if leaf?
	       (sprel (- (* n word-size-bytes) (frame-pad-words inward-arg-count)))
	       (sprel (+ (* n word-size-bytes) (frame-pad-words temp-count)))))]
      [(outward-arg 'nontail outward-arg-count n)
       (if (< n 4)
	   (list-ref '(r0 r1 r2 r3) n)
	   (if leaf?
	       (error 'xs-arm "Nontail call in leaf procedure")
	       (sprel (- (* n word-size-bytes) (frame-pad-words outward-arg-count)))))]
      [(outward-arg 'tail outward-arg-count n)
       (if (< n 4)
	   (list-ref '(r0 r1 r2 r3) n)
	   (if leaf?
	       (sprel (- (* n word-size-bytes) (frame-pad-words outward-arg-count)))
	       (sprel (- (+ (* n word-size-bytes) sp-delta)
			 (frame-pad-words outward-arg-count)))))]
      ))
  (match i
    [`(move-word ,target ,source)
     (define real-target (xs target))
     (define real-source (xs source))
     (cond
      [(and (@reg? real-target) (@reg? real-source))
       ;; We know by the action of expand-temporary-loads-and-stores
       ;; that we'll not see both a temporary source and target, but
       ;; just to be sure...
       (error 'assemble-instr "Cannot *mov from memory to memory on ARM ~v" i)]
      [(@reg? real-target)
       ;; Note that the *source* of the move goes in the "target
       ;; register" position because of the syntactic weirdness of the
       ;; STR instruction.
       (nodata (*str 'al real-source real-target))]
      [(@reg? real-source)
       (nodata (*ldr 'al real-target real-source))]
      [(and (number? real-source) (best-rotation-exists? real-source))
       (nodata (*mov 'al 0 real-target real-source))]
      [(and (number? real-source) (best-rotation-exists? (bitwise-not real-source)))
       (nodata (*mvn 'al 0 real-target (bitwise-not real-source)))]
      [(or (label-reference? real-source) (number? real-source))
       ;; Compare to the "load-word" instruction code slightly below. This is like x86 LEA.
       (indirect-immediate real-target
			   real-source
			   '())]
      [else
       (nodata (*mov 'al 0 real-target real-source))])]
    [`(load-word ,(preg target) ,(preg source) ,ofs)
     (nodata (*ldr 'al target (@reg source '+ ofs)))]
    [`(load-word ,(preg target) ,(lit n) ,ofs)
     (indirect-immediate target
			 (+ n ofs)
			 (*ldr 'al target (@reg target '+ 0)))]
    [`(load-byte ,(preg target) ,(preg source) ,ofs)
     (nodata (*ldrb 'al target (@reg source '+ ofs)))]
    [`(load-byte ,(preg target) ,(lit n) ,ofs)
     (indirect-immediate target
			 (+ n ofs)
			 (*ldrb 'al target (@reg target '+ 0)))]
    [`(store-word ,(preg target) ,(preg source))
     (nodata (*str 'al source (@reg target '+ 0)))]
    [`(store-byte ,(preg target) ,(preg source))
     (nodata (*strb 'al source (@reg target '+ 0)))]
    [`(w+ ,target ,s1 ,s2)			(nodata (*add 'al 0 (xs target) (xs s1) (xs s2)))]
    [`(w- ,target ,s1 ,s2)			(nodata (*sub 'al 0 (xs target) (xs s1) (xs s2)))]
    [`(w* ,target ,s1 ,s2)			(nodata (*mul 'al 0 (xs target) (xs s1) (xs s2)))]
    [`(wand ,target ,s1 ,s2)			(nodata (*and 'al 0 (xs target) (xs s1) (xs s2)))]
    [`(wor ,target ,s1 ,s2)			(nodata (*orr 'al 0 (xs target) (xs s1) (xs s2)))]
    [`(wxor ,target ,s1 ,s2)			(nodata (*eor 'al 0 (xs target) (xs s1) (xs s2)))]
    [`(wnot ,target ,source)			(nodata (*mvn 'al 0 (xs target) (xs source)))]
    [`(wshift << ,(preg target) ,(preg s1) ,(lit n))
     (nodata (*mov 'al 0 target (@shifted s1 n)))]
    [`(wshift >>u ,(preg target) ,(preg s1) ,(preg s2))
     (nodata (*mov 'al 0 target (@shifted s1 (@lsr s2))))]
    [`(compare ,cmpop ,target ,s1 ,s2)
     ;; Let wolog cmpop be <. Then we wish to compute s1 - s2 and have
     ;; the comparison be true if the result of subtraction is
     ;; negative. Now, (*op 'cmp source target) is based around target
     ;; - source, so we need to make sure the arguments are in the
     ;; correct order.
     (define cc (case cmpop
		  ((<=s) 'le) ((<s) 'lt)
		  ((<=u) 'ls) ((<u) 'lo)
		  ((=) 'eq) ((<>) 'ne)
		  ((>s) 'gt) ((>=s) 'ge)
		  ((>u) 'hi) ((>=u) 'hs)))
     (define real-s2 (xs s2))
     (nodata (list (if (and (number? real-s2) (negative? real-s2))
		       (*cmn 'al (xs s1) (- real-s2))
		       (*cmp 'al (xs s1) real-s2))
		   (*mov 'al 0 (xs target) 0)
		   (*mov cc 0 (xs target) 1)))]
    [(label tag)
     (nodata (label-anchor tag))]
    [`(jmp-false ,(preg val) ,(label tag))
     (nodata (list (*cmp 'al val 0)
		   (*b 'eq (label-reference tag))))]
    [`(jmp-false ,(lit 0) ,(label tag))		(nodata (*b 'al (label-reference tag)))]
    [`(jmp-false ,(lit _) ,(label tag))		(nodata '())]
    [`(jmp ,(label tag))			(nodata (*b 'al (label-reference tag)))]
    [`(ret ,(preg 'r0))
     (nodata (list (if (or leaf? (zero? sp-delta)) '() (*add 'al 0 'sp 'sp sp-delta))
		   (*mov 'al 0 'pc 'lr)))]
    [`(call ,(preg 'r0) ,(label tag) ,args)
     (define outward-arg-count (length args))
     (nodata (*bl 'al (label-reference tag)))]
    [`(tailcall ,(preg 'r0) ,(label tag) ,args)
     (nodata (list (if (or leaf? (zero? sp-delta)) '() (*add 'al 0 'sp 'sp sp-delta))
		   (*b 'al (label-reference tag))))]
    [_ (error 'assemble-instr "Cannot assemble ~v" i)]))

(define ((assemble-instr* inward-arg-count temp-count leaf?) i)
  (define-values (icode idata) ((assemble-instr inward-arg-count temp-count leaf?) i))
  (write `(,i -> ,icode ,idata))
  (newline)
  (flush-output)
  (values icode idata))

(define (assemble inward-arg-count temp-count leaf? instrs)
  (define sp-delta (compute-sp-delta inward-arg-count temp-count))
  (let loop ((instrs instrs)
	     (code-rev '())
	     (data-rev '()))
    (match instrs
      ['() (values (list (if (or leaf? (zero? sp-delta)) '() (*sub 'al 0 'sp 'sp sp-delta))
			 (reverse code-rev))
		   (reverse data-rev))]
      [(cons instr rest)
       (define-values (icode idata) ((assemble-instr* inward-arg-count temp-count leaf?) instr))
       (loop rest
	     (cons icode code-rev)
	     (cons idata data-rev))])))

(define machine-arm7
  (machine-description 'arm7
		       word-size-bytes
		       _int32
		       available-regs
		       inward-argument-location
		       outward-argument-location
		       expand-instructions
		       expand-temporary-loads-and-stores
		       assemble))
