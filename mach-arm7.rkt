#lang racket/base
;; Concrete machine: ARMv7.

(require racket/match)
(require racket/list)
(require (only-in srfi/1 iota))
(require (only-in '#%foreign _int32))

(require "lir.rkt")
(require "asm-arm7.rkt")
(require (only-in "machine.rkt" machine-description))

(provide machine-arm7)

;; r0-r11
;; r12 - scratch reg
;; r13 - stack
;; r14 - lr
;; r15 - pc

(define available-regs (map preg (list 'r11 'r10 'r9 'r8
				       'r7 'r6 'r5 'r4
				       'r3 'r2 'r1 'r0
				       'lr)))

(define word-size-bytes 4)
(define frame-alignment 16) ;; must be a power of two
(define linkage-size 0)

(define killed-regs '(r0 r1 r2 r3))
(define saved-regs '(r4 r5 r6 r7 r8 r9 r10 r11 lr))

(define (inward-argument-location i)
  (if (< i 4)
      (preg (list-ref '(r0 r1 r2 r3) i))
      (inward-arg (- i 4))))

(define (outward-argument-location calltype count i)
  (if (< i 4)
      (preg (list-ref '(r0 r1 r2 r3) i))
      (outward-arg calltype count (- i 4))))

(define ((expand-instruction saved-locs) instr)
  (match instr
    [`(ret ,target)
     (append (list `(move-word ,(preg 'r0) ,target))
	     (map (lambda (loc name) `(move-word ,(preg name) ,loc)) saved-locs saved-regs)
	     (map (lambda (name) `(use ,(preg name))) saved-regs)
	     (list `(ret ,(preg 'r0))))]
    [`(,(and op (or 'call 'tailcall)) ,target ,label (,arg ...))
     (define argcount (length arg))
     (define calltype (if (eq? op 'tailcall) 'tail 'nontail))
     (define (mkarg i) (outward-argument-location calltype argcount i))
     (append (if (eq? calltype 'tail)
		 (list `(use ,(preg 'r12))) ;; need a scratch reg
		 (list))
	     (do ((i 0 (+ i 1))
		  (arg arg (cdr arg))
		  (acc '() (cons `(move-word ,(mkarg i) ,(car arg))
				 acc)))
		 ((null? arg) (reverse acc)))
	     (if (eq? calltype 'tail)
		 (append
		  (map (lambda (loc name) `(move-word ,(preg name) ,loc)) saved-locs saved-regs)
		  (map (lambda (name) `(use ,(preg name))) saved-regs))
		 (list))
	     (list `(,op ,(preg 'r0) ,label ,(map mkarg (iota argcount))))
	     (map (lambda (name) `(move-word ,(preg name) ,(junk))) killed-regs)
	     (map (lambda (name) `(use ,(preg name))) killed-regs)
	     (list`(move-word ,target ,(preg 'r0))))]
    [i
     (list i)]))

(define (expand-instructions init-arg-instrs instrs)
  (define saved-locs (map (lambda (r) (fresh-reg)) saved-regs))
  (define expander (expand-instruction saved-locs))
  (append (map (lambda (loc name) `(move-word ,loc ,(preg name))) saved-locs saved-regs)
	  (append-map expander init-arg-instrs)
	  (append-map expander instrs)))

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
	       [`(,(and op (or 'w+ 'w- 'w* 'wdiv 'wmod))
		  ,target
		  ,(? (lambda (v) (not (or (reg? v) (preg? v)))) s1)
		  ,s2)
		(define r (fresh-reg))
		(list `(move-word ,r ,s1)
		      `(,op ,target ,r ,s2))]
	       [`(compare ,cmpop ,target ,(? memory-location? n) ,(? memory-location? m))
		(define r (fresh-reg))
		(list `(move-word ,r ,m)
		      `(compare ,cmpop ,target ,n ,r))]
	       [`(load ,(temporary n) ,source ,offset)
		(define r (fresh-reg))
		(list `(load ,r ,source ,offset)
		      `(move-word ,(temporary n) ,r))]
	       [i
		(list i)])
	      instrs))

;; Stack frames need to account for
;;  - inward args numbered 4 and above
;;  - saved temporaries
;;  - being aligned to the nearest frame-alignment byte boundary
;;
;; Stacks are full descending.
;;  - Ni = inward-arg-count
;;  - Nt = inward-temp-count
;;  - Na = outward-arg-count
;;  - Af = frame-alignment
;;
;; inward(n) = rn, if n < 4
;;           | sp - (Ni - n - 4 - 1) * word-size-bytes
;; temp(n) = sp + (n + 1) * word-size-bytes
;; outward(n) = rn, if n < 4
;;            | sp + roundup((Na + Nt) * word-size-bytes, Af) - (Na - n - 4 - 1) * wordsizebytes
;;
;;  ...
;;  inward 4
;;  inward 5		<-- stack pointer (aligned to 16-byte boundary)
;;  ...
;;  temp 0
;;  temp 1
;;  ...
;;  temp n
;;  ...
;;  outward arg 0
;;  outward arg 1
;;  ...
;;  outward arg n	<-- soon to be stack pointer (aligned to 16-byte boundary)
;;

(define ((assemble-instr inward-arg-count temp-count) i)
  (define (xs v)
    (match v
      [(lit n) n]
      [(preg r) r]
      [(temporary n) (@reg 'sp '+ (* (+ n 1) word-size-bytes))]
      [(inward-arg n)
       (if (< n 4)
	   (list-ref '(r0 r1 r2 r3) n)
	   (@reg 'sp '- (* (- inward-arg-count n 4 1) word-size-bytes)))]
      [(outward-arg 'nontail outward-arg-count n)
       (if (< n 4)
	   (list-ref '(r0 r1 r2 r3) n)
	   (let ((delta
		  (round-up-to-nearest frame-alignment
				       (* (+ outward-arg-count temp-count)
					  word-size-bytes))))
	     (@reg 'sp '+ (- delta (* (- outward-arg-count n 4 1) word-size-bytes)))))]
      [(outward-arg 'tail outward-arg-count n)
       (if (< n 4)
	   (list-ref '(r0 r1 r2 r3) n)
	   (@reg 'sp '- (* (- inward-arg-count n 4 1) word-size-bytes)))]
      ))
  (match i
    [`(move-word ,target ,source)		(*mov 'al 0 (xs target) (xs source))]
    [`(load ,(preg target) ,(lit n) ,ofs)	(*mov 'al 0 target (@imm (+ n ofs)))]
    [`(w+ ,target ,s1 ,s2)			(*add 'al 0 (xs target) (xs s1) (xs s2))]
    [`(w- ,target ,s1 ,s2)			(*sub 'al 0 (xs target) (xs s1) (xs s2))]
    [`(w* ,target ,s1 ,s2)			(*mul 'al 0 (xs target) (xs s1) (xs s2))]
    [`(compare ,cmpop ,target ,s1 ,s2)
     ;; Let wolog cmpop be <. Then we wish to compute s1 - s2 and have
     ;; the comparison be true if the result of subtraction is
     ;; negative. Now, (*op 'cmp source target) is based around target
     ;; - source, so we need to make sure the arguments are in the
     ;; correct order.
     (define cc (case cmpop
		  ((<=s) 'le) ((<s) 'lt)
		  ((<=u) 'ls)
		  ((=) 'eq) ((<>) 'ne)
		  ((>s) 'gt) ((>=s) 'ge)
		  ((>u) 'hi)))
     (list (*cmp 'al (xs s1) (xs s2))
	   (*mov 'al (xs target) 0)
	   (*mov cc (xs target) 1))]
    [(label tag)
     (label-anchor tag)]
    [`(jmp-false ,(preg val) ,(label tag))
     (list (*cmp 'al val 0)
	   (*b 'eq (label-reference tag #f)))]
    [`(jmp ,(label tag))			(*b 'al (label-reference tag #f))]
    [`(ret ,(preg 'r0))				(*mov 'al 0 'pc 'lr)]
    [`(call ,(preg 'r0) ,(label tag) ,args)
     (define outward-arg-count (length args))
     (define delta (round-up-to-nearest frame-alignment
					(* (+ outward-arg-count temp-count)
					   word-size-bytes)))
     (list (*sub 'al 0 'sp delta)
	   (*bl 'al (label-reference tag #f))
	   (*add 'al 0 'sp delta))]
    [`(tailcall ,(preg 'r0) ,(label tag) ,args)
     (define delta (- (length args) inward-arg-count))
     (list (if (zero? delta)
	       '()
	       (*sub 'al 0 'sp (* delta word-size-bytes)))
	   (*b 'al (label-reference tag #f)))]
    [_ (error 'assemble-instr "Cannot assemble ~v" i)]))

(define ((assemble-instr* inward-arg-count temp-count) i)
  (define bs ((assemble-instr inward-arg-count temp-count) i))
  (write `(,i -> ,bs))
  (newline)
  (flush-output)
  bs)

(define (assemble inward-arg-count temp-count instrs)
  (define pre-linking (flatten (map (assemble-instr* inward-arg-count temp-count) instrs)))
  (write `(pre-linking ,pre-linking)) (newline) (flush-output)
  (define-values (linked relocs) (internal-link-32 pre-linking))
  (write `(relocations ,relocs)) (newline) (flush-output)
  (list->bytes linked))

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
