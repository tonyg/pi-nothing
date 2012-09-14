#lang racket/base
;; Concrete machine: ARMv7.

(require racket/match)
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
				       'r3 'r2 'r1 'r0)))

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
	     (list `(prepare-call ,calltype ,argcount))
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
	     (list `(,op ,(preg 'r0) ,label ,(map mkarg (iota argcount)))
		   `(cleanup-call ,calltype ,argcount))
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
		  ,(? memory-location? s1)
		  ,(? memory-location? s2))
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

(define ((assemble-instr inward-arg-count temp-count) i)
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
    [`(move-word ,target ,source)			(*mov (xs source) (xs target))]
    [`(load ,(preg target) ,(lit n) ,ofs)		(*mov (@imm (+ n ofs)) target)]
    [`(w+ ,target ,target ,source)			(*op 'add (xs source) (xs target))]
    [`(w- ,target ,target ,source)			(*op 'sub (xs source) (xs target))]
    [`(w* ,target ,target ,source)			(*imul (xs source) (xs target))]
    [`(wdiv ,(preg 'eax) ,(preg 'eax) ,(preg r))	(*div r)]
    [`(wmod ,(preg 'eax) ,(preg 'eax) ,(preg r))	(*div r)]
    [`(compare ,cmpop ,(preg 'eax) ,s1 ,s2)
     ;; Let wolog cmpop be <. Then we wish to compute s1 - s2 and have
     ;; the comparison be true if the result of subtraction is
     ;; negative. Now, (*op 'cmp source target) is based around target
     ;; - source, so we need to make sure the arguments are in the
     ;; correct order.
     (define cc (case cmpop ((<=) 'le) ((<) 'l) ((=) 'e) ((<>) 'ne) ((>) 'g) ((>=) 'ge)))
     (list (*op 'cmp (xs s2) (xs s1))
	   (*setcc-eax cc))]
    [`(prepare-call nontail ,arg-count)
     (if (zero? arg-count)
	 '()
	 (*op 'sub (round-up-to-nearest frame-alignment (* arg-count word-size-bytes)) 'esp))]
    [`(prepare-call tail ,arg-count)
     (define delta (- arg-count inward-arg-count))
     ;; move saved ebp and saved eip DOWN in memory by delta words
     ;; because ebp is lower in memory, move it first
     ;; r12 is our scratch reg by convention - see expand-instructions
     (if (zero? delta)
	 '()
	 (list (*mov (@reg 'ebp 0) 'eax)
	       (*mov 'eax (@reg 'ebp (- (* delta word-size-bytes))))
	       (*mov (@reg 'ebp word-size-bytes) 'eax)
	       (*mov 'eax (@reg 'ebp (+ word-size-bytes (- (* delta word-size-bytes)))))))]
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

(define ((assemble-instr* inward-arg-count temp-count) i)
  (define bs ((assemble-instr inward-arg-count temp-count) i))
  (write `(,i -> ,bs))
  (newline)
  (flush-output)
  bs)

(define (assemble inward-arg-count temp-count instrs)
  (define pre-linking (flatten (map (assemble-instr* inward-arg-count temp-count) instrs)))

    [`(enter ,n)
     (define temp-size (* n word-size-bytes))
     (define total-requirement (+ temp-size linkage-size))
     (define frame-size (round-up-to-nearest frame-alignment total-requirement))
     (define delta (- frame-size linkage-size))
     (list (*push 'ebp)
	   (*mov 'esp 'ebp)
	   (*op 'sub delta 'esp))]

  (write `(pre-linking ,pre-linking)) (newline) (flush-output)
  (define-values (linked relocs) (internal-link-32 pre-linking))
  (write `(relocations ,relocs)) (newline) (flush-output)
  (list->bytes linked))

(define machine-i386
  (machine-description 'i386
		       word-size-bytes
		       _int32
		       available-regs
		       inward-argument-location
		       outward-argument-location
		       expand-instructions
		       expand-temporary-loads-and-stores
		       assemble))
