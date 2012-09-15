#lang racket/base
;; Concrete machine: x86_64.

(require racket/list)
(require racket/match)
(require (only-in srfi/1 iota))
(require (only-in '#%foreign _int64))

(require "lir.rkt")
(require "asm-x86_64.rkt")
(require (only-in "machine.rkt" machine-description))

(provide machine-x86_64)

;; At the moment putting the preferred register later in the list
;; makes it tried first. See the details of how the recursion in
;; find-available-register works.
(define available-regs (map preg (list
				  'r8 'r9 'r10 'r11 'r12 'r13 'r14 'r15
				  'rbx 'rcx 'rdx 'rsi 'rdi 'rax
				  )))

(define word-size-bytes 8)
(define frame-alignment 32) ;; must be a power of two
(define linkage-size 16) ;; ebp + eip

(define killed-regs '(rcx rdx rsi rdi rax r8 r9 r10 r11))
(define saved-regs '(rbx r12 r13 r14 r15))

(define (inward-argument-location i)
  (case i
    ((0) (preg 'rdi))
    ((1) (preg 'rsi))
    ((2) (preg 'rdx))
    ((3) (preg 'rcx))
    ((4) (preg 'r8))
    ((5) (preg 'r9))
    (else (inward-arg (- i 6)))))

(define (outward-argument-location calltype count i)
  (case i
    ((0) (preg 'rdi))
    ((1) (preg 'rsi))
    ((2) (preg 'rdx))
    ((3) (preg 'rcx))
    ((4) (preg 'r8))
    ((5) (preg 'r9))
    (else (outward-arg calltype count (- i 6)))))

(define ((expand-instruction saved-locs) instr)
  (match instr
    [`(wdiv ,target ,s1 ,s2)
     (list `(move-word ,(preg 'rdx) ,(lit 0))
	   `(move-word ,(preg 'rax) ,s1)
	   `(move-word ,(preg 'rcx) ,s2)
	   `(wdiv ,(preg 'rax) ,(preg 'rax) ,(preg 'rcx))
	   `(use ,(preg 'rdx))
	   `(move-word ,target ,(preg 'rax)))]
    [`(wmod ,target ,s1 ,s2)
     (list `(move-word ,(preg 'rdx) ,(lit 0))
	   `(move-word ,(preg 'rax) ,s1)
	   `(move-word ,(preg 'rcx) ,s2)
	   `(wmod ,(preg 'rax) ,(preg 'rax) ,(preg 'rcx))
	   `(use ,(preg 'rax))
	   `(move-word ,target ,(preg 'rdx)))]
    [`(compare ,cmpop ,target ,s1 ,s2)
     (list `(move-word ,(preg 'rax) ,s1)
	   `(compare ,cmpop ,(preg 'rax) ,(preg 'rax) ,s2)
	   `(move-word ,target ,(preg 'rax)))]
    [`(ret ,target)
     (append (list `(move-word ,(preg 'rax) ,target))
	     (map (lambda (loc name) `(move-word ,(preg name) ,loc)) saved-locs saved-regs)
	     (map (lambda (name) `(use ,(preg name))) saved-regs)
	     (list `(ret ,(preg 'rax))))]
    [`(,(and op (or 'call 'tailcall)) ,target ,label (,arg ...))
     (define argcount (length arg))
     (define calltype (if (eq? op 'tailcall) 'tail 'nontail))
     (define (mkarg i) (outward-argument-location calltype argcount i))
     (append (if (eq? calltype 'tail)
		 (list `(use ,(preg 'rax))) ;; need a scratch reg
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
	     (list `(,op ,(preg 'rax) ,label ,(map mkarg (iota argcount)))
		   `(cleanup-call ,calltype ,argcount))
	     (map (lambda (name) `(move-word ,(preg name) ,(junk))) killed-regs)
	     (map (lambda (name) `(use ,(preg name))) killed-regs)
	     (list`(move-word ,target ,(preg 'rax))))]
    [i
     (list i)]))

(define (expand-instructions init-arg-instrs instrs)
  (define saved-locs (map (lambda (r) (fresh-reg)) saved-regs))
  (define expander (expand-instruction saved-locs))
  ;; TODO: revisit the question of whether we get better register
  ;; allocation with the init-arg-instrs before or after the
  ;; register-saving instrs. Little practical evidence either way at
  ;; present, and I haven't thought the question through to see if in
  ;; theory it should behave better one way or the other.
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
	       [`(,(and op (or 'w+ 'w- 'w* 'wdiv 'wmod)) ,target ,s1 ,s2)
		(shuffle-for-two-args (lambda (o i1 i2) `(,op ,o ,i1 ,i2))
				      target
				      s1
				      s2)]
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
      [(temporary n) (@reg 'rbp (- (* word-size-bytes (+ n 1))))]
      [(inward-arg n) (@reg 'rbp (* word-size-bytes (+ n 2)))]
      [(outward-arg 'nontail _ n) (@reg 'rsp (* word-size-bytes n))]
      [(outward-arg 'tail outward-arg-count n)
       (@reg 'rbp (* word-size-bytes (- (+ n 2) (- outward-arg-count inward-arg-count))))]
      ))
  (match i
    [`(move-word ,target ,source)			(*mov (xs source) (xs target))]
    [`(load ,(preg target) ,(lit n) ,ofs)		(*mov (@imm (+ n ofs)) target)]
    [`(w+ ,target ,target ,source)			(*op 'add (xs source) (xs target))]
    [`(w- ,target ,target ,source)			(*op 'sub (xs source) (xs target))]
    [`(w* ,target ,target ,source)			(*imul (xs source) (xs target))]
    [`(wdiv ,(preg 'rax) ,(preg 'rax) ,(preg r))	(*div r)]
    [`(wmod ,(preg 'rax) ,(preg 'rax) ,(preg r))	(*div r)]
    [`(compare ,cmpop ,(preg 'rax) ,s1 ,s2)
     ;; Let wolog cmpop be <. Then we wish to compute s1 - s2 and have
     ;; the comparison be true if the result of subtraction is
     ;; negative. Now, (*op 'cmp source target) is based around target
     ;; - source, so we need to make sure the arguments are in the
     ;; correct order.
     (define cc (case cmpop
		  ((<=s) 'le) ((<s) 'l)
		  ((<=u) 'be) ((<u) 'b)
		  ((=) 'e) ((<>) 'ne)
		  ((>s) 'g) ((>=s) 'ge)
		  ((>u) 'a) ((>=u) 'ae)))
     (list (*op 'cmp (xs s2) (xs s1))
	   (*setcc-rax cc))]
    [`(prepare-call nontail ,arg-count)
     (if (zero? arg-count)
	 '()
	 (*op 'sub (round-up-to-nearest frame-alignment (* arg-count word-size-bytes)) 'rsp))]
    [`(prepare-call tail ,arg-count)
     (define delta (- arg-count inward-arg-count))
     ;; move saved ebp and saved eip DOWN in memory by delta words
     ;; because ebp is lower in memory, move it first
     ;; rax is our scratch reg by convention - see expand-instructions
     (if (zero? delta)
	 '()
	 (list (*mov (@reg 'rbp 0) 'rax)
	       (*mov 'rax (@reg 'rbp (- (* delta word-size-bytes))))
	       (*mov (@reg 'rbp word-size-bytes) 'rax)
	       (*mov 'rax (@reg 'rbp (+ word-size-bytes (- (* delta word-size-bytes)))))))]
    [`(cleanup-call nontail ,arg-count)
     (if (zero? arg-count)
	 '()
	 (*op 'add (round-up-to-nearest frame-alignment (* arg-count word-size-bytes)) 'rsp))]
    [`(cleanup-call tail ,_)				'()]
    [(label tag)					(label-anchor tag)]
    [`(jmp-false ,(preg val) ,(label tag))
     (list (*op 'cmp 0 val)
	   (*jmp-cc 'z (label-reference tag #f)))]
    [`(jmp ,(label tag))				(*jmp (label-reference tag #f))]
    [`(ret ,(preg 'rax))				(list (*leave) (*ret))]
    [`(call ,(preg 'rax) ,(label tag) ,_)		(*call (label-reference tag #f))]
    [`(tailcall ,(preg 'rax) ,(label tag) ,args)
     (define delta (- (length args) inward-arg-count))
     (list (if (zero? delta)
	       '()
	       (*op 'sub (* delta word-size-bytes) 'rbp))
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
  (define temp-size (* temp-count word-size-bytes))
  (define total-requirement (+ temp-size linkage-size))
  (define frame-size (round-up-to-nearest frame-alignment total-requirement))
  (define delta (- frame-size linkage-size))

  (define pre-linking (flatten (list (*push 'rbp)
				     (*mov 'rsp 'rbp)
				     (*op 'sub delta 'rsp)
				     (map (assemble-instr* inward-arg-count temp-count) instrs))))
  (write `(pre-linking ,pre-linking)) (newline) (flush-output)

  (define-values (linked relocs) (internal-link-64 pre-linking))
  (write `(relocations ,relocs)) (newline) (flush-output)
  (list->bytes linked))

(define machine-x86_64
  (machine-description 'x86_64
		       word-size-bytes
		       _int64
		       available-regs
		       inward-argument-location
		       outward-argument-location
		       expand-instructions
		       expand-temporary-loads-and-stores
		       assemble))
