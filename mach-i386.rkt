#lang racket/base
;; Concrete machine: i386.

(require racket/list)
(require racket/match)
(require (only-in srfi/1 iota))

(require "lir.rkt")
(require "asm-i386.rkt")
(require (only-in "machine.rkt" machine-description))

(provide machine-i386)

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
  (define pre-linking (flatten (map (assemble-instr* inward-arg-count) instrs)))
  (write `(pre-linking ,pre-linking)) (newline) (flush-output)
  (define-values (linked relocs) (internal-link pre-linking))
  (write `(relocations ,relocs)) (newline) (flush-output)
  (list->bytes linked))

(define machine-i386
  (machine-description 'i386
		       available-regs
		       expand-instructions
		       expand-temporary-loads-and-stores
		       assemble))
