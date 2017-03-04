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

;; Concrete machine: i386.

(require racket/match)
(require (only-in racket/list append-map))
(require (only-in srfi/1 iota))
(require (only-in '#%foreign _int32))

(require "lir.rkt")
(require "linker.rkt")
(require "asm-i386.rkt")
(require "tailcall.rkt")
(require (only-in "machine.rkt" machine-description))

(provide machine-i386)

(define cc (calling-convention '()
			       0
			       (lambda (delta) (@reg 'esp delta))
			       4
			       16
			       8 ;; ebp + eip
			       4 ;; space for ebp that we don't use right now
			       ))

(define killed-regs '(eax edx ecx))
(define saved-regs '(ebx esi edi ebp))

;; At the moment putting the preferred register later in the list
;; makes it tried first. See the details of how the recursion in
;; find-available-register works.
(define available-regs (map (lambda (r) (preg r #f))
                            (append
                             ;; '(ebp) ;; TODO: add EBP?
                             (reverse saved-regs)
                             (reverse killed-regs))))

(define ((expand-instruction saved-locs) instr)
  (match instr
    [`(w*/extended ,hi ,lo ,s1 ,s2)
     (list `(move-word ,(preg 'eax #f) ,s1)
           `(move-word ,(preg 'ecx #f) ,s2)
           `(w*/extended ,(preg 'edx #f) ,(preg 'eax #f) ,(preg 'eax #f) ,(preg 'ecx #f))
           `(move-word ,hi ,(preg 'edx #f))
           `(move-word ,lo ,(preg 'eax #f)))]
    [`(wdiv ,target ,s1 ,s2)
     (list `(move-word ,(preg 'edx #f) ,(lit 0))
	   `(move-word ,(preg 'eax #f) ,s1)
	   `(move-word ,(preg 'ecx #f) ,s2)
	   `(wdiv ,(preg 'eax #f) ,(preg 'eax #f) ,(preg 'ecx #f))
	   `(use ,(preg 'edx #f))
	   `(move-word ,target ,(preg 'eax #f)))]
    [`(wmod ,target ,s1 ,s2)
     (list `(move-word ,(preg 'edx #f) ,(lit 0))
	   `(move-word ,(preg 'eax #f) ,s1)
	   `(move-word ,(preg 'ecx #f) ,s2)
	   `(wmod ,(preg 'eax #f) ,(preg 'eax #f) ,(preg 'ecx #f))
	   `(use ,(preg 'eax #f))
	   `(move-word ,target ,(preg 'edx #f)))]
    [`(compare/set ,cmpop ,target ,s1 ,s2)
     (list `(move-word ,(preg 'eax #f) ,s1)
	   `(compare/set ,cmpop ,(preg 'eax #f) ,(preg 'eax #f) ,s2)
	   `(move-word ,target ,(preg 'eax #f)))]
    [`(ret ,target)
     (append (list `(move-word ,(preg 'eax (lir-value-var target)) ,target))
	     (map (lambda (loc name) `(move-word ,(preg name #f) ,loc)) saved-locs saved-regs)
	     (map (lambda (name) `(use ,(preg name #f))) saved-regs)
	     (list `(ret ,(preg 'eax (lir-value-var target)))))]
    [`(call ,target ,label (,arg ...))
     (define argcount (length arg))
     (define (mkarg i) ((outward-argument-location cc) 'nontail argcount i))
     (append (do ((i 0 (+ i 1))
		  (arg arg (cdr arg))
		  (acc '() (cons `(move-word ,(mkarg i) ,(car arg))
				 acc)))
		 ((null? arg) (reverse acc)))
	     (list `(call ,(preg 'eax #f) ,label ,(map mkarg (iota argcount))))
	     (map (lambda (name) `(move-word ,(preg name #f) ,(junk))) killed-regs)
	     (map (lambda (name) `(use ,(preg name #f))) killed-regs)
	     (list `(move-word ,target ,(preg 'eax #f))))]
    [`(tailcall ,label (,arg ...))
     (define argcount (length arg))
     (define (mkarg i) ((outward-argument-location cc) 'tail argcount i))
     (append (do ((i 0 (+ i 1))
		  (arg arg (cdr arg))
		  (acc '() (cons `(move-word ,(mkarg i) ,(car arg))
				 acc)))
		 ((null? arg) (reverse acc)))
             (map (lambda (loc name) `(move-word ,(preg name #f) ,loc)) saved-locs saved-regs)
             ;;(map (lambda (name) `(use ,(preg name #f))) saved-regs)
	     (list `(tailcall ,label ,(map mkarg (iota argcount)))))]
    [`(,(and op (or 'store-word 'store-byte)) ,target ,source)
     (define rt (if (non-reg? target) (fresh-reg) target))
     ;; Here we differ from the x86_64 equivalent logic, for
     ;; `store-byte` only, because we can only store bytes from AL,
     ;; CL, DL, BL or AH, CH, DH, BH. None of the low bytes of ESI,
     ;; EDI, ESP or EBP are available. We'd like to take any of EAX,
     ;; ECX, EDX or EBX here but the register allocator isn't flexible
     ;; enough to express this at the moment, so we hardcode it to EAX
     ;; and just hope that (a) byte stores aren't too frequent and (b)
     ;; whenever we do store a byte, EAX happens to be available.
     (define rs (cond [(eq? op 'store-byte) (preg 'eax (lir-value-var source))] ;; always replace
                      [(non-reg? source) (fresh-reg)] ;; store-word to something not a register
                      [else source])) ;; store-word to a register
     (list `(move-word ,rt ,target)
	   `(move-word ,rs ,source)
	   `(,op ,rt ,rs))]
    [`(wshift ,op ,(? reg-or-preg? target) ,(lit n) ,(lit m))
     (list `(move-word ,target ,(lit (arithmetic-shift n m))))]
    [`(wshift ,op ,(? reg-or-preg? target) ,n ,(lit m))
     (list `(move-word ,target ,n)
	   `(wshift ,op ,target ,target ,(lit m)))]
    [`(wshift ,op ,(? reg-or-preg? target) ,n ,shift-amount)
     (list `(move-word ,target ,n)
	   `(move-word ,(preg 'ecx #f) ,shift-amount)
	   `(wshift ,op ,target ,target ,(preg 'ecx #f)))]
    [i
     (list i)]))

(define (expand-instructions init-arg-instrs instrs)
  (define saved-locs (map (lambda (r) (fresh-reg)) saved-regs))
  (define expander (expand-instruction saved-locs))
  (append (map (lambda (loc name) `(move-word ,loc ,(preg name #f))) saved-locs saved-regs)
	  (append-map expander init-arg-instrs)
	  (append-map expander instrs)))

(define (evaluate-cmpop cmpop n m)
  (if (evaluate-cmpop32 cmpop n m) 1 0))

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
	       [`(,(and op (or 'w+ 'w- 'w* 'wand 'wor 'wxor 'wdiv 'wmod)) ,target ,s1 ,s2)
		(shuffle-for-two-args (lambda (o i1 i2) `(,op ,o ,i1 ,i2))
				      target
				      s1
				      s2)]
	       [`(compare/set ,cmpop ,target ,(? memory-location? n) ,(? memory-location? m))
		(define r (fresh-reg))
		(list `(move-word ,r ,m)
		      `(compare/set ,cmpop ,target ,n ,r))]
	       [`(compare/jmp ,cmpop ,target ,(? memory-location? n) ,(? memory-location? m))
		(define r (fresh-reg))
		(list `(move-word ,r ,m)
		      `(compare/jmp ,cmpop ,target ,n ,r))]
	       [`(,(and op (or 'load-word 'load-byte)) ,(temporary n var) ,source ,offset)
		(define r (fresh-reg))
		(list `(,op ,r ,source ,offset)
		      `(move-word ,(temporary n var) ,r))]
	       [`(,(and op (or 'store-word 'store-byte)) ,target ,(temporary n var))
		(define r (fresh-reg))
		(list `(move-word ,r ,(temporary n var))
		      `(,op ,target ,r))]
	       ;; [`(store-byte ,target ,source)
               ;;  #:when (match source
               ;;           [(preg (or 'eax 'ebx 'ecx 'edx) _) #f]
               ;;           [_ #t])
               ;;  ;; TODO: This feels sketchy. I can't remember whether
               ;;  ;; naming a *physical* register here is legit.
	       ;;  (define r (preg 'eax (lir-value-var source)))
	       ;;  (list `(move-word ,r ,source)
	       ;;        `(store-byte ,target ,r))]
               [`(call ,target ,(? memory-location? proc) ,args)
                (define r (fresh-reg))
                (list `(move-word ,r ,proc)
                      `(call ,target ,r ,args))]
	       [i
		(list i)])
	      instrs))

(define (comparison-code cmpop real-s1 real-s2 k)
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
  (cons (*op 'cmp real-s2 real-s1)
	(k cc)))

(define ((assemble-instr xs sp-delta) i)
  (match i
    [`(move-word ,target ,source)			(*mov (xs source) (xs target))]
    [`(load-word ,(preg target _) ,(preg source _) ,o)	(*mov (@reg source o) target)]
    [`(load-byte ,(preg target _) ,(preg source _) ,o)	(*movz (@reg source o) target)]
    [`(load-word ,(preg target _) ,(lit n) ,ofs)	(*mov (@imm (+ n ofs)) target)]
    [`(load-byte ,(preg target _) ,(lit n) ,ofs)	(*movz (@imm (+ n ofs)) target)]
    [`(store-word ,(preg target _) ,(preg source _))	(*mov source (@reg target 0))]
    [`(store-byte ,(preg target _) ,(preg source _))	(*mov source (@reg target 0) #t)]
    [`(w+ ,target ,target ,source)			(*op 'add (xs source) (xs target))]
    [`(w- ,target ,target ,source)			(*op 'sub (xs source) (xs target))]
    [`(w* ,target ,target ,source)			(*imul (xs source) (xs target))]
    [`(w*/extended ,(preg 'edx _) ,(preg 'eax _) ,(preg 'eax _) ,(preg r _))
     (*imul/extended r)]
    [`(wand ,target ,target ,source)			(*op 'and (xs source) (xs target))]
    [`(wor ,target ,target ,source)			(*op 'or (xs source) (xs target))]
    [`(wxor ,target ,target ,source)			(*op 'xor (xs source) (xs target))]
    [`(wdiv ,(preg 'eax _) ,(preg 'eax _) ,(preg r _))	(*div r)]
    [`(wmod ,(preg 'eax _) ,(preg 'eax _) ,(preg r _))	(*div r)]
    [`(wshift ,op ,target ,target ,amount)		(case op
							  [(<<) (*shl (xs amount) (xs target))]
							  [(>>u) (*shr (xs amount) (xs target))]
							  [(>>s) (*sar (xs amount) (xs target))])]
    [`(compare/set ,cmpop ,(preg 'eax _) ,(? lit? n) ,(? lit? m))
     (*mov (evaluate-cmpop cmpop (lit-val n) (lit-val m)) 'eax)]
    [`(compare/jmp ,cmpop ,(label tag) ,(? lit? n) ,(? lit? m))
     (if (not (zero? (evaluate-cmpop cmpop (lit-val n) (lit-val m))))
         (*jmp (label-reference tag))
         '())]
    [`(compare/set ,cmpop ,(preg 'eax _) ,s1 ,s2)
     (comparison-code cmpop (xs s1) (xs s2)
		      (lambda (cc)
			(list (*setcc-eax cc))))]
    [`(compare/jmp ,cmpop ,(label tag) ,s1 ,s2)
     (comparison-code cmpop (xs s1) (xs s2)
		      (lambda (cc)
			(list (*jmp-cc cc (label-reference tag)))))]
    [(label tag)					(label-anchor tag)]
    [`(jmp ,(label tag))				(*jmp (label-reference tag))]
    [`(ret ,(preg 'eax _))
     (list (if (zero? sp-delta) '() (*op 'add sp-delta 'esp))
	   (*ret))]
    [`(call ,(preg 'eax _) ,target ,_)
     (*call (match target
	      [(label tag) (label-reference tag)]
	      [(preg r _) r]))]
    [`(tailcall ,target ,args)
     (list (if (zero? sp-delta) '() (*op 'add sp-delta 'esp))
	   (*jmp (match target
		   [(label tag) (label-reference tag)]
		   [(preg r _) r])))]
    [_ (error 'assemble-instr "Cannot assemble ~v" i)]))

(define ((assemble-instr* xs sp-delta) i)
  (define bs ((assemble-instr xs sp-delta) i))
  (write `(,i -> ,bs))
  (newline)
  (flush-output)
  bs)

(define (assemble inward-arg-count most-tail-args temp-count leaf? instrs)
  (define xs (make-location-resolver cc inward-arg-count most-tail-args temp-count leaf?))
  (define sp-delta (if leaf? 0 (compute-sp-delta cc most-tail-args temp-count)))
  (values (list (if (zero? sp-delta) '() (*op 'sub sp-delta 'esp))
		(map (assemble-instr* xs sp-delta) instrs))
	  '()))

(define machine-i386
  (machine-description 'i386
		       (calling-convention-word-size cc)
		       _int32
		       available-regs
		       (inward-argument-location cc)
		       (outward-argument-location cc)
		       expand-instructions
		       expand-temporary-loads-and-stores
		       assemble))
