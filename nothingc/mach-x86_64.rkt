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

;; Concrete machine: x86_64.

(require racket/match)
(require (only-in racket/list append-map))
(require (only-in srfi/1 iota))
(require (only-in '#%foreign _int64))

(require "lir.rkt")
(require "linker.rkt")
(require "asm-x86_64.rkt")
(require "tailcall.rkt")
(require (only-in "machine.rkt" machine-description))

(provide machine-x86_64)

(define cc (calling-convention '(rdi rsi rdx rcx r8 r9)
			       0
			       (lambda (delta) (@reg 'rsp delta))
			       8
			       16 ;; must be a power of two
			       16 ;; rbp + rip
			       8  ;; space for rbp that we don't use right now
			       ))

(define killed-regs '(rax rcx rdx rsi rdi r8 r9 r10 r11))
(define saved-regs '(rbp rbx r12 r13 r14 r15))

;; At the moment putting the preferred register later in the list
;; makes it tried first. See the details of how the recursion in
;; find-available-register works.
(define available-regs (map (lambda (r) (preg r #f))
                            (append (reverse saved-regs)
                                    (reverse killed-regs))))

(define ((expand-instruction saved-locs) instr)
  (match instr
    [`(w*/extended ,hi ,lo ,s1 ,s2)
     (list `(move-word ,(preg 'rax #f) ,s1)
           `(move-word ,(preg 'rcx #f) ,s2)
           `(w*/extended ,(preg 'rdx #f) ,(preg 'rax #f) ,(preg 'rax #f) ,(preg 'rcx #f))
           `(move-word ,hi ,(preg 'rdx #f))
           `(move-word ,lo ,(preg 'rax #f)))]
    [`(wdiv ,target ,s1 ,s2)
     (list `(move-word ,(preg 'rdx #f) ,(lit 0))
	   `(move-word ,(preg 'rax #f) ,s1)
	   `(move-word ,(preg 'rcx #f) ,s2)
	   `(wdiv ,(preg 'rax #f) ,(preg 'rax #f) ,(preg 'rcx #f))
	   `(use ,(preg 'rdx #f))
	   `(move-word ,target ,(preg 'rax #f)))]
    [`(wmod ,target ,s1 ,s2)
     (list `(move-word ,(preg 'rdx #f) ,(lit 0))
	   `(move-word ,(preg 'rax #f) ,s1)
	   `(move-word ,(preg 'rcx #f) ,s2)
	   `(wmod ,(preg 'rax #f) ,(preg 'rax #f) ,(preg 'rcx #f))
	   `(use ,(preg 'rax #f))
	   `(move-word ,target ,(preg 'rdx #f)))]
    [`(compare/set ,cmpop ,target ,s1 ,s2)
     (list `(move-word ,(preg 'rax #f) ,s1)
	   `(compare/set ,cmpop ,(preg 'rax #f) ,(preg 'rax #f) ,s2)
	   `(move-word ,target ,(preg 'rax #f)))]
    [`(ret ,target)
     (append (list `(move-word ,(preg 'rax (lir-value-var target)) ,target))
	     (map (lambda (loc name) `(move-word ,(preg name #f) ,loc)) saved-locs saved-regs)
	     (map (lambda (name) `(use ,(preg name #f))) saved-regs)
	     (list `(ret ,(preg 'rax (lir-value-var target)))))]
    [`(call ,target ,label (,arg ...))
     (define argcount (length arg))
     (define (mkarg i) ((outward-argument-location cc) 'nontail argcount i))
     (append (do ((i 0 (+ i 1))
		  (arg arg (cdr arg))
		  (acc '() (cons `(move-word ,(mkarg i) ,(car arg))
				 acc)))
		 ((null? arg) (reverse acc)))
	     (list `(call ,(preg 'rax #f) ,label ,(map mkarg (iota argcount))))
	     (map (lambda (name) `(move-word ,(preg name #f) ,(junk))) killed-regs)
	     (map (lambda (name) `(use ,(preg name #f))) killed-regs)
	     (list `(move-word ,target ,(preg 'rax #f))))]
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
     (define rs (if (non-reg? source) (fresh-reg) source))
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
	   `(move-word ,(preg 'rcx #f) ,shift-amount)
	   `(wshift ,op ,target ,target ,(preg 'rcx #f)))]
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
    [`(w*/extended ,(preg 'rdx _) ,(preg 'rax _) ,(preg 'rax _) ,(preg r _))
     (*imul/extended r)]
    [`(wand ,target ,target ,source)			(*op 'and (xs source) (xs target))]
    [`(wor ,target ,target ,source)			(*op 'or (xs source) (xs target))]
    [`(wxor ,target ,target ,source)			(*op 'xor (xs source) (xs target))]
    [`(wdiv ,(preg 'rax _) ,(preg 'rax _) ,(preg r _))	(*div r)]
    [`(wmod ,(preg 'rax _) ,(preg 'rax _) ,(preg r _))	(*div r)]
    [`(wshift ,op ,target ,target ,amount)		(case op
							  [(<<) (*shl (xs amount) (xs target))]
							  [(>>u) (*shr (xs amount) (xs target))]
							  [(>>s) (*sar (xs amount) (xs target))])]
    [`(compare/set ,cmpop ,(preg 'rax _) ,(? lit? n) ,(? lit? m))
     (*mov (evaluate-cmpop cmpop (lit-val n) (lit-val m)) 'rax)]
    [`(compare/jmp ,cmpop ,(label tag) ,(? lit? n) ,(? lit? m))
     (if (not (zero? (evaluate-cmpop cmpop (lit-val n) (lit-val m))))
         (*jmp (label-reference tag))
         '())]
    [`(compare/set ,cmpop ,(preg 'rax _) ,s1 ,s2)
     (comparison-code cmpop (xs s1) (xs s2)
		      (lambda (cc)
			(list (*setcc-rax cc))))]
    [`(compare/jmp ,cmpop ,(label tag) ,s1 ,s2)
     (comparison-code cmpop (xs s1) (xs s2)
		      (lambda (cc)
			(list (*jmp-cc cc (label-reference tag)))))]
    [(label tag)					(label-anchor tag)]
    [`(jmp ,(label tag))				(*jmp (label-reference tag))]
    [`(ret ,(preg 'rax _))
     (list (if (zero? sp-delta) '() (*op 'add sp-delta 'rsp))
	   (*ret))]
    [`(call ,(preg 'rax _) ,target ,_)
     (*call (match target
	      [(label tag) (label-reference tag)]
	      [(preg r _) r]))]
    [`(tailcall ,target ,args)
     (list (if (zero? sp-delta) '() (*op 'add sp-delta 'rsp))
	   (*jmp (match target
		   [(label tag) (label-reference tag)]
		   [(preg r _) r])))]
    [_ (error 'assemble-instr "Cannot assemble ~v" i)]))

(define ((assemble-instr* xs sp-delta) i)
  (define bs ((assemble-instr xs sp-delta) i))
  ;; (write `(,i -> ,bs))
  ;; (newline)
  ;; (flush-output)
  bs)

(define (assemble inward-arg-count most-tail-args temp-count leaf? instrs)
  (define xs (make-location-resolver cc inward-arg-count most-tail-args temp-count leaf?))
  (define sp-delta (if leaf? 0 (compute-sp-delta cc most-tail-args temp-count)))
  (values (list (if (zero? sp-delta) '() (*op 'sub sp-delta 'rsp))
		(map (assemble-instr* xs sp-delta) instrs))
	  '()))

(define machine-x86_64
  (machine-description 'x86_64
		       (calling-convention-word-size cc)
		       _int64
		       available-regs
		       (inward-argument-location cc)
		       (outward-argument-location cc)
		       expand-instructions
		       expand-temporary-loads-and-stores
		       assemble))
