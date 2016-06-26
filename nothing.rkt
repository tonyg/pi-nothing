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

;; After "Nothing", the BCPL-like language from VPRI
;;  - an expression language with support for calls and tail calls

;; TODO: separate statements from expressions?

(require racket/match)
(require racket/list)

(require "lir.rkt")
(require "linker.rkt")

(provide frontend)

(define (field-type? x)
  (memq x '(word byte)))

(struct layout (fields) #:prefab)
(struct layout-field (name type) #:prefab)

;; (snippet (Listof Instr) (Constreeof MachineCode) Val)
(struct snippet (instrs data val) #:prefab)
(define (snip val . instrs) (snippet instrs '() val))

(struct binding (name val instrs data mutable?) #:prefab)

(define-syntax seq
  (syntax-rules ()
    [(seq () final ...)
     (let () final ...)]
    [(seq ([valname v] rest ...) final ...)
     (match v
       [(snippet instrs1 data1 valname)
	(match (seq (rest ...) final ...)
	  [(snippet instrs2 data2 finalval)
	   (snippet (append instrs1 instrs2)
		    (cons data1 data2)
		    finalval)])])]))

(define (real-dest? dest)
  (not (junk? dest)))

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
	      (match-define (snippet left-instrs left-data left-val) left-snippet)
	      (match-define (snippet right-instrs right-data right-val)
		(translate-exp #f (fresh-reg) right-rand env))
	      (snippet (append left-instrs
			       right-instrs
			       (if (real-dest? dest)
				   (list `(,instr-op ,dest ,left-val ,right-val))
				   (list)))
		       (cons left-data right-data)
		       dest))
	    (translate-exp #f (fresh-reg) (car rands) env)
	    (cdr rands))]))

(define (lookup varname env)
  (findf (lambda (b) (equal? varname (binding-name b))) env))

(define (translate-comparison target-t target-f run-through-on-true exp env)
  ;; Both target-t and target-f have to be real targets. Because a jmp
  ;; to one or the other will be a no-op, run-through-on-true is set
  ;; to #t if a `(jmp ,target-t) would be pointless, or #f if `(jmp
  ;; ,target-f) would be pointless.
  (define (cmp2 rator a b)
    (define cmpop (if run-through-on-true (negate-cmpop rator) rator))
    (define target (if run-through-on-true target-f target-t))
    (seq ([av (translate-exp #f (fresh-reg) a env)]
	  [bv (translate-exp #f (fresh-reg) b env)])
	 (snip (lit 0) `(compare/jmp ,cmpop ,target ,av ,bv))))
  (define (jmp-t) (if run-through-on-true (snip (lit 0)) (snip (lit 0) `(jmp ,target-t))))
  (define (jmp-f) (if run-through-on-true (snip (lit 0) `(jmp ,target-f)) (snip (lit 0))))
  (match exp
    [`(<=s ,a ,b) (cmp2 '<=s a b)]
    [`(<s ,a ,b) (cmp2 '<s a b)]
    [`(<=u ,a ,b) (cmp2 '<=u a b)]
    [`(<u ,a ,b) (cmp2 '<u a b)]
    [`(= ,a ,b) (cmp2 '= a b)]
    [`(<> ,a ,b) (cmp2 '<> a b)]
    [`(>s ,a ,b) (cmp2 '>s a b)]
    [`(>=s ,a ,b) (cmp2 '>=s a b)]
    [`(>u ,a ,b) (cmp2 '>u a b)]
    [`(>=u ,a ,b) (cmp2 '>=u a b)]

    [`(lognot ,rand) (translate-comparison target-f target-t (not run-through-on-true) rand env)]

    [`(logand) (jmp-t)]
    [`(logand ,r) (translate-comparison target-t target-f run-through-on-true r env)]
    [`(logand ,r ,rands ...)
     (define Lta (fresh-label))
     (seq ([av (translate-comparison Lta target-f #t r env)]
	   [labeldef (snip (lit 0) Lta)])
	  (translate-comparison target-t target-f run-through-on-true `(logand ,@rands) env))]

    [`(logor) (jmp-f)]
    [`(logor ,r) (translate-comparison target-t target-f run-through-on-true r env)]
    [`(logor ,r ,rands ...)
     (define Lfa (fresh-label))
     (seq ([av (translate-comparison target-t Lfa #f r env)]
	   [labeldef (snip (lit 0) Lfa)])
	  (translate-comparison target-t target-f run-through-on-true `(logor ,@rands) env))]))

(define (translate-exp tail? dest exp env)
  (match exp
    [(? number? val)
     (store-result dest (lit val))]

    [(? symbol? varname)
     (store-result dest (cond [(lookup varname env) => binding-val]
			      [else (label varname)]))]

    [`(let ,bindings ,body ...)
     (define rib (map (lambda (b)
			(define-values (mutable? name init-exp)
			  (match b
			    [`(mutable ,name ,init-exp) (values #t name init-exp)]
			    [`(,name ,init-exp) (values #f name init-exp)]))
			(define r (fresh-reg name))
			(match-define (snippet instrs data v) (translate-exp #f r init-exp env))
			(if (and (lit? v) (not mutable?))
			    (binding name v instrs data mutable?)
			    (binding name r instrs data mutable?)))
		      bindings))
     (match-define (snippet instrs data val)
       (translate-exp tail? dest `(begin ,@body) (append rib env)))
     (snippet (append (append* (map binding-instrs rib))
		      instrs)
	      (cons (map binding-data rib)
		    data)
	      val)]

    [`(begin)
     (store-result dest (lit 0))]

    [`(begin ,exp)
     (translate-exp tail? dest exp env)]

    [`(begin ,exp ,exps ...)
     (seq ([v (translate-exp #f (junk) exp env)])
	  (translate-exp tail? dest `(begin ,@exps) env))]

    [`(?volatile ,exp)
     (define temp-reg (fresh-reg))
     (seq ([v (translate-exp #f (fresh-reg) exp env)])
	  (snip dest
                `(load-word ,temp-reg ,v 0)
                `(use ,temp-reg)
                `(move-word ,dest ,temp-reg)))]
    [`(? ,exp)
     (seq ([v (translate-exp #f (fresh-reg) exp env)])
	  (snip dest `(load-word ,dest ,v 0)))]
    [`(?byte ,exp)
     (seq ([v (translate-exp #f (fresh-reg) exp env)])
	  (snip dest `(load-byte ,dest ,v 0)))]

    [`(! ,locexp ,valexp)
     (seq ([locv (translate-exp #f (fresh-reg) locexp env)]
	   [valv (translate-exp #f (if (real-dest? dest) dest (fresh-reg)) valexp env)])
	  (snip dest `(store-word ,locv ,valv)))]
    [`(!byte ,locexp ,valexp)
     (seq ([locv (translate-exp #f (fresh-reg) locexp env)]
	   [valv (translate-exp #f (if (real-dest? dest) dest (fresh-reg)) valexp env)])
	  (snip dest `(store-byte ,locv ,valv)))]

    [`(+ ,rands ...) (op2 tail? dest env 'w+ 0 rands)]
    [`(* ,rands ...) (op2 tail? dest env 'w* 1 rands)]
    [`(*/extended ,a1 ,a2 (,hi ,lo) ,body ...)
     (seq ([a1v (translate-exp #f (fresh-reg) a1 env)]
           [a2v (translate-exp #f (fresh-reg) a2 env)])
          (define r1 (fresh-reg hi))
          (define r2 (fresh-reg lo))
          (define rib (list (binding hi r1 '() '() #f)
                            (binding lo r2 '() '() #f)))
          (match-define (snippet instrs data val)
            (translate-exp tail? dest `(begin ,@body) (append rib env)))
          (snippet (cons `(w*/extended ,r1 ,r2 ,a1v ,a2v) instrs)
                   data
                   val))]

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
     (error 'translate-exp "(%) needs two or more arguments")]
    [`(% ,rands ...) (op2 tail? dest env 'wmod (void) rands)]

    [`(binand ,rands ...) (op2 tail? dest env 'wand -1 rands)]
    [`(binor ,rands ...) (op2 tail? dest env 'wor 0 rands)]
    [`(binxor ,rands ...) (op2 tail? dest env 'wxor 0 rands)]
    [`(,(and op (or '<< '>>s '>>u)) ,a ,b) 
     (seq ([av (translate-exp #f (fresh-reg) a env)]
	   [bv (translate-exp #f (fresh-reg) b env)])
	  (snip dest `(wshift ,op ,dest ,av ,bv)))]

    [`(binnot ,rand)
     (seq ([v (translate-exp #f dest rand env)])
	  (snip dest `(wnot ,dest ,dest)))]

    [`(return ,exp)
     (seq ([v (translate-exp #t dest exp env)])
	  (snip dest `(ret ,v)))]

    [`(when ,test ,body ...)
     ;; TODO: decide what to do wrt putting a value into dest in the
     ;; case that the test evaluates to false. At the moment it uses
     ;; whatever junk is lying around (!)
     (define Ltrue (fresh-label))
     (define Ldone (fresh-label))
     (seq ([testv (translate-comparison Ltrue Ldone #t test env)])
	  (match-define (snippet bi bd bv) (translate-exp tail? dest `(begin ,@body) env))
	  (snippet (append (list Ltrue)
			   bi
			   (list Ldone))
		   bd
                   (lit 0)))]

    [`(if ,test ,texp ,fexp)
     (define Ltrue (fresh-label))
     (define Lfalse (fresh-label))
     (define Ldone (fresh-label))
     (seq ([testv (translate-comparison Ltrue Lfalse #t test env)])
	  (match-define (snippet ti td tv) (translate-exp tail? dest texp env))
	  (match-define (snippet fi fd fv) (translate-exp tail? dest fexp env))
	  (snippet (append (list Ltrue)
			   ti
			   (list (if tail? `(ret ,dest) `(jmp ,Ldone))
				 Lfalse)
			   fi
			   (if tail? (list) (list Ldone)))
		   (cons td fd)
		   dest))]

    [`(cond)
     (store-result dest (lit 0))]

    [`(cond [else ,e ...])
     (translate-exp tail? dest `(begin ,@e) env)]

    [`(cond [,t ,e ...] ,rest ...)
     (translate-exp tail? dest `(if ,t (begin ,@e) (cond ,@rest)) env)]

    [`(while ,test ,body ...)
     (define Ltop (fresh-label))
     (define Lbodystart (fresh-label))
     (define Ldone (fresh-label))
     (match-define (snippet testi testd testv) (translate-comparison Lbodystart Ldone #t test env))
     (match-define (snippet bodyi bodyd bodyv) (translate-exp #f (fresh-reg) `(begin ,@body) env))
     (snippet (append (list Ltop)
		      testi
		      (list Lbodystart)
		      bodyi
		      (list `(jmp ,Ltop)
			    Ldone))
	      (cons testd bodyd)
	      (lit 0))]

    [`(set! ,varname ,val)
     (seq ([valv (translate-exp #f (fresh-reg) val env)])
	  (match (lookup varname env)
	    [(binding _ reg _ _ #t)
	     (snip reg `(move-word ,reg ,valv))]
	    [#f
	     (error 'translate "Unbound variable ~a in set!" varname)]
	    [_
	     (error 'translate "Immutable variable ~a in set!" varname)]))]

    [`(data ,ds ...)
     (define L (fresh-label))
     (snippet (list `(move-word ,dest ,L))
	      (list (label-anchor (label-tag L)) ds)
	      dest)]

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
			     (list `(tailcall ,rator-v ,(map snippet-val rand-snips))))
		     (map snippet-data rand-snips)
		     dest)]
	   [(real-dest? dest)
	    ;; Nontail call and we care about the result
	    (snippet (append (append* (map snippet-instrs rand-snips))
			     (list `(call ,dest ,rator-v ,(map snippet-val rand-snips))))
		     (map snippet-data rand-snips)
		     dest)]
	   [else
	    ;; Nontail call and we don't care about the result
	    (snippet (append (append* (map snippet-instrs rand-snips))
			     (list `(call ,(fresh-reg) ,rator-v ,(map snippet-val rand-snips))))
		     (map snippet-data rand-snips)
		     (lit 0))]))]

    ))

(define (frontend proc-name exp raw-env)
  (define target-reg (fresh-reg (string->symbol (format "$result$_~a" proc-name))))
  (define env (map (lambda (e) (binding (car e) (cadr e) '() '() #f)) raw-env))
  (match-define (snippet body-instrs body-data val) (translate-exp #t target-reg exp env))
  (values (append body-instrs
		  (list `(ret ,val)))
	  body-data))
