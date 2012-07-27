#lang racket/base
;; After "Nothing", the BCPL-like language from VPRI
;;  - an expression language with support for calls and tail calls

;; TODO: separate statements from expressions?

(require racket/match)
(require racket/list)

(require "lir.rkt")

(provide frontend)

(define (field-type? x)
  (memq x '(word byte)))

(struct layout (fields) #:prefab)
(struct layout-field (name type) #:prefab)

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

(define (frontend exp env)
  (define target-reg (fresh-reg))
  (match-define (snippet body-instrs val) (translate-exp #t target-reg exp env))
  (append body-instrs
	  (list `(ret ,val))))