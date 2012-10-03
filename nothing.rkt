#lang racket/base
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

(define (cmp2 dest env rator a b)
  (seq ([av (translate-exp #f (fresh-reg) a env)]
	[bv (translate-exp #f (fresh-reg) b env)])
       (snip dest `(compare ,rator ,dest ,av ,bv))))

(define (lookup varname env)
  (findf (lambda (b) (equal? varname (binding-name b))) env))

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
			(define r (fresh-reg))
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
     (seq ([v (translate-exp #f (void) exp env)])
	  (translate-exp tail? dest `(begin ,@exps) env))]

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

    [`(<=s ,a ,b) (cmp2 dest env '<=s a b)]
    [`(<s ,a ,b) (cmp2 dest env '<s a b)]
    [`(<=u ,a ,b) (cmp2 dest env '<=u a b)]
    [`(<u ,a ,b) (cmp2 dest env '<u a b)]
    [`(= ,a ,b) (cmp2 dest env '= a b)]
    [`(<> ,a ,b) (cmp2 dest env '<> a b)]
    [`(>s ,a ,b) (cmp2 dest env '>s a b)]
    [`(>=s ,a ,b) (cmp2 dest env '>=s a b)]
    [`(>u ,a ,b) (cmp2 dest env '>u a b)]
    [`(>=u ,a ,b) (cmp2 dest env '>=u a b)]

    [`(and ,rands ...) (op2 tail? dest env 'wand -1 rands)]
    [`(or ,rands ...) (op2 tail? dest env 'wor 0 rands)]
    [`(xor ,rands ...) (op2 tail? dest env 'wxor 0 rands)]
    [`(,(and op (or '<< '>>s '>>u)) ,a ,b) 
     (seq ([av (translate-exp #f dest a env)]
	   [bv (translate-exp #f (fresh-reg) b env)])
	  (snip dest `(wshift ,op ,dest ,av ,bv)))]

    [`(~ ,rand)
     (seq ([v (translate-exp #f dest rand env)])
	  (snip dest `(wnot ,dest ,dest)))]

    [`(not ,rand)
     (seq ([v (translate-exp #f dest rand env)])
	  (snip dest
		`(wnot ,dest ,dest)
		`(wand ,dest ,dest ,(lit 1))))]

    [`(return ,exp)
     (seq ([v (translate-exp #t dest exp env)])
	  (snip dest `(ret ,v)))]

    [`(when ,test ,body ...)
     ;; TODO: decide what to do wrt putting a value into dest in the
     ;; case that the test evaluates to false. At the moment it uses
     ;; whatever junk is lying around (!)
     (define Ldone (fresh-label))
     (seq ([testv (translate-exp #f (fresh-reg) test env)])
	  (match-define (snippet bi bd bv) (translate-exp tail? dest `(begin ,@body) env))
	  (snippet (append (list `(jmp-false ,testv ,Ldone))
			   bi
			   (list Ldone))
		   bd
		   dest))]

    [`(if ,test ,texp ,fexp)
     (define Lfalse (fresh-label))
     (define Ldone (fresh-label))
     (seq ([testv (translate-exp #f (fresh-reg) test env)])
	  (match-define (snippet ti td tv) (translate-exp tail? dest texp env))
	  (match-define (snippet fi fd fv) (translate-exp tail? dest fexp env))
	  (snippet (append (list `(jmp-false ,testv ,Lfalse))
			   ti
			   (list (if tail? `(ret ,dest) `(jmp ,Ldone))
				 Lfalse)
			   fi
			   (if tail? (list) (list Ldone)))
		   (cons td fd)
		   dest))]

    [`(cond)
     (store-result dest (lit 0))]

    [`(cond [,t ,e ...] ,rest ...)
     (translate-exp tail? dest `(if ,t (begin ,@e) (cond ,@rest)) env)]

    [`(while ,test ,body ...)
     (define Ltop (fresh-label))
     (define Ldone (fresh-label))
     (match-define (snippet testi testd testv) (translate-exp #f (fresh-reg) test env))
     (match-define (snippet bodyi bodyd bodyv) (translate-exp #f (fresh-reg) `(begin ,@body) env))
     (snippet (append (list Ltop)
		      testi
		      (list `(jmp-false ,testv ,Ldone))
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
			     (list `(tailcall ,dest ,rator-v ,(map snippet-val rand-snips))))
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

(define (frontend exp raw-env)
  (define target-reg (fresh-reg))
  (define env (map (lambda (e) (binding (car e) (cadr e) '() '() #f)) raw-env))
  (match-define (snippet body-instrs body-data val) (translate-exp #t target-reg exp env))
  (values (append body-instrs
		  (list `(ret ,val)))
	  body-data))
