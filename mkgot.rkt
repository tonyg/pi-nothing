#lang racket
;; Experiment with production of an x86_64 Global Offset Table for dynamic linking

(require bitsyntax)

(require "dump-bytes.rkt")
(require "disasm.rkt")
(require "asm-x86_64.rkt")
(require "linker.rkt")
(require "elf.rkt")

(define origin-addr #x0000000000400000)
(define start-offset #x1000) ;; need to skip past the ELF header.
(define start-addr (+ origin-addr start-offset))

(define plt ;; procedure linkage table
  (list (label-anchor 'plt-trapunbound)
        (*push (@imm (label-reference 'got-fixup0)))
        (*jmp (@imm (label-reference 'got-fixup1)))

        (label-anchor 'exitstub)
        (*jmp (@imm (label-reference 'got-exitloc)))
        (label-anchor 'exitunbound)
        (*pushl 0) ;; index into relocation table
        (*jmp (label-reference 'plt-trapunbound))

        (label-anchor 'addsharedvarstub)
        (*jmp (@imm (label-reference 'got-addsharedvarloc)))
        (label-anchor 'addsharedvarunbound)
        (*pushl 1) ;; index into relocation table
        (*jmp (label-reference 'plt-trapunbound))

        ))

(define shared-data
  (list (label-anchor 'shared-data-top)

        (label-anchor 'sharedvar-loc)
        (imm64-abs 0)))

(define got ;; global offset table
  (for/list [(entry `((got-top 0)
                      (got-fixup0 0)
                      (got-fixup1 0)
                      (got-exitloc ,(label-reference 'exitunbound))
                      (got-addsharedvarloc ,(label-reference 'addsharedvarunbound))))]
    (match-define (list labelname value) entry)
    (list (label-anchor labelname) (imm64-abs value))))

(define code
  (list (*mov (@imm (label-reference 'sharedvar-loc)) 'rdi)
        (*mov (@reg 'rdi 0) 'rdi)
        (*call (label-reference 'addsharedvarstub))
        (*sar 2 'rax)
        (*mov 'rax 'rdi)
        (*call (label-reference 'exitstub))
        (label-anchor 'loopforever)
        (*jmp (label-reference 'loopforever))))

(define all-blobs
  (list code plt shared-data got))

(define-values (linked0 relocs link-map) (link all-blobs start-addr))

(define linked (list->bytes linked0))

(define (lookup-label name)
  (cdr (assoc (label-anchor name) link-map)))

;; Depends on r.so produced using "gcc -O0 -fPIC -shared -o r.so r.c"
;; where r.c contains:
;;
;; int sharedvar = 123;
;; int addsharedvar(int arg) {
;;   return arg + sharedvar;
;; }

(write-executable "got.elf"
                  (elf64-executable #:image linked
                                    #:machine 'x86_64
                                    #:origin origin-addr
                                    #:start-offset start-offset
                                    #:shared-data-address (lookup-label 'shared-data-top)
                                    #:got-address (lookup-label 'got-top)
                                    #:interpreter #"/lib64/ld-linux-x86-64.so.2"
                                    #:shared-data-symbols
                                    (list (dynamic-symbol #"sharedvar" #"r.so"))
                                    #:shared-function-symbols
                                    (list (dynamic-symbol #"exit" #"libc.so.6")
                                          (dynamic-symbol #"addsharedvar" #"r.so"))))
