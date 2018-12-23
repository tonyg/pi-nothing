#lang racket
;; Experiment with production of an ARM Global Offset Table for dynamic linking

(require bitsyntax)

(require "dump-bytes.rkt")
(require "disasm.rkt")
(require "asm-arm7.rkt")
(require "linker.rkt")
(require "elf.rkt")

(define origin-addr #x0000000000400000)
(define start-offset #x1000) ;; need to skip past the ELF header.
(define start-addr (+ origin-addr start-offset))

(define plt ;; procedure linkage table
  ;;
  ;; From reading glibc-2.24/sysdeps/arm/dl-trampoline.S, we see that
  ;; the trampoline expects to have
  ;;  - stack[0] = the return address from the call to the stub
  ;;  - ip contains a pointer to the GOT slot to modify
  ;;  - lr contains a pointer to GOT slot number 2, which holds the trampoline address
  ;;
  ;; Code emitted by (presumably) binutils ld is quite clever; here's
  ;; a sample, showing the trap code followed by a couple of PLT
  ;; stubs:
  ;;
  ;;   011AA0 E52DE004 STR     lr, [sp, #-4]!
  ;;   011AA4 E59FE004 LDR     lr, &00011AB0
  ;;   011AA8 E08FE00E ADD     lr, pc, lr
  ;;   011AAC E5BEF008 LDR     pc, [lr, #8]!
  ;;   011AB0 00022550 ANDEQ   r2, r2, r0, ASR r5
  ;;
  ;;   011AB4 E28FC600 ADR     ip, &00011ABC  ; [unexpected bits]
  ;;   011AB8 E28CCA22 ADD     ip, ip, #&22000
  ;;   011ABC E5BCF550 LDR     pc, [ip, #&550]!
  ;;
  ;;   011AC0 E28FC600 ADR     ip, &00011AC8  ; [unexpected bits]
  ;;   011AC4 E28CCA22 ADD     ip, ip, #&22000
  ;;   011AC8 E5BCF548 LDR     pc, [ip, #&548]!
  ;;
  ;; Notice the "!" at the end of the various LDR instructions, which
  ;; cause post-load updates to whichever index pointer is being used.
  ;; So, for instance, the instruction at 0x11AAC updates lr to lr+8
  ;; just before jumping, and the one at 0x11ABC updates ip to
  ;; ip+0x550 just before jumping.
  ;;
  ;; I don't want to get that fancy! Instead I'm going to go for a
  ;; crude, simple approach:
  ;;
  ;;      STR lr, [sp, #-4]!
  ;;      LDR lr, 1f
  ;;      LDR pc, [lr]
  ;;   1: .data <actual hard-coded offset to GOT+8>
  ;;
  ;;      LDR ip, 1f
  ;;      LDR pc, [ip]
  ;;   1: .data <actual hard-coded offset to GOT+(4*n)>
  ;;
  (list (label-anchor 'plt-trapunbound)
        (*str 'al 'lr (@pre (@reg 'sp '- 4)))
        (*ldr 'al 'lr (@reg 'pc '+ (- 8 8)))
        (*ldr 'al 'pc (@reg 'lr '+ 0))
        (imm32-abs (label-reference 'got-fixup1))

        (label-anchor 'putsstub)
        (*ldr 'al 'ip (@reg 'pc '+ (- 8 8)))
        (*ldr 'al 'pc (@reg 'ip '+ 0))
        (imm32-abs (label-reference 'got-putsloc))

        (label-anchor 'exitstub)
        (*ldr 'al 'ip (@reg 'pc '+ (- 8 8)))
        (*ldr 'al 'pc (@reg 'ip '+ 0))
        (imm32-abs (label-reference 'got-exitloc))
        ))

(define shared-data
  (list (label-anchor 'shared-data-top)))

(define got ;; global offset table
  (for/list [(entry `((got-top 0)
                      (got-fixup0 0)
                      (got-fixup1 0)
                      (got-putsloc ,(label-reference 'plt-trapunbound))
                      (got-exitloc ,(label-reference 'plt-trapunbound))))]
    (match-define (list labelname value) entry)
    (list (label-anchor labelname) (imm32-abs value))))

(define code
  (list (label-linker 'hello-world 4 (lambda (delta i) (*add 'al 0 'r0 'pc (- delta 8))))
        (*bl 'al (label-reference 'putsstub))
        (*mov 'al 0 'r0 99)
        (*bl 'al (label-reference 'exitstub))
        (label-anchor 'loopforever)
        (*b 'al (label-reference 'loopforever))
        (label-anchor 'hello-world)
        (let ((str #"Hello, world!\n\0"))
          (list str
                (make-bytes (- (round-up-to-nearest 4 (bytes-length str)) (bytes-length str)) 0)))))

(define all-blobs
  (list code plt shared-data got))

(define-values (linked0 relocs link-map) (link all-blobs start-addr))

(define linked (list->bytes linked0))

(define (lookup-label name)
  (cdr (assoc (label-anchor name) link-map)))

(write-executable "got.elf"
                  (elf-executable #:image linked
                                  #:machine 'arm7
                                  #:origin origin-addr
                                  #:start-offset start-offset
                                  #:shared-data-address (lookup-label 'shared-data-top)
                                  #:got-address (lookup-label 'got-top)
                                  #:interpreter #"/lib/ld-linux-armhf.so.3"
                                  #:shared-data-symbols
                                  (list)
                                  #:shared-function-symbols
                                  (list (dynamic-symbol #"puts" #"libc.so.6")
                                        (dynamic-symbol #"exit" #"libc.so.6"))))
