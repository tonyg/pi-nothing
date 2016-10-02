#lang racket/base
;; Emitter object. Mutable.

(provide (struct-out emitter)
         make-emitter
         emit-raw-blob!
         emit-padding!
         emit-blob!)

(require bitsyntax)
(require (only-in "asm-common.rkt" round-up-to-nearest))

(struct emitter ([offset #:mutable]
                 [buffer #:mutable]) #:transparent)

(define (make-emitter [initial-offset 0])
  (emitter initial-offset (bit-string)))

(define (emit-raw-blob! e blob)
  (set-emitter-buffer! e (bit-string-append (emitter-buffer e) blob))
  (define o (emitter-offset e))
  (set-emitter-offset! e (+ o (bit-string-byte-count blob)))
  o)

(define (emit-padding! e target-offset #:pad-byte [pad-byte 0])
  (define padding (- target-offset (emitter-offset e)))
  (when (negative? padding)
    (error 'emit-padding!
           "Cannot emit negative padding; target-offset ~v is smaller than current offset ~v"
           target-offset
           (emitter-offset e)))
  (emit-raw-blob! e (make-bytes padding pad-byte)))

(define (emit-blob! e blob alignment)
  (emit-padding! e (round-up-to-nearest alignment (emitter-offset e)))
  (emit-raw-blob! e blob))
