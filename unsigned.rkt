#lang racket/base
;; Unsigned arithmetic utilities.

(provide <=u32
	 <u32
	 >=u32
	 >u32)

(define two32 (expt 2 32))

(define ((lift32 f) a b)
  (f (modulo a two32) (modulo b two32)))

(define <=u32 (lift32 <=))
(define <u32 (lift32 <))
(define >=u32 (lift32 >=))
(define >u32 (lift32 >))
