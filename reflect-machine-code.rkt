#lang racket/base

(require (only-in '#%foreign ffi-call))
(require ffi/unsafe)

(provide (struct-out executable-machine-code)
	 reflect-machine-code)

(struct executable-machine-code (bytes arg-spec result-spec callout)
	#:property prop:procedure (struct-field-index callout))
	
(define builtins (ffi-lib #f))
(define %scheme-malloc-code
  (get-ffi-obj "scheme_malloc_code" builtins (_fun (size : _long) -> (_bytes o size))))

(define (reflect-machine-code bs arg-spec result-spec)
  (define xbs (%scheme-malloc-code (bytes-length bs)))
  (bytes-copy! xbs 0 bs)
  (executable-machine-code xbs
			   arg-spec
			   result-spec
			   (ffi-call xbs arg-spec result-spec)))
