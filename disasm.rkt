#lang racket/base

(require ffi/unsafe)
(require "platform.rkt")

(provide disassemble-bytes!
	 disassemble-raw!)

(define lib (with-handlers ((exn:fail? (lambda (e) #f)))
	      (ffi-lib "./beaengine-wrapper.so")))

(define %disassemble-block
  (if lib
      (get-ffi-obj "disassemble_block" lib (_fun _gcpointer _int _int _int -> _void))
      (lambda (bs len arch show-binary)
	(display "beaengine not available")
	(newline))))

(define (disassemble-raw! x len
			  #:arch [arch (current-cpu-architecture)]
			  #:show-binary [show-binary #t])
  (%disassemble-block x
		      len
		      (case arch
			[(i386) 0]
			[(x86_64) 1]
			[else (error 'disassemble-block "Unsupported architecture ~v" arch)])
		      (if show-binary 1 0)))

(define (disassemble-bytes! bs
			    #:arch [arch (current-cpu-architecture)]
			    #:show-binary [show-binary #t])
  (disassemble-raw! bs (bytes-length bs) #:arch arch #:show-binary show-binary))
