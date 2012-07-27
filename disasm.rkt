#lang racket/base

(require ffi/unsafe)

(provide disassemble-bytes!
	 disassemble-raw!)

(define lib (ffi-lib "./beaengine-wrapper.so"))

(define %disassemble-block
  (get-ffi-obj "disassemble_block" lib (_fun _pointer _int _int _int -> _void)))

(define (disassemble-raw! x len #:arch [arch 'i386] #:show-binary [show-binary #t])
  (%disassemble-block x
		      len
		      (case arch
			[(i386) 0]
			[(x86_64) 1]
			[else (error 'disassemble-block "Unsupported architecture ~v" arch)])
		      (if show-binary 1 0)))

(define (disassemble-bytes! bs #:arch [arch 'i386] #:show-binary [show-binary #t])
  (disassemble-raw! bs (bytes-length bs) #:arch arch #:show-binary show-binary))
