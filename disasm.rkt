#lang racket/base

(require (only-in racket/port with-input-from-bytes))
(require (only-in racket/system system))
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
  (if (eq? arch 'arm7)
      (disassemble-arm7 x len)
      (%disassemble-block x
			  len
			  (case arch
			    [(i386) 0]
			    [(x86_64) 1]
			    [else (error 'disassemble-block "Unsupported architecture ~v" arch)])
			  (if show-binary 1 0))))

(define (disassemble-bytes! bs
			    #:arch [arch (current-cpu-architecture)]
			    #:show-binary [show-binary #t])
  (disassemble-raw! bs (bytes-length bs) #:arch arch #:show-binary show-binary))

(define (disassemble-arm7 x len)
  (with-input-from-bytes (subbytes x 0 len)
    (lambda ()
      (system "./disarm/disarm-0.11 - 0"))))
