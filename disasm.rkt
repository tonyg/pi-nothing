#lang racket/base
;; Copyright (C) 2012 Tony Garnock-Jones <tonygarnockjones@gmail.com>
;;
;; This file is part of pi-nothing.
;;
;; pi-nothing is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation, either version 3 of the License,
;; or (at your option) any later version.
;;
;; pi-nothing is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with pi-nothing. If not, see <http://www.gnu.org/licenses/>.

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
      (get-ffi-obj "disassemble_block" lib (_fun _gcpointer _int _uint _int _int -> _void))
      (lambda (bs len base arch show-binary)
	(display "beaengine not available")
	(newline))))

(define (disassemble-raw! x len
			  #:arch [arch (current-cpu-architecture)]
			  #:base [base 0]
			  #:show-binary [show-binary #t])
  (if (eq? arch 'arm7)
      (disassemble-arm7 x len base)
      (%disassemble-block x
			  len
			  base
			  (case arch
			    [(i386) 0]
			    [(x86_64) 1]
			    [else (error 'disassemble-block "Unsupported architecture ~v" arch)])
			  (if show-binary 1 0))))

(define (disassemble-bytes! bs
			    #:arch [arch (current-cpu-architecture)]
			    #:base [base 0]
			    #:show-binary [show-binary #t])
  (disassemble-raw! bs (bytes-length bs) #:arch arch #:base base #:show-binary show-binary))

(define (disassemble-arm7 x len base)
  (with-input-from-bytes (subbytes x 0 len)
    (lambda ()
      (system (string-append "./disarm/disarm-0.11 - "
			     (number->string base))))))
