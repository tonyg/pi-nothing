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
(require "platform.rkt")

(provide disassemble-bytes!
	 disassemble-raw!)

(define (disassemble-raw! x len
			  #:arch [arch (current-cpu-architecture)]
			  #:base [base 0]
			  #:show-binary [show-binary #t])
  (case arch
    [(arm7) (disassemble-arm7 x len base)]
    [(i386) (disassemble-udcli "-32" x len base show-binary)]
    [(x86_64) (disassemble-udcli "-64" x len base show-binary)]
    [else (error 'disassemble-raw! "Unsupported architecture ~v" arch)]))

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

(define (disassemble-udcli mode x len base show-binary)
  (with-input-from-bytes (subbytes x 0 len)
    (lambda ()
      (system (format "./udcli -o ~x ~a~a" base mode (if show-binary "" " -nohex"))))))
