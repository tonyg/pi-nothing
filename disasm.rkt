#lang racket/base
;; Copyright (C) 2012-2015 Tony Garnock-Jones <tonyg@leastfixedpoint.com>
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; We parse output from disarm and udcli in order to helpfully write
;; out correlations with any passed-in link-map.
;;
;; We expect disarm to produce lines that look like this:
;;
;; 400080 EB0000EC	BL	&00400438
;;
;; and we expect udcli to produce lines that look like this:
;;
;; 000000010000116d 350 373 376 377  call 0x10000106d
;;                  377
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require (only-in racket/port with-input-from-bytes with-output-to-string))
(require (only-in racket/system system))
(require (only-in racket/string string-split))
(require "platform.rkt")

(provide disassemble-bytes!
	 disassemble-raw!)

(define (disassemble-raw! x len
			  #:arch [arch (current-cpu-architecture)]
			  #:base [base 0]
			  #:show-binary [show-binary #t]
                          #:link-map [link-map '()])
  (case arch
    [(arm7) (disassemble-arm7 x len base link-map)]
    [(i386) (disassemble-udcli "-32" x len base show-binary link-map)]
    [(x86_64) (disassemble-udcli "-64" x len base show-binary link-map)]
    [else (error 'disassemble-raw! "Unsupported architecture ~v" arch)]))

(define (disassemble-bytes! bs
			    #:arch [arch (current-cpu-architecture)]
			    #:base [base 0]
			    #:show-binary [show-binary #t]
                            #:link-map [link-map '()])
  (disassemble-raw! bs
                    (bytes-length bs)
                    #:arch arch
                    #:base base
                    #:show-binary show-binary
                    #:link-map link-map))

(define (invert-map link-map)
  (for/hash [(entry link-map)]
    (values (cdr entry) (car entry))))

(define (disassemble-arm7 x len base link-map)
  (define addr-map (invert-map link-map))
  (define lines
    (string-split
     (with-output-to-string
       (lambda ()
         (with-input-from-bytes (subbytes x 0 len)
           (lambda ()
             (system (string-append "./disarm/disarm-0.11 - "
                                    (number->string base)))))))
     "\n"))
  (for [(line (in-list lines))]
    (define pieces (string-split line))
    (define maybe-anchor (and (pair? pieces)
                              (hash-ref addr-map (string->number (car pieces) 16) #f)))
    (when maybe-anchor (printf "\n~a:\n" maybe-anchor))
    (define maybe-ref (let ((m (regexp-match #px"&(........)" line)))
                        (and m
                             (hash-ref addr-map (string->number (cadr m) 16) #f))))
    (if maybe-ref
        (printf "~a ;; ~a\n" line maybe-ref)
        (printf "~a\n" line))))

(define (disassemble-udcli mode x len base show-binary link-map)
  (define addr-map (invert-map link-map))
  (define lines
    (string-split
     (with-output-to-string
       (lambda ()
         (with-input-from-bytes (subbytes x 0 len)
           (lambda ()
             (system (format "./udcli -o ~x ~a~a" base mode (if show-binary "" " -nohex")))))))
     "\n"))
  (for [(line (in-list lines))]
    (define addr (string->number (substring line 0 16) 16))
    (define maybe-anchor (and addr (hash-ref addr-map addr #f)))
    (when maybe-anchor (printf "\n~a:\n" maybe-anchor))
    (define maybe-ref (let ((m (regexp-match #px".*0x([0-9a-fA-F]+)" line)))
                        (and m
                             (hash-ref addr-map (string->number (cadr m) 16) #f))))
    (if maybe-ref
        (printf "~a ;; ~a\n" line maybe-ref)
        (printf "~a\n" line))))
