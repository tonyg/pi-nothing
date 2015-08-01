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

(require (only-in racket/port with-output-to-string))
(require (only-in racket/system system))

(require "machine.rkt")
(require "mach-i386.rkt")
(require "mach-x86_64.rkt")

(provide guess-architecture
	 architecture->machine-description
	 guess-machine-description
	 current-machine-description
	 current-cpu-architecture)

;; -> (or 'i386 'x86_64)
;; Racket knows the architecture we're running on, but isn't telling.
(define (guess-architecture)
  (define racket-file-info (with-output-to-string (lambda () (system "file -L `which racket`"))))
  (cond
   [(regexp-match #rx"x86_64" racket-file-info) 'x86_64]
   [(regexp-match #rx"x86-64" racket-file-info) 'x86_64]
   [(regexp-match #rx"i386" racket-file-info) 'i386]
   [(regexp-match #rx"80386" racket-file-info) 'i386]
   [else (log-warning
	  (format "Could not determine CPU architecture from 'file -L `which racket`' output: ~v"
		  racket-file-info))
	 'i386]))

(define (architecture->machine-description a)
  (case a
    [(i386) machine-i386]
    [(x86_64) machine-x86_64]
    [else (error 'architecture->machine-description "Unsupported architecture ~v" a)]))

(define (guess-machine-description)
  (architecture->machine-description (guess-architecture)))

(define current-machine-description (make-parameter (guess-machine-description)))

(define (current-cpu-architecture)
  (machine-description-architecture (current-machine-description)))
