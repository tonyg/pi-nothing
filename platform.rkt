#lang racket/base

(require (only-in racket/port with-output-to-string))
(require (only-in racket/system system))

(provide guess-architecture
	 current-cpu-architecture)

;; -> (or 'i386 'x86_64)
;; Racket knows the architecture we're running on, but isn't telling.
(define (guess-architecture)
  (define racket-file-info (with-output-to-string (lambda () (system "file -L `which racket`"))))
  (cond
   [(regexp-match #rx"x86_64" racket-file-info) 'x86_64]
   [(regexp-match #rx"i386" racket-file-info) 'i386]
   [(regexp-match #rx"80386" racket-file-info) 'i386]
   [else (log-warning
	  (format "Could not determine CPU architecture from 'file -L `which racket`' output: ~v"
		  racket-file-info))
	 'i386]))

(define current-cpu-architecture (make-parameter (guess-architecture)))
