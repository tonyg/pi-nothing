#lang racket/base
;; Pretty hex dump output of a Bytes.

(provide dump-bytes!)

;; Exact Exact -> String
;; Returns the "0"-padded, width-digit hex representation of n
(define (hex width n)
  (define s (number->string n 16))
  (define slen (string-length s))
  (cond
   ((< slen width) (string-append (make-string (- width slen) #\0) s))
   ((= slen width) s)
   ((> slen width) (substring s 0 width))))

;; Bytes Exact -> Void
;; Prints a pretty hex/ASCII dump of bs on (current-output-port).
(define (dump-bytes! bs [requested-count (bytes-length bs)] #:base [baseaddr 0])
  (define count (min requested-count (bytes-length bs)))
  (define clipped (subbytes bs 0 count))
  (define (dump-hex i)
    (if (< i count)
	(display (hex 2 (bytes-ref clipped i)))
	(display "  "))
    (display #\space))
  (define (dump-char i)
    (if (< i count)
	(let ((ch (bytes-ref clipped i)))
	  (if (<= 32 ch 127)
	      (display (integer->char ch))
	      (display #\.)))
	(display #\space)))
  (define (for-each-between f low high)
    (do ((i low (+ i 1)))
	((= i high))
      (f i)))
  (define (dump-line i)
    (display (hex 8 (+ i baseaddr)))
    (display #\space)
    (for-each-between dump-hex i (+ i 8))
    (display ": ")
    (for-each-between dump-hex (+ i 8) (+ i 16))
    (display #\space)
    (for-each-between dump-char i (+ i 8))
    (display " : ")
    (for-each-between dump-char (+ i 8) (+ i 16))
    (newline))
  (do ((i 0 (+ i 16)))
      ((>= i count))
    (dump-line i)))
