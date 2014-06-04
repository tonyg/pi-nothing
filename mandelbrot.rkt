#lang racket/base

(require racket/flonum)

(define (putrgb buf stride x y r g b)
  (define i (* 3 (+ x (* y stride))))
  (bytes-set! buf i r)
  (bytes-set! buf (+ i 1) g)
  (bytes-set! buf (+ i 2) b))

(define (escape-iteration-count cx cy)
  (define iteration-limit 256)
  (let loop ((i 0) (zx 0.0) (zy 0.0))
    (if (>= i iteration-limit)
	-1
	(let ((zx2 (fl* zx zx))
	      (zy2 (fl* zy zy)))
	  (if (fl>= (fl+ zx2 zy2) 4.0)
	      i
	      (loop (+ i 1)
		    (fl+ cx (fl- zx2 zy2))
		    (fl+ cy (fl* 2.0 (fl* zx zy)))))))))

(define (main)
  (define width 1024)
  (define height 1024)
  (printf "P6 ~a ~a 255\n" width height)
  (define buf (make-bytes (* width height 3)))
  (let yloop ((y 0))
    (when (< y height)
      (let xloop ((x 0))
	(when (< x height)
	  (define i (escape-iteration-count
		     (fl+ (->fl -2) (fl* (->fl x) (fl/ 4.0 (->fl width))))
		     (fl+ (->fl -2) (fl* (->fl y) (fl/ 4.0 (->fl height))))))
	  (define b (if (= i -1) 0 i))
	  (putrgb buf width x y b b b)
	  (xloop (+ x 1))))
      (yloop (+ y 1))))
  (write-bytes buf))

(module+ main
  (main))
