#lang racket/base
;; Port of linear_intervals.erl by Tony Garnock-Jones

(require racket/match)
(require (only-in racket/list last))

(provide empty-interval
	 full-interval
	 half-interval
	 singleton-interval ;; the original supported strings too
	 range-interval
	 list->interval
	 interval->list
	 interval-min
	 interval-max
	 foldl-interval
	 interval-subset?
	 interval-member?
	 interval-empty?
	 interval-invert
	 interval-intersection
	 interval-union
	 interval-symmetric-difference
	 interval-subtract
	 interval-first-fit)

(struct interval (initial toggles) #:prefab)

(define (empty-interval)
  (interval #f '()))

(define (full-interval)
  (interval #t '()))

(define (half-interval n)
  (interval #f (list n)))

(define (singleton-interval n)
  (interval #f (list n (+ n 1))))

;; Half-open range
(define (range-interval lo hi)
  (interval #f (list lo hi)))

(define (list->interval ranges)
  (let loop ((acc (empty-interval))
	     (rest (reverse (sort (sort ranges < #:key cdr) < #:key car))))
    (write rest) (newline)
    (match rest
      ['() acc]
      [(cons (cons lo hi) rest) (loop (interval-union (range-interval lo hi) acc) rest)]
      [_ (error 'list->interval "Ill-formed range list: ~v" ranges)])))

(define (nonfinite proc i)
  (error proc "Can only handle finite intervals: ~v" i))

(define (interval->list i)
  (when (interval-initial i) (nonfinite 'interval->list i))
  (let loop ((acc '())
	     (remaining (interval-toggles i)))
    (match remaining
      ['() (reverse acc)]
      [(list* lo hi rest) (loop (cons (cons lo hi) acc) rest)]
      [(list _) (nonfinite 'interval->list i)])))

;; Returns lowest value in the interval
(define (interval-min i)
  (when (or (interval-initial i) (null? (interval-toggles i))) (nonfinite 'interval-min i))
  (car (interval-toggles i)))

;; Returns *lowest* value such that the value and any greater values are not in the interval
(define (interval-max i)
  (when (or ((if (interval-initial i) even? odd?) (length (interval-toggles i)))
	    (null? (interval-toggles i)))
    (nonfinite 'interval-max i))
  (last (interval-toggles i)))

(define (foldl-interval f seed i)
  (when (interval-initial i) (nonfinite 'foldl-interval i))
  (let loop ((seed seed)
	     (toggles (interval-toggles i)))
    (match toggles
      ['() seed]
      [(list* lo hi rest) (loop (do ((n lo (+ n 1))
				     (seed seed (f n seed)))
				    ((= n hi) seed))
				rest)]
      [(list _) (nonfinite 'foldl-interval i)])))

;; Is i1 a subset of i2?
(define (interval-subset? i1 i2)
  (equal? i1 (interval-intersection i1 i2)))

(define (interval-member? i x)
  (let loop ((in (interval-initial i))
	     (toggles (interval-toggles i)))
    (cond
     [(null? toggles) in]
     [(< x (car toggles)) in]
     [else (loop (not in) (cdr toggles))])))

(define (interval-empty? i)
  (and (not (interval-initial i))
       (null? (interval-toggles i))))

(define (interval-invert i)
  (interval (not (interval-initial i)) (interval-toggles i)))

(define (merge elementwise mergetail i1 i2)
  (define (continue in toggles-rev in1 toggles1 in2 toggles2)
    (cond
     [(null? toggles1) (finalise toggles-rev (mergetail 'left in1 toggles2))]
     [(null? toggles2) (finalise toggles-rev (mergetail 'right in2 toggles1))]
     [(= (car toggles1) (car toggles2))
      (update in toggles-rev (not in1) (cdr toggles1) (not in2) (cdr toggles2) (car toggles1))]
     [(< (car toggles1) (car toggles2))
      (update in toggles-rev (not in1) (cdr toggles1) in2 toggles2 (car toggles1))]
     [else
      (update in toggles-rev in1 toggles1 (not in2) (cdr toggles2) (car toggles2))]))

  (define (update in toggles-rev in1 toggles1 in2 toggles2 toggle)
    (define merged (elementwise in1 in2))
    (if (equal? in merged)
	(continue in toggles-rev in1 toggles1 in2 toggles2)
	(continue merged (cons toggle toggles-rev) in1 toggles1 in2 toggles2)))

  (define (finalise toggles-rev tail)
    (append (reverse toggles-rev) tail))

  (let ((initial (elementwise (interval-initial i1) (interval-initial i2))))
    (interval initial
	      (continue initial
			'()
			(interval-initial i1)
			(interval-toggles i1)
			(interval-initial i2)
			(interval-toggles i2)))))

(define (interval-intersection i1 i2)
  (merge (lambda (a b) (and a b))
	 (lambda (lr in tail) (if in tail '()))
	 i1 i2))

(define (interval-union i1 i2)
  (merge (lambda (a b) (or a b))
	 (lambda (lr in tail) (if in '() tail))
	 i1 i2))

(define (interval-symmetric-difference i1 i2)
  (merge (lambda (a b) (if a (not b) b))
	 (lambda (lr in tail) tail)
	 i1 i2))

(define (interval-subtract i1 i2)
  (merge (lambda (a b) (and a (not b)))
	 (lambda (lr in tail) (if (or (and (eq? lr 'left) in)
				      (and (eq? lr 'right) (not in)))
				  tail
				  '()))
	 i1 i2))

(define (interval-first-fit request i)
  (when (interval-initial i) (nonfinite 'interval-first-fit i))
  (let search ((toggles (interval-toggles i)))
    (match toggles
      ['() #f]
      [(list final) final]
      [(list* lo hi rest)
       (if (>= (- hi lo) request)
	   lo
	   (search rest))])))
