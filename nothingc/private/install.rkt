#lang racket/base

(provide pre-installer)

(require racket/system)

(define (pre-installer collections-top-path nothingc-path)
  (parameterize ((current-directory (build-path nothingc-path "private")))
    (system "make")))
