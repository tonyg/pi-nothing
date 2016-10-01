#lang racket/base

(provide elf-hash)

(define (elf-hash symbol-bytes)
  (for/fold [(h 0)] [(b (in-bytes symbol-bytes))]
    (let* ((h (bitwise-and #xffffffff (+ (arithmetic-shift h 4) b)))
           (g (bitwise-and #xf0000000 h)))
      (bitwise-and #xffffffff
                   (if (zero? g)
                       h
                       (bitwise-xor h (bitwise-and #xff (arithmetic-shift g -24))))
                   (bitwise-not g)))))

(module+ main
  (require racket/match)
  (let loop ((count 0))
    (match (read)
      [(? eof-object?)
       (printf "elf-hash passed ~v test cases\n" count)]
      [(list identifier-bytes expected-hash-value)
       (define actual-hash-value (elf-hash identifier-bytes))
       (when (not (= expected-hash-value actual-hash-value))
         (error 'elf-hash "Incorrect result: expected ~v, got ~v for ~v"
                expected-hash-value
                actual-hash-value
                identifier-bytes))
       (loop (+ count 1))])))
