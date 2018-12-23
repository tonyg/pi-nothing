#lang setup/infotab
(define collection "nothingc")
(define deps '("base"
               "make"))

(define pre-install-collection "private/install.rkt")
(define compile-omit-files '("private/install.rkt"
                             "private/alternatives/intervals-bitset.rkt"
                             "private/alternatives/intervals-datastructure.rkt"
                             ))

(define racket-launcher-names '("pi-nothing-arm-baremetal" "pi-nothing-elf" "pi-nothing-macho"))
(define racket-launcher-libraries '("exec-arm-baremetal.rkt" "exec-elf.rkt" "exec-macho.rkt"))
