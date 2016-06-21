#lang racket/base
;; ELF executables
;; Copyright (C) 2013-2015 Tony Garnock-Jones <tonyg@leastfixedpoint.com>
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

;; Based on the teachings of http://www.muppetlabs.com/~breadbox/software/tiny/teensy.html
;; and /usr/include/linux/elf.h
;; and http://www.uclibc.org/docs/elf-64-gen.pdf

(provide elf32-executable
         elf64-executable
         write-executable)

(require racket/match)
(require racket/system)

(require bitsyntax)

(define (machine->machine-id machine)
  (match machine
    ['i386 3] ;; EM_386
    ['x86_64 62] ;; EM_X86_64
    ['arm7 40])) ;; EM_ARM

(define (elf32-executable #:image image
                          #:machine machine
                          #:origin origin-addr
                          #:start-offset start-offset
                          #:e_flags [e_flags 0]
                          #:memsize [memsize (bytes-length image)])
  (define start-addr (+ origin-addr start-offset))
  (define header
    (bit-string ;; Elf64_Ehdr
                #x7f
		(#"ELF" :: binary)

		1  ;; EI_CLASS - 32 bit (1 = 32 bit, 2 = 64 bit)
		1  ;; EI_DATA - ELFDATA2LSB = 1
		1  ;; EI_VERSION - EV_CURRENT = 1
		0  ;; EI_OSABI - ELFOSABI_SYSV (aka ELFOSABI_NONE) = 0
		0  ;; EI_ABIVERSION - should contain 0
		0 0 0 0 0 0 0 ;; EI_PAD

		(2 :: little-endian bits 16) ;; e_type - ET_EXEC = 2
		((machine->machine-id machine) :: little-endian bits 16)

		(1 :: little-endian bits 32) ;; e_version - EV_CURRENT = 1

		(start-addr :: little-endian bits 32) ;; e_entry
		(52 :: little-endian bits 32) ;; e_phoff - offset relative to start of file
		(0 :: little-endian bits 32)  ;; e_shoff

		(e_flags :: little-endian bits 32) ;; e_flags

		(52 :: little-endian bits 16) ;; e_ehsize
		(32 :: little-endian bits 16) ;; e_phentsize
		(1 :: little-endian bits 16)  ;; e_phnum
		(40 :: little-endian bits 16) ;; e_shentsize
		(0 :: little-endian bits 16)  ;; e_shnum
		(0 :: little-endian bits 16)  ;; e_shstrndx

		;; 52 bytes in

		;; Elf32_Phdr
		(1 :: little-endian bits 32) ;; p_type - PT_LOAD = 1
		(0 :: little-endian bits 32) ;; p_offset
		(origin-addr :: little-endian bits 32) ;; p_vaddr
		(origin-addr :: little-endian bits 32) ;; p_paddr
		((+ start-offset (bytes-length image)) :: little-endian bits 32) ;; p_filesz
		((+ start-offset memsize) :: little-endian bits 32) ;; p_memsz
		(7 :: little-endian bits 32) ;; p_flags - PT_R=4 | PT_W=2 | PT_X=1 --> 7
		(#x1000 :: little-endian bits 32)  ;; p_align
		))
  (define padding (make-bytes (- start-offset (bit-string-byte-count header)) 0))
  (bit-string->bytes (bit-string (header :: binary)
                                 (padding :: binary)
                                 (image :: binary))))

(define (elf64-executable #:image image
                          #:machine machine
                          #:origin origin-addr
                          #:start-offset start-offset
                          #:e_flags [e_flags 0]
                          #:memsize [memsize (bytes-length image)])
  (define start-addr (+ origin-addr start-offset))
  (define header
    (bit-string ;; Elf64_Ehdr
                #x7f
		(#"ELF" :: binary)

		2  ;; EI_CLASS - 64 bit (1 = 32 bit, 2 = 64 bit)
		1  ;; EI_DATA - ELFDATA2LSB = 1
		1  ;; EI_VERSION - EV_CURRENT = 1
		0  ;; EI_OSABI - ELFOSABI_SYSV (aka ELFOSABI_NONE) = 0
		0  ;; EI_ABIVERSION - should contain 0
		0 0 0 0 0 0 0 ;; EI_PAD

		(2 :: little-endian bits 16) ;; e_type - ET_EXEC = 2
		((machine->machine-id machine) :: little-endian bits 16)

		(1 :: little-endian bits 32) ;; e_version - EV_CURRENT = 1

		(start-addr :: little-endian bits 64) ;; e_entry
		(64 :: little-endian bits 64) ;; e_phoff - offset relative to start of file
		(0 :: little-endian bits 64)  ;; e_shoff

		(e_flags :: little-endian bits 32) ;; e_flags

		(64 :: little-endian bits 16) ;; e_ehsize
		(56 :: little-endian bits 16) ;; e_phentsize
		(1 :: little-endian bits 16)  ;; e_phnum
		(64 :: little-endian bits 16) ;; e_shentsize
		(0 :: little-endian bits 16)  ;; e_shnum
		(0 :: little-endian bits 16)  ;; e_shstrndx

		;; 64 bytes in

		;; Elf64_Phdr
		(1 :: little-endian bits 32) ;; p_type - PT_LOAD = 1
		(7 :: little-endian bits 32) ;; p_flags - PT_R=4 | PT_W=2 | PT_X=1 --> 7
		(0 :: little-endian bits 64) ;; p_offset
		(origin-addr :: little-endian bits 64) ;; p_vaddr
		(origin-addr :: little-endian bits 64) ;; p_paddr
		((+ start-offset (bytes-length image)) :: little-endian bits 64) ;; p_filesz
		((+ start-offset memsize) :: little-endian bits 64) ;; p_memsz
		(#x1000 :: little-endian bits 64)  ;; p_align
		))
  (define padding (make-bytes (- start-offset (bit-string-byte-count header)) 0))
  (bit-string->bytes (bit-string (header :: binary)
                                 (padding :: binary)
                                 (image :: binary))))

(define (write-executable filename bs)
  (with-output-to-file filename #:exists 'replace
    (lambda () (write-bytes bs)))
  (system* "/usr/bin/env" "chmod" "+x" filename))
