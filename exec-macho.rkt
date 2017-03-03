#lang racket/base
;; Mach-O x86_64 executables (OS X)
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

;; TODO: factor out commonality between main-arm.rkt and this.

(require racket/match)
(require racket/system)
(require racket/format)
(require racket/pretty)
(require (only-in racket/file file->list))
(require (only-in racket/list make-list append-map))

(require bitsyntax)

(require "driver.rkt")
(require "linker.rkt")
(require "dump-bytes.rkt")
(require "disasm.rkt")

(require "lir.rkt")
(require "machine.rkt")
(require "asm-x86_64.rkt")
(require "mach-x86_64.rkt")

;; It looks like (on my system, at least) program images are loaded
;; into core at 0x100000000. The first page begins with the Mach-O
;; header, so the actual program text starts toward the end of the
;; page. We follow these conventions, and generate our code to run
;; from the first page boundary following the origin: 0x100001000.

(define md machine-x86_64)
(define start-addr #x100001000)

;; /usr/include/mach-o/loader.h
;; https://developer.apple.com/library/mac/documentation/developertools/conceptual/MachORuntime/Reference/reference.html
;; https://developer.apple.com/library/mac/documentation/developertools/conceptual/MachORuntime/Reference/reference.html#//apple_ref/c/tag/mach_header_64

(define (mach-header-64 commands)
  (define sizeofcmds (foldr + 0 (map bit-string-byte-count commands)))
  (define flags (bitwise-ior #x1 ;; MH_NOUNDEFS
			     ;; #x400 ;; MH_NOFIXPREBINDING
			     ;; #x20000 ;; MH_ALLOW_STACK_EXECUTION
			     ))
  (apply bit-string-append
	 (bit-string (#xfeedfacf :: little-endian bits 32) ;; magic
		     (#x01000007 :: little-endian bits 32) ;; cputype: CPU_TYPE_X86_64
		     (3 :: little-endian bits 32) ;; cpusubtype: CPU_SUBTYPE_X86_64_ALL
		     (1 :: little-endian bits 32) ;; filetype: MH_OBJECT
		     ((length commands) :: little-endian bits 32) ;; ncmds
		     (sizeofcmds :: little-endian bits 32) ;; sizeofcmds
		     (flags :: little-endian bits 32)	   ;; flags
		     (0 :: little-endian bits 32)	   ;; reserved
		     )
	 commands))

(define (mach-load-command cmdtype payload)
  (unless (zero? (modulo (bit-string-byte-count payload) 8))
    (error 'mach-load-command "Mach-O load command payload must be a multiple of 8 bytes long"))
  (bit-string (cmdtype :: little-endian bits 32)
	      ((+ 8 (bit-string-byte-count payload)) :: little-endian bits 32)
	      ;; ^ **includes** size of the cmdtype and cmdsize fields, as well as the payload
	      (payload :: binary)))

(define (fixed-width-c-string s w)
  (string->bytes/latin-1 (substring (string-append s (make-string w #\nul)) 0 w)))

(define (mach-segment-command-64 segname sectname vmaddr vmsize fileoff filesize sectionsize)
  (define segname-bytes (fixed-width-c-string segname 16))
  (define sectname-bytes (fixed-width-c-string sectname 16))
  (mach-load-command
   #x19 ;; LC_SEGMENT_64
   (bit-string (segname-bytes :: binary) ;; 16 bytes long
	       (vmaddr :: little-endian bits 64)
	       (vmsize :: little-endian bits 64)
	       (fileoff :: little-endian bits 64)
	       (filesize :: little-endian bits 64)
	       (7 :: little-endian bits 32) ;; maxprot: R=1 | W=2 | X=4 --> 7
	       (7 :: little-endian bits 32) ;; initprot: same
	       (1 :: little-endian bits 32) ;; nsects
	       (0 :: little-endian bits 32) ;; flags

	       ;; Section-header and section follows segment-header
	       (sectname-bytes :: binary) ;; 16 bytes long
	       (segname-bytes :: binary)  ;; 16 bytes long
	       (vmaddr :: little-endian bits 64) ;; addr
	       (sectionsize :: little-endian bits 64) ;; size
	       (fileoff :: little-endian bits 32) ;; offset
	       (12 :: little-endian bits 32) ;; align (4096 = 2^12)
	       (0 :: little-endian bits 32) ;; reloff (no relocations)
	       (0 :: little-endian bits 32) ;; nreloc (no relocations)
	       (#x04000400 :: little-endian bits 32)
	       ;; ^ flags: S_REGULAR + S_ATTR_SELF_MODIFYING_CODE +
	       ;;          S_ATTR_SOME_INSTRUCTIONS
	       (0 :: little-endian bits 32) ;; reserved1
	       (0 :: little-endian bits 32) ;; reserved2
	       (0 :: little-endian bits 32) ;; reserved3
	       )))

(define (mach-thread-command entry-addr)
  (mach-load-command
   #x05 ;; LC_UNIXTHREAD
   (bit-string (4 :: little-endian bits 32) ;; flavor: x86_THREAD_STATE64
	       (42 :: little-endian bits 32) ;; count: 42 4-byte words of state
	       (0 :: little-endian bits 64) ;; rax
	       (0 :: little-endian bits 64) ;; rbx
	       (0 :: little-endian bits 64) ;; rcx
	       (0 :: little-endian bits 64) ;; rdx
	       (0 :: little-endian bits 64) ;; rdi
	       (0 :: little-endian bits 64) ;; rsi
	       (0 :: little-endian bits 64) ;; rbp
	       (0 :: little-endian bits 64) ;; rsp
	       (0 :: little-endian bits 64) ;; r8
	       (0 :: little-endian bits 64) ;; r9
	       (0 :: little-endian bits 64) ;; r10
	       (0 :: little-endian bits 64) ;; r11
	       (0 :: little-endian bits 64) ;; r12
	       (0 :: little-endian bits 64) ;; r13
	       (0 :: little-endian bits 64) ;; r14
	       (0 :: little-endian bits 64) ;; r15
	       (entry-addr :: little-endian bits 64) ;; rip
	       (0 :: little-endian bits 64) ;; rflags
	       (0 :: little-endian bits 64) ;; cs
	       (0 :: little-endian bits 64) ;; fs
	       (0 :: little-endian bits 64) ;; gs
	       )))

(define (format-macho-image image memsize)
  (define seg (mach-segment-command-64 "MutableTextSeg"
				       "MutableTextSec"
				       start-addr
				       memsize
				       #x1000
				       (bit-string-byte-count image)
				       (bit-string-byte-count image)))
  (define thr (mach-thread-command start-addr))
  (define hdr (mach-header-64 (list seg thr)))
  (define padding (make-bytes (- #x1000 (bit-string-byte-count hdr)) 0))
  (bit-string (hdr :: binary)
	      (padding :: binary)
	      (image :: binary)))

(define (write-image filename bs)
  (with-output-to-file filename #:exists 'replace
    (lambda ()
      (write-bytes (bit-string->bytes (format-macho-image bs (bytes-length bs))))))
  (system* "/usr/bin/env" "chmod" "+x" filename))

(define (startup-code)
  (list (*op 'and #xfffffffffffffff0 'rsp) ;; 16-byte stack alignment; also reqd for syscalls
	(*call (label-reference 'main))
	(*mov 'rax 'rdi)
	(*call (label-reference '%%exit))
	(label-anchor '%%ostype)
	(*mov 1 'rax)
	(*ret)
))

(define (make-syscall name body)
  (list (label-anchor name)
	(*push 'rbp)
	(*mov 'rsp 'rbp)
	(*push 'r10)
	(*mov 'rcx 'r10)
	(*op 'and #xfffffffffffffff0 'rsp)
	body
	(*pop 'r10)
	(*leave)
	(*ret)))

(define (syscalls)
  (list (make-syscall '%%write ;; RDI=fd, RSI=ptr, RDX=length
		      (list (*mov #x2000004 'rax) ;; SYS_write
			    (*syscall)))
	(make-syscall '%%exit ;; RDI=exit_status
		      (list (*mov #x2000001 'rax) ;; SYS_exit
			    (*syscall)))
	(make-syscall '%%mmap ;; RDI=addr, RSI=len, RDX=prot
		              ;; RCX=flags, R8=fd, R9=offset
		      (list (*mov #x20000c5 'rax) ;; SYS_mmap
			    (*syscall)))
	))

(define (compile-toplevel form global-env)
  (match form
    [`(define (,proc ,argname ...)
	,body ...)
     (write `(compiling ,proc ...)) (newline)
     (define-values (code data _debug-map) (compile-procedure md proc argname `(begin ,@body) global-env))
     (values (cons (label-anchor proc) code) data)]
    [`(struct ,_ ...)	(values '() '())]
    [`(const ,_ ...)	(values '() '())]
    [_
     (error 'compile-toplevel "Cannot compile toplevel form: ~v" form)]))

(define (link-blobs blobs)
  (define all-blobs (list* (startup-code)
			   (syscalls)
			   blobs))
  (pretty-print `(all-blobs ,all-blobs))
  (define-values (linked0 relocs link-map) (link all-blobs start-addr))
  (when (not (null? relocs))
    (error 'link-and-emit "Unresolved relocations: ~v" relocs))
  (define linked (list->bytes linked0))
  (dump-bytes! linked #:base start-addr) (flush-output)
  (for-each (match-lambda [(cons anchor addr)
			   (write `(,(label-anchor-name anchor) -> ,(number->string addr 16)))
			   (newline)])
	    link-map)
  (disassemble-bytes! linked
  		      #:arch (machine-description-architecture md)
  		      #:base start-addr
                      #:link-map link-map)
  linked)

(define (pad-to bs multiple)
  (define l (machine-code-length bs))
  (define leftover (modulo l multiple))
  (if (zero? leftover)
      bs
      (cons bs (make-list (- multiple leftover) #x90)))) ;; NOP

(define (field-def-size def)
  (match def
    [`(,name word64) 8]
    [`(,name word64 ,n) (* 8 n)]
    [`(,name word32) 4]
    [`(,name word32 ,n) (* 4 n)]
    [`(,name byte) 1]
    [`(,name byte ,n) (* 1 n)]))

(define (symbol-append . syms)
  (string->symbol (apply string-append (map symbol->string syms))))

(define (extract-constants forms)
  (append-map (match-lambda
	       [`(struct ,name (,field-defs ...))
		(define struct-size (foldl + 0 (map field-def-size field-defs)))
		(do ((field-defs field-defs (cdr field-defs))
		     (offset 0 (+ offset (field-def-size (car field-defs))))
		     (acc (list (list (symbol-append 'sizeof- name) (lit struct-size)))
			  (cons (list (symbol-append name '- (car (car field-defs))) (lit offset))
				acc)))
		    ((null? field-defs) (reverse acc)))]
	       [`(const ,name ,(? number? literal-value))
		(list (list name (lit literal-value)))]
	       [_
		'()])
	      forms))

(define (compile-file filename)
  (define all-forms (file->list filename))
  (define global-env (extract-constants all-forms))
  (let loop ((forms all-forms)
	     (blobs-rev '()))
    (match forms
      ['()
       (define blobs (reverse blobs-rev))
       (link-blobs blobs)]
      [(cons form rest)
       (define-values (code data) (compile-toplevel form global-env))
       (loop rest
	     (list* (pad-to data 16)
		    (pad-to code 16)
		    blobs-rev))])))

(define (compile-and-link filename-base)
  (let ((bs (compile-file (string-append filename-base".nothing"))))
    (write-image filename-base bs)))

(module+ main
  (require racket/cmdline)
  (file-stream-buffer-mode (current-output-port) 'none)
  (compile-and-link
   (command-line
    #:program "exec-macho.rkt"
    #:args (base-filename)
    base-filename)))
