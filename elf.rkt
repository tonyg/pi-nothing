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

;; From https://blogs.oracle.com/ali/entry/inside_elf_symbol_tables, we learn that:
;; "The symbols in a symbol table are written in the following order:
;;  - Index 0 in any symbol table is used to represent undefined
;;    symbols. As such, the first entry in a symbol table (index 0) is
;;    always completely zeroed (type STT_NOTYPE), and is not used.
;;  - If the file contains any local symbols, the second entry (index
;;    1) the symbol table will be a STT_FILE symbol giving the name of
;;    the file.
;;  - Section symbols.
;;  - Register symbols.
;;  - Global symbols that have been reduced to local scope via a
;;    mapfile.
;;  - For each input file that supplies local symbols, a STT_FILE
;;    symbol giving the name of the input file is put in the symbol
;;    table, followed by the symbols in question.
;;  - The global symbols immediately follow the local symbols in the
;;    symbol table. Local and global symbols are always kept separate
;;    in this manner, and cannot be mixed together."

(provide (struct-out dynamic-symbol)
         elf32-executable
         elf64-executable
         write-executable)

(require racket/match)
(require racket/system)
(require (only-in racket/list filter-map))

(require bitsyntax)

(require (only-in "asm-common.rkt" round-up-to-nearest))
(require "elf-hash.rkt")
(require "emit.rkt")

;; An ELF file, from the perspective of the *loader* (not the linker)
;; can be thought of as a collection of segments laid out within a
;; blob of memory. The segments contain code and data, but also
;; instructions for the loader to interpret.

;; We will need to include one or more program content segments, plus
;; a collection of symbol references to be relocated at load-time and
;; zero or more initialization and termination function addresses.

;; These will be translated into
;;  - the content segments
;;  - a symbol table
;;  - a string table
;;  - a PT_DYNAMIC segment containing
;;     - DT_NEEDED for all referenced shared libraries
;;     - DT_HASH, DT_SYMTAB and DT_SYMENT for the symbol table
;;     - DT_STRTAB and DT_STRSZ for the string table
;;     - DT_RELA, DT_RELASZ, DT_RELAENT (or the DT_REL versions?) for relocations
;;     - DT_INIT and DT_FINI, as many as required
;;     - DT_TEXTREL might be required??
;;     - DT_NULL marking the end of the section

;;---------------------------------------------------------------------------

(struct elf-segment (type ;; SegmentType
                     flags ;; Listof SegmentFlag
                     offset ;; Option Word -- if absent, computed
                     vaddr ;; Option Word -- if absent, computed
                     paddr ;; Option Word -- if absent, vaddr
                     filesize ;; Word
                     memsize ;; Option Word -- if absent, filesize
                     align ;; Word
                     )
  #:transparent)

;; (dynamic-symbol Bytes Bytes)
(struct dynamic-symbol (name library-name) #:transparent)

;; (elf-symbol Bytes (Option Bytes) SymbolType SymbolScope SymbolSection Word Word)
;; where Word is written as 32 or 64 bits, depending on the output file type
(struct elf-symbol (name needed type scope section value size) #:transparent)

;; (elf-relocation Nat RelocationType Nat (Option SignedWord))
;; where SignedWord is written as 32 or 64 bits, depending on the output file type
(struct elf-relocation (offset type symbol-index addend) #:transparent)

;; (elf-dyn DynTag Word)
;; where Word is written as 32 or 64 bits, depending on the output file type
(struct elf-dyn (tag value) #:transparent)

;;---------------------------------------------------------------------------

(define (symbol-scope->number scope)
  (match scope
    ['local 0]
    ['global 1]
    ['weak 2]
    [(? number? n) n]))

(define (symbol-type->number type)
  (match type
    ['notype 0]
    ['object 1]
    ['func 2]
    ['section 3]
    ['file 4]
    [(? number? n) n]))

(define (section->number section)
  (match section
    ['undef 0]
    ['abs #xfff1]
    ['common #xfff2]
    [(? number? n) n]))

(define (relocation-type->number type)
  (match type
    ['x86_64-none 0]
    ['x86_64-64 1]
    ['x86_64-pc32 2]
    ['x86_64-got32 3]
    ['x86_64-plt32 4]
    ['x86_64-copy 5]
    ['x86_64-glob_dat 6]
    ['x86_64-jump_slot 7]
    ['x86_64-relative 8]
    ['x86_64-gotpcrel 9]
    ['x86_64-32 10]
    ['x86_64-32s 11]
    ['x86_64-16 12]
    ['x86_64-pc16 13]
    ['x86_64-8 14]
    ['x86_64-pc8 15]
    ['x86_64-dtpmod64 16]
    ['x86_64-dtpoff64 17]
    ['x86_64-tpoff64 18]
    ['x86_64-tlsgd 19]
    ['x86_64-tlsld 20]
    ['x86_64-dtpoff32 21]
    ['x86_64-gottpoff 22]
    ['x86_64-tpoff32 23]
    ['x86_64-pc64 24]
    ['x86_64-gotoff64 25]
    ['x86_64-gotpc32 26]
    ['x86_64-got64 27]
    ['x86_64-gotpcrel64 28]
    ['x86_64-gotpc64 29]
    ['x86_64-gotplt64 30]
    ['x86_64-pltoff64 31]
    ['x86_64-size32 32]
    ['x86_64-size64 33]
    ['x86_64-gotpc32_tlsdesc 34]
    ['x86_64-tlsdesc_call 35]
    ['x86_64-tlsdesc 36]
    ['x86_64-irelative 37]
    ['x86_64-relative64 38]
    ['x86_64-gotpcrelx 41]
    ['x86_64-rex_gotpcrelx 42]
    ['x86_64-num 43]
    [(? number? n) n]))

(define (dyn-tag->number tag)
  (match tag
    ['null 0]
    ['needed 1]
    ['pltrelsz 2]
    ['pltgot 3]
    ['hash 4]
    ['strtab 5]
    ['symtab 6]
    ['rela 7]
    ['relasz 8]
    ['relaent 9]
    ['strsz 10]
    ['syment 11]
    ['init 12]
    ['fini 13]
    ['soname 14]
    ['rpath 15]
    ['symbolic 16]
    ['rel 17]
    ['relsz 18]
    ['relent 19]
    ['pltrel 20]
    ['debug 21]
    ['textrel 22]
    ['jmprel 23]
    ['bind-now 24]
    [(? number? n) n]))

(define (machine->machine-id machine)
  (match machine
    ['i386 3] ;; EM_386
    ['x86_64 62] ;; EM_X86_64
    ['arm7 40])) ;; EM_ARM

(define (segment-type->id segtype)
  (match segtype
    ['null 0]
    ['load 1]
    ['dynamic 2]
    ['interp 3]
    ['note 4]
    ['shlib 5]
    ['phdr 6]
    [(? integer? n) n]))

(define (segment-flags->number flags)
  (for/fold [(v 0)] [(flag (in-list flags))]
    (bitwise-ior v (match flag ['x 1] ['w 2] ['r 4]))))

;; (Listof Bytes) #:elf64? Boolean -> Bytes
;; Expects symbols to be in the order they will appear in the symbol table.
(define (sysv-symbol-hash-table symbols #:elf64? elf64?)
  ;; How to choose a good number of hash buckets? Metasm (the Ruby
  ;; assembly manipulation toolkit) goes with number of symbols,
  ;; divided by four, plus one. Let's do that too.
  (define start-symbol-index 1) ;; the 0th symbol is always STN_UNDEF
  (define nchain (+ start-symbol-index (length symbols)))
  (define nbuckets (+ 1 (quotient nchain 4)))
  (define buckets (make-vector nbuckets 0))
  (define chain (make-vector nchain 0))
  (for [(symbol (in-list symbols))
        (symbol-number (in-naturals start-symbol-index))]
    (define h (elf-hash symbol))
    (define index (remainder h nbuckets))
    (when (positive? (vector-ref buckets index))
      (vector-set! chain symbol-number (vector-ref buckets index)))
    (vector-set! buckets index symbol-number))
  (define word->bytes
    (compose bit-string->bytes
             (if elf64?
                 (lambda (w) (bit-string (w :: little-endian bits 64)))
                 (lambda (w) (bit-string (w :: little-endian bits 32))))))
  (apply bytes-append
         (word->bytes nbuckets)
         (word->bytes nchain)
         (append (map word->bytes (vector->list buckets))
                 (map word->bytes (vector->list chain)))))

;; (Listof Bytes) -> (Values Bytes (Hash Bytes Nat))
;; Builds a string table, yielding the table and an index into it.
(define (build-string-table bytestrings)
  ;; ELF says to put in a leading NUL byte so that a real string-table
  ;; index is never zero and, conversely, that an index of 0 gives an
  ;; empty string.
  (define-values (pieces index)
    (for/fold [(pieces (bit-string)) (index (hash))]
              [(bytestring (in-list (cons #"" bytestrings)))]
      (if (hash-has-key? index bytestring)
          (values pieces index)
          (values (bit-string-append pieces bytestring #"\0")
                  (hash-set index bytestring (quotient (bit-string-length pieces) 8))))))
  (values (bit-string->bytes pieces) index))

;; (Listof ElfSymbol) (Hash Bytes Nat) #:elf64? Boolean -> Bytes
(define (build-symbol-table symbols strtab-index #:elf64? elf64?)
  (bit-string->bytes
   (apply bit-string-append
          (for/list [(symbol (in-list (cons (elf-symbol #"" #f 0 0 0 0 0) symbols)))]
            (elf-symbol->bit-string symbol strtab-index elf64?)))))

(define (elf-symbol->bit-string symbol strtab-index elf64?)
  (match-define (elf-symbol name _needed type scope section value size) symbol)
  (if elf64?
      (bit-string ((hash-ref strtab-index name) :: little-endian bits 32)
                  ((symbol-scope->number scope) :: little-endian bits 4)
                  ((symbol-type->number type) :: little-endian bits 4)
                  (0 :: little-endian bits 8) ;; st_other, reserved
                  ((section->number section) :: little-endian bits 16)
                  (value :: little-endian bits 64)
                  (size :: little-endian bits 64))
      (bit-string ((hash-ref strtab-index name) :: little-endian bits 32)
                  (value :: little-endian bits 32)
                  (size :: little-endian bits 32)
                  ((symbol-scope->number scope) :: little-endian bits 4)
                  ((symbol-type->number type) :: little-endian bits 4)
                  (0 :: little-endian bits 8) ;; st_other, reserved
                  ((section->number section) :: little-endian bits 16))))

;; (Listof ElfReloc) (Hash Bytes Nat) #:elf64? Boolean #:include-addend? Boolean
(define (build-relocation-table relocs
                                #:elf64? elf64?
                                #:include-addend? include-addend?)
  (bit-string->bytes
   (apply bit-string-append
          (for/list [(reloc (in-list relocs))]
            (elf-relocation->bit-string reloc elf64? include-addend?)))))

(define (elf-relocation->bit-string reloc elf64? include-addend?)
  (match-define (elf-relocation offset type symbol-index addend) reloc)
  (when (or (and include-addend? (not addend))
            (and addend (not include-addend?)))
    (error 'elf-relocation->bit-string
           "Relocation addend is ~a but ~a: ~v"
           (if include-addend? "required" "forbidden")
           (if addend "present" "missing")
           reloc))
  (define rel
    (if elf64?
        (bit-string (offset :: little-endian bits 64)
                    ((relocation-type->number type) :: little-endian bits 32)
                    (symbol-index :: little-endian bits 32))
        (bit-string (offset :: little-endian bits 32)
                    ((relocation-type->number type) :: little-endian bits 8)
                    (symbol-index :: little-endian bits 24))))
  (define a
    (cond [(not addend) (bit-string)]
          [elf64?       (bit-string (addend :: little-endian bits 64))]
          [else         (bit-string (addend :: little-endian bits 32))]))
  (bit-string-append rel a))

;; (Listof ElfDyn) #:elf64? Boolean -> Bytes
;; Automatically puts the DT_NULL entry at the end.
(define (build-dynamic-segment dyns #:elf64? elf64?)
  (bit-string->bytes
   (bit-string-append (apply bit-string-append
                             (for/list [(dyn (in-list dyns))]
                               (elf-dyn->bit-string dyn elf64?)))
                      (elf-dyn->bit-string (elf-dyn 'null 0) elf64?))))

(define (elf-dyn->bit-string dyn elf64?)
  (match-define (elf-dyn tag value) dyn)
  (if elf64?
      (bit-string ((dyn-tag->number tag) :: little-endian bits 64)
                  (value :: little-endian bits 64))
      (bit-string ((dyn-tag->number tag) :: little-endian bits 32)
                  (value :: little-endian bits 32))))

(define (elf-segment->program-header seg #:elf64? elf64?)
  (match-define (elf-segment type flags offset vaddr paddr filesize memsize align) seg)
  (if elf64?
      (bit-string ((segment-type->id type) :: little-endian bits 32)
                  ((segment-flags->number flags) :: little-endian bits 32)
                  (offset :: little-endian bits 64)
                  (vaddr :: little-endian bits 64)
                  ((or paddr vaddr) :: little-endian bits 64)
                  (filesize :: little-endian bits 64)
                  ((or memsize filesize) :: little-endian bits 64)
                  (align :: little-endian bits 64))
      (bit-string ((segment-type->id type) :: little-endian bits 32)
                  (offset :: little-endian bits 32)
                  (vaddr :: little-endian bits 32)
                  ((or paddr vaddr) :: little-endian bits 32)
                  (filesize :: little-endian bits 32)
                  ((or memsize filesize) :: little-endian bits 32)
                  ((segment-flags->number flags) :: little-endian bits 32)
                  (align :: little-endian bits 32))))

(define (elf32-executable #:image image
                          #:machine machine
                          #:origin origin-addr
                          #:start-offset start-offset
                          #:e_flags [e_flags 0]
                          #:memsize [memsize (bytes-length image)])
  (define start-addr (+ origin-addr start-offset))
  (define header
    (bit-string-append (elf-header #:elf64? #f
                                   #:machine machine
                                   #:entry start-addr
                                   #:e_flags e_flags
                                   #:segment-count 1)
                       (elf-segment->program-header
                        (elf-segment 'load
                                     '(r w x)
                                     start-offset
                                     start-addr
                                     #f
                                     (bytes-length image)
                                     memsize
                                     #x1000)
                        #:elf64? #f)))
  (define padding-size (- start-offset (bit-string-byte-count header)))
  (when (negative? padding-size)
    (error 'elf32-executable "Start offset ~v too small for header size ~v"
           start-offset
           (bit-string-byte-count header)))
  (define padding (make-bytes padding-size 0))
  (bit-string->bytes (bit-string (header :: binary)
                                 (padding :: binary)
                                 (image :: binary))))

(define (lookup-symbol-index symbols name library-name symbol-type)
  (for/or [(s symbols) (i (in-naturals))]
    (and (equal? (elf-symbol-name s) name)
         (equal? (elf-symbol-needed s) library-name)
         (equal? (elf-symbol-type s) symbol-type)
         (+ i 1)))) ;; The 0th symbol is the empty symbol

(define (dynamic-symbol->elf-relocation d
                                        table-base
                                        slot-index
                                        symbols
                                        symbol-type
                                        relocation-type
                                        elf64?)
  (match-define (dynamic-symbol name library-name) d)
  (define addr (+ table-base (* (if elf64? 8 4) slot-index)))
  (define index (lookup-symbol-index symbols name library-name symbol-type))
  (elf-relocation addr relocation-type index 0))

(define (elf-header #:elf64? elf64?
                    #:machine machine
                    #:entry entry
                    #:e_flags e_flags
                    #:segment-count segment-count)
  (if elf64?
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

                  (entry :: little-endian bits 64) ;; e_entry
                  (64 :: little-endian bits 64) ;; e_phoff
                  (0 :: little-endian bits 64)  ;; e_shoff

                  (e_flags :: little-endian bits 32) ;; e_flags

                  (64 :: little-endian bits 16) ;; e_ehsize
                  ((elf-phentsize #:elf64? elf64?) :: little-endian bits 16) ;; e_phentsize
                  (segment-count :: little-endian bits 16)  ;; e_phnum
                  ((elf-shentsize #:elf64? elf64?) :: little-endian bits 16) ;; e_shentsize
                  (0 :: little-endian bits 16)  ;; e_shnum
                  (0 :: little-endian bits 16)  ;; e_shstrndx

                  ;; 64 bytes in
                  )
      (bit-string ;; Elf32_Ehdr
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

                  (entry :: little-endian bits 32) ;; e_entry
                  (52 :: little-endian bits 32) ;; e_phoff - offset relative to start of file
                  (0 :: little-endian bits 32)  ;; e_shoff

                  (e_flags :: little-endian bits 32) ;; e_flags

                  (52 :: little-endian bits 16) ;; e_ehsize
                  ((elf-phentsize #:elf64? elf64?) :: little-endian bits 16) ;; e_phentsize
                  (segment-count :: little-endian bits 16)  ;; e_phnum
                  ((elf-shentsize #:elf64? elf64?) :: little-endian bits 16) ;; e_shentsize
                  (0 :: little-endian bits 16)  ;; e_shnum
                  (0 :: little-endian bits 16)  ;; e_shstrndx

                  ;; 52 bytes in
                  )))

(define (elf-phentsize #:elf64? elf64?) (if elf64? 56 32))
(define (elf-shentsize #:elf64? elf64?) (if elf64? 64 40))

(define (elf64-executable #:image image
                          #:machine machine
                          #:origin origin-addr
                          #:start-offset start-offset
                          #:e_flags [e_flags 0]
                          #:memsize [memsize (bytes-length image)]
                          #:shared-data-address [shared-data-address #f]
                          #:got-address [got-address #f]
                          #:shared-data-symbols [shared-data-symbols '()]
                          #:shared-function-symbols [shared-function-symbols '()]
                          #:interpreter [interpreter #f])
  (define phdr-end #x200) ;; offset to first real segment

  (when (or shared-data-address
            got-address
            (pair? shared-data-symbols)
            (pair? shared-function-symbols))
    ;; TODO: Could this be split into checks for just the data and just the functions?
    (when (not (and shared-data-address got-address interpreter))
      (error 'elf64-executable
             "All of shared-data-address, got-address and interpreter are required.")))

  (define symbols
    (append (for/list [(d shared-data-symbols)]
              (match-define (dynamic-symbol name library-name) d)
              (elf-symbol name library-name 'object 'global 0 0 0))
            (for/list [(d shared-function-symbols)]
              (match-define (dynamic-symbol name library-name) d)
              (elf-symbol name library-name 'func 'global 0 0 0))))

  (define data-relocations
    (for/list [(d shared-data-symbols)
               (i (in-naturals))]
      (dynamic-symbol->elf-relocation d shared-data-address i symbols 'object 'x86_64-glob_dat #t)))

  (define function-relocations
    (for/list [(d shared-function-symbols)
               (i (in-naturals 3))] ;; skip 0 and the two special entries
      (dynamic-symbol->elf-relocation d got-address i symbols 'func 'x86_64-jump_slot #t)))

  (define-values (strtab strtab-index)
    (build-string-table
     (append (filter-map elf-symbol-needed symbols)
             (map elf-symbol-name symbols))))

  (define body (make-emitter phdr-end))

  (define interp-offset (and interpreter (emit-blob! body (bytes-append interpreter (bytes 0)) 1)))
  (define strtab-offset (emit-blob! body strtab 16))
  (define symtab (build-symbol-table symbols strtab-index #:elf64? #t))
  (define symtab-offset (emit-blob! body symtab 16))
  (define symhash-offset (emit-blob! body
                                     (sysv-symbol-hash-table (map elf-symbol-name symbols)
                                                             #:elf64? #t)
                                     16))
  (define rela (build-relocation-table data-relocations
                                       #:elf64? #t
                                       #:include-addend? #t))
  (define rela-offset (emit-blob! body rela 16))
  (define jmprel (build-relocation-table function-relocations
                                         #:elf64? #t
                                         #:include-addend? #t))
  (define jmprel-offset (emit-blob! body jmprel 16))
  (define dynseg-offset
    (emit-blob! body
                (build-dynamic-segment
                 (append
                  (for/list [(sym symbols) #:when (elf-symbol-needed sym)]
                    (elf-dyn 'needed (hash-ref strtab-index (elf-symbol-needed sym))))
                  (list (elf-dyn 'strtab (+ origin-addr strtab-offset))
                        (elf-dyn 'strsz (bytes-length strtab))
                        (elf-dyn 'symtab (+ origin-addr symtab-offset))
                        (elf-dyn 'syment (/ (bytes-length symtab) (+ 1 (length symbols))))
                        (elf-dyn 'hash (+ origin-addr symhash-offset))
                        (elf-dyn 'rela (+ origin-addr rela-offset))
                        (elf-dyn 'relasz (bytes-length rela))
                        (elf-dyn 'relaent (if (null? data-relocations)
                                              24 ;; TODO: compute
                                              (/ (bytes-length rela) (length data-relocations)))))
                  (if shared-data-address
                      (list (elf-dyn 'jmprel (+ origin-addr jmprel-offset))
                            (elf-dyn 'pltrel (dyn-tag->number 'rela))
                            (elf-dyn 'pltrelsz (bytes-length jmprel)))
                      '())
                  (if got-address
                      (list (elf-dyn 'pltgot got-address))
                      '()))
                 #:elf64? #t)
                16))
  (define dynseg-size (- (emitter-offset body) dynseg-offset))
  (define dyndata-end (emitter-offset body))

  (emit-padding! body start-offset)
  (emit-raw-blob! body image)

  (define segments
    (filter values
            (list 'phdr-placeholder
                  (and interpreter
                       (elf-segment 'interp '(r)
                                    interp-offset (+ origin-addr interp-offset) #f
                                    (+ (bytes-length interpreter) 1) #f 1))
                  (elf-segment 'load '(r w)
                               strtab-offset (+ origin-addr strtab-offset) #f
                               (- dyndata-end strtab-offset) #f 16)
                  (elf-segment 'dynamic '(r w)
                               dynseg-offset (+ origin-addr dynseg-offset) #f
                               dynseg-size #f 16)
                  (elf-segment 'load '(r w x)
                               start-offset (+ origin-addr start-offset) #f
                               (bytes-length image) memsize #x1000))))

  (define header (make-emitter 0))

  (emit-raw-blob! header (elf-header #:elf64? #t
                                     #:machine machine
                                     #:entry (+ origin-addr start-offset)
                                     #:e_flags e_flags
                                     #:segment-count (length segments)))

  (set! segments
        (cons (elf-segment 'phdr '(r x)
                           (emitter-offset header) (+ origin-addr (emitter-offset header)) #f
                           (* (elf-phentsize #:elf64? #t) (length segments)) #f 8)
              (cdr segments)))

  (for [(seg segments)]
    (emit-raw-blob! header (elf-segment->program-header seg #:elf64? #t)))

  (emit-padding! header phdr-end)
  (emit-raw-blob! header (emitter-buffer body))
  (bit-string->bytes (emitter-buffer header)))

(define (write-executable filename bs)
  (with-output-to-file filename #:exists 'replace
    (lambda () (write-bytes bs)))
  (system* "/usr/bin/env" "chmod" "+x" filename))

;;---------------------------------------------------------------------------

(module+ test
  (require rackunit)
  (check-equal? (sysv-symbol-hash-table '(#"one" #"two" #"three") #:elf64? #f)
                (bytes 2 0 0 0 ;; nbuckets
                       4 0 0 0 ;; nchain
                       0 0 0 0 ;; bucket 0
                       3 0 0 0 ;; bucket 1
                       0 0 0 0 ;; symbol 0
                       0 0 0 0 ;; symbol 1
                       1 0 0 0 ;; symbol 2
                       2 0 0 0 ;; symbol 3
                       ))
  (check-equal? (sysv-symbol-hash-table '(#"one" #"nineteen" #"three") #:elf64? #f)
                (bytes 2 0 0 0 ;; nbuckets
                       4 0 0 0 ;; nchain
                       2 0 0 0 ;; bucket 0
                       3 0 0 0 ;; bucket 1
                       0 0 0 0 ;; symbol 0
                       0 0 0 0 ;; symbol 1
                       0 0 0 0 ;; symbol 2
                       1 0 0 0 ;; symbol 3
                       ))
  (check-equal? (sysv-symbol-hash-table '(#"one" #"nineteen" #"three") #:elf64? #t)
                (bytes 2 0 0 0 0 0 0 0 ;; nbuckets
                       4 0 0 0 0 0 0 0 ;; nchain
                       2 0 0 0 0 0 0 0 ;; bucket 0
                       3 0 0 0 0 0 0 0 ;; bucket 1
                       0 0 0 0 0 0 0 0 ;; symbol 0
                       0 0 0 0 0 0 0 0 ;; symbol 1
                       0 0 0 0 0 0 0 0 ;; symbol 2
                       1 0 0 0 0 0 0 0 ;; symbol 3
                       ))
  (check-equal? (call-with-values (lambda () (build-string-table '(#"one" #"two" #"three"))) list)
                (list #"\0one\0two\0three\0"
                      (hash #"" 0
                            #"one" 1
                            #"two" 5
                            #"three" 9)))
  (check-equal? (call-with-values (lambda () (build-string-table '(#"one" #"nineteen" #"three")))
                                  list)
                (list #"\0one\0nineteen\0three\0"
                      (hash #"" 0
                            #"one" 1
                            #"nineteen" 5
                            #"three" 14)))
  (let-values (((_strtab strtab-index) (build-string-table '(#"main" #"puts" #"abort")))
               ((st1) (list (elf-symbol #"main" #"libc.so.6" 'func 'global 0 #x400200 #x0)
                            (elf-symbol #"puts" #"libc.so.6" 'func 'global 0 0 0)
                            (elf-symbol #"abort" #"libc.so.6" 'func 'global 0 0 0))))
    (check-equal? (build-symbol-table st1 strtab-index #:elf64? #t)
                  (bytes  0 0 0 0   0  0  0 0  0 0 0 0 0 0 0 0   0 0 0 0 0 0 0 0
                          1 0 0 0  18  0  0 0  0 2 64 0 0 0 0 0  0 0 0 0 0 0 0 0
                          6 0 0 0  18  0  0 0  0 0 0 0 0 0 0 0   0 0 0 0 0 0 0 0
                         11 0 0 0  18  0  0 0  0 0 0 0 0 0 0 0   0 0 0 0 0 0 0 0))
    (check-equal? (build-symbol-table st1 strtab-index #:elf64? #f)
                  (bytes  0 0 0 0  0 0 0 0   0 0 0 0   0  0  0 0
                          1 0 0 0  0 2 64 0  0 0 0 0  18  0  0 0
                          6 0 0 0  0 0 0 0   0 0 0 0  18  0  0 0
                         11 0 0 0  0 0 0 0   0 0 0 0  18  0  0 0)))

  )
