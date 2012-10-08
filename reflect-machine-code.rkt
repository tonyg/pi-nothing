#lang racket/base
;; Copyright (C) 2012 Tony Garnock-Jones <tonygarnockjones@gmail.com>
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

(require (only-in '#%foreign ffi-call))
(require ffi/unsafe)

(provide (struct-out executable-machine-code)
	 reflect-machine-code)

(struct executable-machine-code (bytes arg-spec result-spec callout)
	#:property prop:procedure (struct-field-index callout))
	
(define builtins (ffi-lib #f))
(define %scheme-malloc-code
  (get-ffi-obj "scheme_malloc_code" builtins (_fun (size : _long) -> (_bytes o size))))

(define (reflect-machine-code bs arg-spec result-spec)
  (define xbs (%scheme-malloc-code (bytes-length bs)))
  (bytes-copy! xbs 0 bs)
  (executable-machine-code xbs
			   arg-spec
			   result-spec
			   (ffi-call xbs arg-spec result-spec)))
