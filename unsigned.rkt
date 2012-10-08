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

;; Unsigned arithmetic utilities.

(provide <=u32
	 <u32
	 >=u32
	 >u32)

(define two32 (expt 2 32))

(define ((lift32 f) a b)
  (f (modulo a two32) (modulo b two32)))

(define <=u32 (lift32 <=))
(define <u32 (lift32 <))
(define >=u32 (lift32 >=))
(define >u32 (lift32 >))
