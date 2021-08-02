#lang racket/base

(require
 redex/reduction-semantics
 "../anf.rkt"
 redex/gui)


;; Take second path; there's a bug in the first one.
;(stepper anf->+ (term (AS (let ([x (let ([y true]) y)]) x))))
(stepper anf->+ (term (AS (let ([x (begin (set! y true) y)]) x))))

(stepper anf->+ (term (AS (+ (if (let ([x #t]) x) 6 7) 1))))
