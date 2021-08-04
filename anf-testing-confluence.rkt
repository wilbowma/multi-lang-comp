#lang racket/base

(require
 redex/reduction-semantics
 "anf.rkt"
 redex/gui)

;; Confluence fixed!
;(stepper anf->+ (term (AS (let ([x (let ([y true]) y)]) x))))

;(stepper anf->+ (term (AS (let ([x true]) x))))
(stepper anf->+ (term (AS (let ([x (+ 1 2)]) x))))

;(stepper anf->+ (term (AS (let ([x (begin (set! y true) y)]) x))))

;(stepper anf->+ (term (AS (+ (if (let ([x #t]) x) 6 7) 1))))
