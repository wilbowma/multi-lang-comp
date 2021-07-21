#lang racket/base

(require
 redex/reduction-semantics
 "../anf.rkt"
 redex/gui)


; Bug: not confluent, so doesn't normalize
;(stepper aot-normalize (term (let ([x (let ([y true]) y)]) x)))

;(stepper anf->+ (term (AS (let ([x (let ([y true]) y)]) x))))

(stepper aot-normalize (term (+ (if (let ([x #t]) x) 6 7) 1)))

;; Run to completion
;(stepper anf->+ (term (AS (let ([x (let ([y true]) y)]) x))))
(stepper anf->+ (term (AS (+ (if (let ([x #t]) x) 6 7) 1))))

;; Bug, causes infinite loop. Must be missing a termination condition.
#;(stepper aot-normalize
         (term
          (letrec ([fact (λ (n)
                               (if (eq? n 0)
                                   1
                                   (* n (fact (- n 1)))))])
                (fact 5))))
