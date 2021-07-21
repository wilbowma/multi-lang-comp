#lang racket/base

(require
 redex/reduction-semantics
 "../anf.rkt"
 redex/gui)

(stepper anf-eval->+ (term (() (AS (let ([x (let ([y true]) y)]) x)))))

(stepper anf-eval->+ (term (() (AS (+ (if (let ([x #t]) x) 6 7) 1)))))

(stepper anf-eval->+
         (term
          (() (AS (letrec ([fact (λ (n)
                               (if (eq? n 0)
                                   1
                                   (* n (fact (- n 1)))))])
                (fact 5))))))
