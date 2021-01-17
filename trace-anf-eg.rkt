#lang racket/base

(require
 "anf.rkt"
 redex/reduction-semantics
 redex/gui)

(traces
 anf-eval->+
 (term (()
        (AS (letrec ([fact (λ (n)
                             (if (eq? n 0)
                                 1
                                 (* n (fact (- n 1)))))])
              (fact 5))))))
