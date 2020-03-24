#lang racket/base
(require redex/reduction-semantics)

; λmilL is the λ-calculus language in monadic form.
(define-language λmilL
  [v ::= fixnum x]
  [n ::= (box v) (unbox v) (set-box! v) (cons v v) (car v) (cdr v)
     (+ v v) (* v v)]
  [m ::= (λ (x ...) n) (v v ...) x (begin m ... m)
     (let ([x m] ...) m) (letrec ([x m] ...) m)]
  [x ::= variable-not-otherwise-mentioned]
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (letrec ([x e] ...) #:refers-to (shadow x ...)
          e #:refers-to (shadow x ...))
  (let ([x e] ...) e #:refers-to (shadow x ...)))
