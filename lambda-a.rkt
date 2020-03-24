#lang racket/base
(require redex/reduction-semantics)

(provide (all-defined-out))

; λaL is the ANF language.
(define-language λaL
  [v ::= '() fixnum boolean (void) x]
  [n ::= (cons v v)
     (car v)
     (cdr v)
     (box v)
     (unbox v)
     (set-box! v v)
     (+ v v)
     (- v v)
     (* v v)
     (eq? v v)
     (pair? v)
     (fixnum? v)
     (boolean? v)
     (procedure? v)
     (box? v)
     (void? v)
     (< v v)
     (v v ...)
     v]
  [e ::= (letrec ([x (λ (x ...) e)] ...) e)
     (let ([x n] ...) e)
     (begin e ... e)
     (if v e e)
     n]
  [x ::= variable-not-otherwise-mentioned]
  [fixnum ::= number]
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (letrec ([x any] ...) #:refers-to (shadow x ...)
          e #:refers-to (shadow x ...))
  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))
