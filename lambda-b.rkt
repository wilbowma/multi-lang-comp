#lang racket/base
(require
 redex/reduction-semantics)

(provide (all-defined-out))

; λbL is the bit-specified λ-calculus.
(define-language λbL
  [p ::= (with-labels ([x (λ (x ...) e)] ...)
           p)
     e]
  [e ::= (call e e ...)
     x
     (begin e ... e)
     (alloc e tag)
     (immediate number tag) ; TODO restrict range
     (word number)
     (mref e e)
     (mset! e e e)
     (+ e e) (- e e) (* e e)
     (let ([x e] ...) e)
     (compare (flag e e) e e)
     (compare (tag-eq? e tag) e e)
     ]
  [flag ::= eq? <]
  ; TODO: Can't use 'bool?
  [tag ::= 'bool 'pair 'box 'void 'empty 'fixnum 'procedure]
  [x ::= variable-not-otherwise-mentioned]
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))

  (with-labels ([x any_1] ...) #:refers-to (shadow x ...)
          e_2 #:refers-to (shadow x ...))

  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))

