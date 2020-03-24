#lang racket/base
(require
 redex/reduction-semantics)

(provide (all-defined-out))

; aL is an assembly language.
; It has infinite registers, an abstract notion of tagged word-size data and
; pointers, a primitive memory operations, push and pop onto an abstract stack.
(define-language aL
  [n ::= w (alloc w tag) (+ r w) (* r w) (- r w) (to-word w) (mref r w)]
  [e ::=
     (begin e ...)
     (with-label label e)
     s]
  [s ::=
     (with-label label s)
     (set! r n)
     (push w)
     (pop r)
     (mset! r w w)
     (jump-if (flag r w) label)
     (jump-if (tag-eq? r tag) label)
     (jump w)]
  [w ::= (immediate number tag) r (word number) label]
  [r ::= (variable-prefix r)]
  [label ::= variable-not-otherwise-mentioned]
  [flag ::= eq? <]
  [tag ::= 'bool 'pair 'box 'void 'empty 'fixnum 'procedure]

  ; Spec
  #;[C ::= (compatible-closure-context e)]
  ; Speed
  [C ::= hole (begin s ... hole e ...)])

(current-cache-all? #t)

(define flatten->
  (reduction-relation
   aL

   #:domain e
   #:codomain e

   (-->
    (begin e ... (begin e_n ...) e_r ...)
    (begin e ... e_n ... e_r ...))

   (-->
    (with-label label (begin e e_r ...))
    (begin (with-label label e) e_r ...))))

(define flatten->+ (context-closure flatten-> aL C))
