#lang racket/base
(require redex/reduction-semantics)

(provide (all-defined-out))

; λsL is the λ-calculus surface language.
; It's a Scheme-like language, but could be ML like if given a type system
(define-language λsL
  [e ::= (λ (x ...) e) (e e ...) x (begin e ... e) (box e) (unbox e)
     (set-box! e) (cons e e) (car e) (cdr e) fixnum (+ e e) (* e e)
     (let ([x e] ...) e) (letrec ([x e] ...) e)
     (void) '()
     (if e e e)
     (eq? e e)
     (pair? e)
     (fixnum? e)
     (boolean? e)
     (procedure? e)
     (box? e)
     (void? e)
     (< e e)
     boolean]
  [x ::= variable-not-otherwise-mentioned]
  [fixnum ::= integer] ; TODO restrict to fixnum range
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (letrec ([x e_1] ...) #:refers-to (shadow x ...)
          e_2 #:refers-to (shadow x ...))
  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))

; λiL is the λ-calculus internal language.
(define-language λiL
  [e ::= (letrec ([x (λ (x ...) e)] ...) e) (e e ...) x (begin e ... e) (box e)
     (unbox e) (set-box! e e) (cons e e) (car e) (cdr e) fixnum (+ e e) (- e e) (* e e)
     (let ([x e] ...) e)
     (void) '()
     (if e e e)
     (eq? e e)
     (pair? e)
     (fixnum? e)
     (boolean? e)
     (procedure? e)
     (box? e)
     (void? e)
     (< e e)
     boolean]
  [x ::= variable-not-otherwise-mentioned]
  [fixnum ::= number]
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (letrec ([x any] ...) #:refers-to (shadow x ...)
          e #:refers-to (shadow x ...))
  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))


(define-term s-eg
  (let ([x (box 0)])
    (letrec ([fact (λ (n)
                     (if (eq? n 0)
                         1
                         (* n (fact (- n 1)))))])
      (letrec ([even? (λ (n)
                        (if (eq? n 0)
                            #t
                            (odd? (- n 1))))]
               [odd? (λ (n)
                       (if (eq? n 0)
                           #f
                           (even? (- n 1))))])
        (begin
          (if (even? (fact 5))
              (letrec ([length (λ (x)
                                 (letrec ([empty? (λ (x) (eq? x '()))])
                                   (if (pair? x)
                                       (if (empty? x)
                                           0
                                           (+ 1 (length (cdr x))))
                                       -1)))])
                (set-box! x (length (cons 1 '()))))
              (set-box! x (cons 2 '())))
          (unbox x))))))

(test-match λiL e (term s-eg))
