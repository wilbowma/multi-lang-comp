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

#;(define-metafunction λiL
  [(subst-all () () any) any]
  [(subst-all (x_1 x ...) (e_1 e ...) any)
   (subst-all (x ...) (e ...) (substitute any e_1 x_1))])

#;(define λi->
  (reduction-relation
   λiL-eval
   #:domain e
   #:codomain e

   (--> (S ((λ (x ...) e) e_1 ...))
        (subst-all (x_1 ...) (e_1 ...) e))

   (--> (S (let ([x_1 e_1] ...) e))
        (subst-all (x_1 ...) (e_1 ...) e))

   (--> (S (letrec ([x_1 e_1] ...
          e))
        ((S (x_1 e_1) ...) e)))

   ;; Booleans
   (--> (S (if #t e_1 e_2))
        (S e_1))
   (--> (S (boolean? #t))
        (S #t))
   (--> (S (boolean? #f))
        (S #t))
   (--> (S (boolean? v))
        (S #f)
        (side-condition
         ,(not (redex-match? λiL-eval boolean v)))))

   ;; Boxes
   (--> (S (box e))
        ((S (x (box e))) x)
        (fresh x))
   (--> (((x_1 e_1) ... (x (box e)) (x_r e_r) ...) (unbox x))
        (S e))
   (--> (((x_1 e_1) ... (x (box e)) (x_r e_r) ...) (set-box! x e_1))
        (((x_1 e_1) ... (x (box e_1)) (x_r e_r) ...) (void)))
   (--> (((x_1 e_1) ... (x (box e)) (x_r e_r) ...) (box? x))
        (((x_1 e_1) ... (x (box e_1)) (x_r e_r) ...) #t))

   ;; Pairs
   (--> (S (car (cons e_1 e_2)))
        (S e_1))
   (--> (S (cdr (cons e_1 e_2)))
        (S e_2))
   (--> (S (pair? (cons e_1 e_2)))
        (S #t))
   ))

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
