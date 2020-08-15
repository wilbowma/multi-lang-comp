#lang racket/base
(require
 "base.rkt"
 "lambda-s.rkt"
 redex/reduction-semantics)

(provide (all-defined-out))

; λaL is the ANF language.
(define-extended-language λaL baseL
  [V ::= '() fixnum boolean (void) x]
  [n ::= (pair V V) (first V) (second V)
     (box V) (unbox V) (set-box! V V)
     (binop V V)
     (tag-pred V)
     (V V ...)
     V]
  [e ::= (letrec ([x (λ (x ...) e)] ...) e)
     (let ([x n] ...) e)
     (begin n ... e)
     (if V e e)
     n]

  #;[Cm ::= (compatible-closure-context e)]
  #;[Cn ::= (compatible-closure-context e #:wrt n)]
  #;[Cv ::= (compatible-closure-context e #:wrt V)]
  [Cv ::= hole
      (V ... Cv V ...)
      (primop V ... Cv V ...)
      (let ([x n] ... [x Cv] [x n] ...) e)
      (begin n ... Cv n ... e)
      (if Cv e e)]
  [Cn ::= hole
      (let ([x n] ... [x Cn] [x n] ...) e)
      (let ([x n] ...) Cn)
      (letrec ([x n] ...) Cn)
      (begin n ... Cn n ... e)
      (begin n ... Cn)]
  [Cm ::= hole
     (let ([x n] ...) Cm)
     (letrec ([x (λ (x ...) e)]
              ...
              [x (λ (x ...) Cm)]
              [x (λ (x ...) e)]
              ...) e)
     (letrec ([x (λ (x ...) e)] ...) Cm)
     (begin n ... Cm)
     (if V Cm e)
     (if V e Cm)]

  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (letrec ([x any] ...) #:refers-to (shadow x ...)
          e #:refers-to (shadow x ...))
  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))

(define-extended-language λaL-eval λaL
  [S ::= env] ; must be a dict of labels to values
  [E ::= (let ([x v] ... [x hole] [x n] ...) e)
     (begin v ... hole e ...)]
  [v ::= '() fixnum boolean (pair v v) (λ (x ...) e) (void) l])

(define λa->composition
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)

   (--> (S (let ([x v] ...) e))
        (S (subst-all (x ...) (v ...) e)))

   (--> (S_1 (letrec ([x v] ...) e))
        (S_2 (in-hole E (subst-all (x ...) (l ...) e)))

        (where (l ...) (fresh-labels x ...))
        (where (v_1 ...) ((subst-all (x ...) (l ...) v) ...))
        (where S_2 (store-extend S_1 (l v_1) ...)))

   (--> (S (begin v ... e))
        (S e))))

(define λa->admin
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)

   (--> (S (in-hole E (l v ..._1)))
        (S (in-hole E (subst-all (x ...) (v ...) e)))
        (where (λ (x ..._1) e) (store-ref S l)))

   (--> (S (in-hole E (l v ...)))
        (S (error))
        (where (λ (x ...) e) (store-ref S l))
        (side-condition (not (eq? (length (term (x ...)))
                                  (length (term (v ...)))))))))

(define λa->bools
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)

   (--> (S (if #f e_1 e_2))
        (S e_2))
   (--> (S (if v e_1 e_2))
        (S e_1)
        (where (v_!_1 v_!_1) (v #f)))

   (--> (S (in-hole E (boolean? #t)))
        (S (in-hole E #t)))
   (--> (S (in-hole E (boolean? #f)))
        (S (in-hole E #t)))
   (--> (S (in-hole E (boolean? v)))
        (S (in-hole E #f))
        (side-condition (boolean-error? (term v))))))

(define λa->boxes
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)

   ;; Boxes
   (--> (S (in-hole E (box v)))
        (S_1 (in-hole E l))
        (where l ,(fresh-label))
        (where S_1 (store-set S l (box v))))
   (--> (S (in-hole E (unbox l)))
        (S (in-hole E v))
        (where (box v) (store-ref S l)))
   (--> (S (in-hole E (unbox v)))
        (S (error))
        (side-condition (box-error? (term S) (term v))))
   (--> (S_1 (in-hole E (set-box! l v)))
        (S_2 (in-hole E (void)))
        (where S_2 (store-set S_1 l (box v))))
   (--> (S (in-hole E (box? l)))
        (S (in-hole E #t))
        (where (box v) (store-ref S l)))
   (--> (S (in-hole E (box? v)))
        (S (in-hole E #f))
        (side-condition (box-error? (term S) (term v))))))

(define λa->pairs
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)

   ;; Pairs
   (--> (S (in-hole E (first (pair v_1 v_2))))
        (S (in-hole E v_1)))
   (--> (S (in-hole E (first v)))
        (S (error))
        (side-condition (pair-error? (term v))))
   (--> (S (in-hole E (second (pair v_1 v_2))))
        (S (in-hole E v_2)))
   (--> (S (in-hole E (second v)))
        (S (error))
        (side-condition (pair-error? (term v))))
   (--> (S (in-hole E (pair? (pair v_1 v_2))))
        (S (in-hole E #t)))
   (--> (S (in-hole E (pair? v)))
        (S (in-hole E #f))
        (side-condition (pair-error? (term v))))))

(define λa->arith
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)

   ;; Arith
   (--> (S (in-hole E (arith-op fixnum_1 fixnum_2)))
        (S (in-hole E v))
        (where v (denote arith-op fixnum_1 fixnum_2)))

   (--> (S (in-hole E (arith-op v_1 v_2)))
        (S (error))
        (side-condition (term (non-fixnum? v_1))))
   (--> (S (in-hole E (arith-op v_1 v_2)))
        (S (error))
        (side-condition (term (non-fixnum? v_1))))
   (--> (S (in-hole E (fixnum? fixnum_1)))
        (S (in-hole E #t)))
   (--> (S (in-hole E (fixnum? v)))
        (S (in-hole E #f))
        (side-condition (term (non-fixnum? v))))))

(define λa->eq
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)

   ;; Eq
   (--> (S (in-hole E (eq? v v)))
        (S (in-hole E #t)))
   (--> (S (in-hole E (eq? v_!_1 v_!_1)))
        (S (in-hole E #f)))))

(define λa->
  (union-reduction-relations
   λa->composition
   λa->admin
   λa->bools
   λa->boxes
   λa->pairs
   λa->arith
   λa->eq))
