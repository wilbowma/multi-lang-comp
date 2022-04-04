#lang racket/base
(require
 "base.rkt"
 "lambda-s.rkt"
 redex/reduction-semantics)

(provide (all-defined-out))

; λaL is the ANF language.
(define-extended-language λaL baseL
  [v ::= '() fixnum boolean (void) x]
  [n ::= v (v ...) (primop v v ...)]
  [e ::= n (letrec ([x (λ (x ...) e)] ...) e) (let ([x n] ...) e) (begin n ... e) (if v e e)]

  #;[Cm ::= (compatible-closure-context e)]
  #;[Cn ::= (compatible-closure-context e #:wrt n)]
  #;[Cv ::= (compatible-closure-context e #:wrt V)]
  [Cv ::= Cn
      (in-hole Cn (v ... hole v ...))
      (in-hole Cn (primop v ... hole v ...))
      (in-hole Cm (if hole e e))]
  [Cn ::= Cm
      (in-hole Cm (let ([x n] ... [x hole] [x n] ...) e))
      (in-hole Cm (begin n ... hole n ... e))]
  [Cm ::= hole
     (let ([x n] ...) Cm)
     (letrec ([x (λ (x ...) e)] ...
              [x (λ (x ...) Cm)]
              [x (λ (x ...) e)] ...) e)
     (letrec ([x (λ (x ...) e)] ...) Cm)
     (begin n ... Cm)
     (if v Cm e)
     (if v e Cm)]

  ;; For display only
  [Γ ::= ∅]
  [τ ::= ∅]

  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (letrec ([x any] ...) #:refers-to (shadow x ...)
          e #:refers-to (shadow x ...))
  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))

(define-extended-language λaL-eval λaL
  [S ::= env] ; must be a dict of labels to values
  [E ::= (let ([x v] ... [x hole] [x n] ...) e) (begin v ... hole n ... e)]
  [v ::= .... l]
  [fv ::= (λ (x ...) e)]
  [hv ::= v fv (pair v v) (box v)])

(define λa->composition
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λa

   (-->λa (S (let ([x v] ...) e))
        (S (subst-all e (x ...) (v ...))))

   (-->λa (S_1 (letrec ([x fv] ...) e))
        (S_2 (in-hole E (subst-all e (x ...) (l ...))))

        (where (l ...) (fresh-labels x ...))
        (where (v_1 ...) ((subst-all fv (x ...) (l ...)) ...))
        (where S_2 (store-extend S_1 (l v_1) ...)))

   (-->λa (S (begin v ... e))
        (S e))))

(define-metafunction λaL-eval
  hcompose : E e -> e
  [(hcompose E n) (in-hole E n)]
  [(hcompose E (let ([x n] ...) e))
   (let ([x n] ...) (hcompose E e))]
  [(hcompose E (begin n ... e))
   (begin n ... (hcompose E e))]
  [(hcompose E (if v e_1 e_2))
   (if v (hcompose E e_1) (hcompose E e_2))]
  [(hcompose E (letrec ([x any] ...) e))
   (letrec ([x any] ...) (hcompose E e))])

(define λa->admin
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λa

   (-->λa (S (in-hole E (l v ..._1)))
        (S (hcompose E (subst-all e (x ...) (v ...))))
        (where (λ (x ..._1) e) (store-ref S l)))

   (-->λa (S (in-hole E (l v ...)))
        (S (error))
        (where (λ (x ...) e) (store-ref S l))
        (side-condition (term (arity-error (x ...) (v ...)))))

   (-->λa (S (in-hole E (l v ...)))
        (S (error))
        (where hv (store-ref S l))
        (side-condition (term (non-fv? hv))))))

(define λa->bools
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λa

   (-->λa (S (if #f e_1 e_2))
        (S e_2))
   (-->λa (S (if v e_1 e_2))
        (S e_1)
        (side-condition (term (non-false? v))))

   (-->λa (S (in-hole E (boolean? #t)))
        (S (in-hole E #t)))
   (-->λa (S (in-hole E (boolean? #f)))
        (S (in-hole E #t)))
   (-->λa (S (in-hole E (boolean? v)))
        (S (in-hole E #f))
        (side-condition (term (non-boolean? v))))))

(define λa->boxes
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λa

   ;; Boxes
   (-->λa (S (in-hole E (box v)))
        (S_1 (in-hole E l))
        (where l ,(fresh-label))
        (where S_1 (store-set S l (box v))))
   (-->λa (S (in-hole E (unbox l)))
        (S (in-hole E v))
        (where (box v) (store-ref S l)))
   (-->λa (S (in-hole E (unbox v)))
        (S (error))
        (side-condition (box-error? (term S) (term v))))
   (-->λa (S_1 (in-hole E (set-box! l v)))
        (S_2 (in-hole E (void)))
        (where S_2 (store-set S_1 l (box v))))
   (-->λa (S (in-hole E (box? l)))
        (S (in-hole E #t))
        (where (box v) (store-ref S l)))
   (-->λa (S (in-hole E (box? v)))
        (S (in-hole E #f))
        (side-condition (box-error? (term S) (term v))))))

(define λa->pairs
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λa

   ;; Pairs
   (-->λa (S (in-hole E (pair v_1 v_2)))
        (S_1 (in-hole E l))
        (where S_1 (store-set S l (pair v_1 v_2)))
        (fresh l))
   (-->λa (S (in-hole E (first l)))
        (S (in-hole E v_1))
        (where (pair v_1 v_2) (store-ref S l)))
   (-->λa (S (in-hole E (first v)))
        (S (error))
        (side-condition (pair-error? (term v))))
   (-->λa (S (in-hole E (second l)))
        (S (in-hole E v_2))
        (where (pair v_1 v_2) (store-ref S l)))
   (-->λa (S (in-hole E (second v)))
        (S (error))
        (side-condition (pair-error? (term v))))
   (-->λa (S (in-hole E (pair? l)))
        (S (in-hole E #t))
        (where (pair v_1 v_2) (store-ref S l)))
   (-->λa (S (in-hole E (pair? v)))
        (S (in-hole E #f))
        (side-condition (pair-error? (term v))))))

(define λa->arith
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λa

   ;; Arith
   (-->λa (S (in-hole E (arith-op fixnum_1 fixnum_2)))
        (S (in-hole E v))
        (where v (denote arith-op fixnum_1 fixnum_2)))

   (-->λa (S (in-hole E (arith-op v_1 v_2)))
        (S (error))
        (side-condition (term (non-fixnum? v_1))))
   (-->λa (S (in-hole E (arith-op v_1 v_2)))
        (S (error))
        (side-condition (term (non-fixnum? v_1))))
   (-->λa (S (in-hole E (fixnum? fixnum_1)))
        (S (in-hole E #t)))
   (-->λa (S (in-hole E (fixnum? v)))
        (S (in-hole E #f))
        (side-condition (term (non-fixnum? v))))))

(define λa->eq
  (reduction-relation
   λaL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λa

   ;; Eq
   (-->λa (S (in-hole E (eq? v v)))
        (S (in-hole E #t)))
   (-->λa (S (in-hole E (eq? v_!_1 v_!_1)))
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
