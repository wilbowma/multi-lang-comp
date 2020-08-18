#lang racket/base
(require
 "base.rkt"
 redex/reduction-semantics
 racket/list
 racket/dict)

(provide (all-defined-out))

; λsL is the λ-calculus surface language.
; It's a Scheme-like language, but could be ML like if given a type system
(define-language λsL
  [e ::= (λ (x ...) e) (e e ...) x
     (begin e ... e) (box e) (unbox e)
     (set-box! e) (pair e e) (car e) (cdr e) fixnum (+ e e) (* e e)
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
;; NOTE: whitespace sensitive for typesetting in the paper.
(define-extended-language λiL baseL
  [e ::= (letrec ([x (λ (x ...) e)] ...) e) (e e ...) x
     (let ([x e] ...) e) (error)
     (begin e ... e) (void)
     (box e) (unbox e) (set-box! e e)
     '() (pair e e) (first e) (second e)
     fixnum (binop e e)
     #t #f (if e e e)
     (tag-pred e)]
  [x ::= variable-not-otherwise-mentioned]
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (letrec ([x any] ...) #:refers-to (shadow x ...)
          e #:refers-to (shadow x ...))
  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))

(define-extended-language λiL-eval λiL
  [S ::= env] ; must be a dict of labels to values
  [E ::= hole
     (v ... E e ...)
     (let ([x v] ... [x E] [x e] ...) e)
     (begin v ... E e ...)
     (box E)
     (unbox E)
     (set-box! E e)
     (set-box! v E)
     (pair E e)
     (pair v E)
     (first E)
     (second E)
     (if E e e)
     (binop E e)
     (binop v E)
     (tag-pred E)]
  ;; NOTE: Need vars as variable if we want to reuse in ANF def.
  [v ::= fixnum boolean '() (void) l x]
  [fv ::= (λ (x ...) e)]
  [hv ::= v fv (pair v v) (box v)])

(define-metafunction λiL-eval
  store-extend : S (l hv) ... -> S
  [(store-extend any ...)
   (env-extend any ...)])

(define (box-error? S v)
  (or (not (redex-match? λiL-eval l v))
      (not (redex-match? λiL-eval (box v)
                         (dict-ref S v)))))

(define (pair-error? v)
  (not (redex-match? λiL-eval (pair e_1 e_2) v)))

;; NOTE: These are split-up to make type setting easier.
(define λi->composition
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)

   (--> (S (in-hole E (let ([x v] ...) e)))
        (S (in-hole E (subst-all e (x ...) (v ...)))))

   (--> (S_1 (in-hole E (letrec ([x fv] ...) e)))
        (S_2 (in-hole E (subst-all e (x ...) (l ...))))

        (where (l ...) (fresh-labels x ...))
        (where (fv_1 ...) ((subst-all fv (x ...) (l ...)) ...))
        (where S_2 (store-extend S_1 (l fv_1) ...)))

   (--> (S (in-hole E (begin v ... e)))
        (S (in-hole E e)))))

(define-metafunction λiL-eval
  store-ref : S l -> hv
  [(store-ref S l) (env-ref S l)])

(define λi->admin
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)

   (--> (S (in-hole E (l v ..._1)))
        (S (in-hole E (subst-all e (x ...) (v ...))))
        (where (λ (x ..._1) e) (store-ref S l)))

   (--> (S (in-hole E (l v ...)))
        (S (error))
        (where (λ (x ...) e) (store-ref S l))
        (side-condition (term (arity-error (x ...) (v ...)))))

   (--> (S (in-hole E (l v ...)))
        (S (error))
        (where hv (store-ref S l))
        (side-condition (term (non-fv? hv))))))

(define λi->bools
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)

   ;; Booleans
   (--> (S (in-hole E (if #f e_1 e_2)))
        (S (in-hole E e_2)))
   (--> (S (in-hole E (if v e_1 e_2)))
        (S (in-hole E e_1))
        (side-condition (term (non-false? v))))

   (--> (S (in-hole E (boolean? #t)))
        (S (in-hole E #t)))
   (--> (S (in-hole E (boolean? #f)))
        (S (in-hole E #t)))
   (--> (S (in-hole E (boolean? v)))
        (S (in-hole E #f))
        (side-condition (term (non-boolean? v))))))

(define λi->boxes
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)

  ;; Boxes
  (--> (S (in-hole E (box v)))
       (S_1 (in-hole E l))
       (where l ,(fresh-label))
       (where S_1 ,(dict-set (term S) (term l) (term (box v)))))
  (--> (S (in-hole E (unbox l)))
       (S (in-hole E v))
       (where (box v) ,(dict-ref (term S) (term l))))
  (--> (S (in-hole E (unbox v)))
       (S (error))
       (side-condition (box-error? (term S) (term v))))
  (--> (S_1 (in-hole E (set-box! l v)))
       (S_2 (in-hole E (void)))
       (where S_2 ,(dict-set (term S_1) (term l) (term (box v)))))
  (--> (S (in-hole E (box? l)))
       (S (in-hole E #t))
       (where (box v) ,(dict-ref (term S) (term l))))
  (--> (S (in-hole E (box? v)))
       (S (in-hole E #f))
       (side-condition (box-error? (term S) (term v))))))

(define λi->pairs
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)

   ;; Pairs
   (--> (S (in-hole E (pair v_1 v_2)))
        (S_1 (in-hole E l))
        (where l ,(fresh-label))
        (where S_1 (store-extend S (l (pair v_1 v_2)))))
   (--> (S (in-hole E (first l)))
        (S (in-hole E v_1))
        (where (pair v_1 v_2) (store-ref S l)))
   (--> (S (in-hole E (first v)))
        (S (error))
        (side-condition (pair-error? (term v))))
   (--> (S (in-hole E (second l)))
        (S (in-hole E v_2))
        (where (pair v_1 v_2) (store-ref S l)))
   (--> (S (in-hole E (second v)))
        (S (error))
        (side-condition (pair-error? (term v))))
   (--> (S (in-hole E (pair? (pair v_1 v_2))))
        (S (in-hole E #t)))
   (--> (S (in-hole E (pair? v)))
        (S (in-hole E #f))
        (side-condition (pair-error? (term v))))))

(define λi->arith
  (reduction-relation
   λiL-eval
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

(define λi->eq
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)

   ;; Eq
   (--> (S (in-hole E (eq? v v)))
        (S (in-hole E #t)))
   (--> (S (in-hole E (eq? v_!_1 v_!_1)))
        (S (in-hole E #f)))))

(define λi->
  (union-reduction-relations
   λi->composition
   λi->admin
   λi->bools
   λi->boxes
   λi->pairs
   λi->arith
   λi->eq))

(define-metafunction λiL-eval
  print-λiL : S hv -> e
  [(print-λiL S l)
   (print-λiL S (store-ref S l))]
  [(print-λiL S (pair v_1 v_2))
   (pair (print-λiL S v_1) (print-λiL S v_2))]
  [(print-λiL S (λ (x ...) e))
   '<procedure>]
  [(print-λiL S v)
   v])

(define-metafunction λiL-eval
  eval-λiL : e -> v
  [(eval-λiL e)
   ,(second (car (apply-reduction-relation* λi-> (term (() e)))))])

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
          (if (even? 1)
              (letrec ([length (λ (x)
                                 (letrec ([empty? (λ (x) (eq? x '()))])
                                   (if (pair? x)
                                       (if (empty? x)
                                           0
                                           (+ 1 (length (cdr x))))
                                       (error))))])
                (set-box! x (length (pair 1 '()))))
              (set-box! x (pair (fact 5) '())))
          (unbox x))))))

(test-match λiL e (term s-eg))

(test-->> λi-> #:equiv (lambda (x y)
                           (alpha-equivalent? λiL (second x) y))
          (term (() (letrec ([fact (λ (n)
                                     (if (eq? n 0)
                                         1
                                         (* n (fact (- n 1)))))])
                      (fact 5))))
          (term 120))


(test-->> λi->
         #:equiv (lambda (x y)
                   (alpha-equivalent? λiL (second x) y))
         (term
          (()
           (letrec ([even? (λ (n)
                             (if (eq? n 0)
                                 #t
                                 (odd? (- n 1))))]
                    [odd? (λ (n)
                            (if (eq? n 0)
                                #f
                                (even? (- n 1))))]
                    [and (λ (n m) (if n m #f))]
                    [not (λ (n) (if n #f #t))])
             (and
              (not (even? 5))
              (and
               (even? 4)
               (even? 0))))))
         (term #t))

(test-->> λi->
          #:equiv (lambda (x y)
                    (alpha-equivalent? λiL (term (print-λiL ,(car x) ,(cadr x))) y))
          (term
           (()
            (let ([x (box 5)])
              (pair (unbox x)
                    (pair
                     (begin
                       (set-box! x 6)
                       (unbox x))
                     '())))))
          (term (pair 5 (pair 6 '()))))

(test-->> λi-> #:equiv (lambda (x y)
                         (alpha-equivalent? λiL (term (print-λiL ,(car x) ,(cadr x))) y))
          (term (() s-eg)) (term (pair 120 '())))
