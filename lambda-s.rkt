#lang racket/base
(require
 "base.rkt"
 redex/reduction-semantics
 racket/list)

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
     (let ([x e] ...) e) (begin e ... e) (void)
     (box e) (unbox e) (set-box! e e)
     '() (pair e e) (first e) (second e)
     fixnum (binop e e)
     #t #f (if e e e)
     (tag-pred e) (error)]
  [x ::= variable-not-otherwise-mentioned]

  ;; for display
  [Γ ::= ∅]
  [τ ::= ∅]
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (letrec ([x any] ...) #:refers-to (shadow x ...)
          e #:refers-to (shadow x ...))
  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))

(define-extended-language λiL-eval λiL
  ;[S ::= env] ; must be a dict of labels to values
  [E ::= hole (let ([x v] ... [x E] [x e] ...) e) (begin v ... E e ...)
     (if E e e) (primop v ... E e ...) (v ... E e ...)]

  [Cs ::= hole
      (e ... Cs e ...)
      (primop e ... Cs e ...)
      (if Cs e e)
      (if e Cs e)
      (if e e Cs)
      (let ([x e] ... [x Cs] [x e] ...) e)
      (let ([x e] ...) Cs)
      (letrec ([x (λ (x ...) e)] ... [x (λ (x ...) Cs)] [x (λ (x ...) e)] ...) e)
      (letrec ([x fv] ...) Cs)
      (begin e ... Cs e ...)]

  ; make boundary markers reserved keywords
  ;[w ::= SA AS]

  [S ::= ((l hv) ...)]
  [e ::= .... l]
  [v ::= fixnum boolean '() (void) l x]
  [fv ::= (λ (x ...) e)]
  [hv ::= v fv (pair v v) (box v)])

(define-metafunction λiL-eval
  store-extend : S (l hv) ... -> S
  [(store-extend S (l hv) ...)
   (env-extend S (l (hv)) ...)])

(define-metafunction λiL-eval
  store-ref : S l -> hv
  [(store-ref S l) ,(car (term (env-ref S l)))])

(define (box-error? S v)
  (or (not (redex-match? λiL-eval l v))
      (not (redex-match? λiL-eval (box v)
                         (term (store-ref ,S ,v))))))

(define (pair-error? v)
  (not (redex-match? λiL-eval (pair e_1 e_2) v)))

(define-metafunction λiL-eval
  [(non-pair? any)
   ,(pair-error? (term any))])

;; NOTE: These are split-up to make type setting easier.
(define λi->composition
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λs

   (-->λs (S (in-hole E (let ([x v] ...) e)))
         (S (in-hole E (subst-all e (x ...) (v ...)))))

   (-->λs (S_1 (in-hole E (letrec ([x fv] ...) e)))
         (S_2 (in-hole E (subst-all e (x ...) (l ...))))

         (where (l ...) (fresh-labels x ...))
         (where (fv_1 ...) ((subst-all fv (x ...) (l ...)) ...))
         (where S_2 (store-extend S_1 (l fv_1) ...)))

   (-->λs (S (in-hole E (begin v ... e)))
         (S (in-hole E e)))))

(define λi->proc
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λs

   (-->λs (S (in-hole E (l v ..._1)))
         (S (in-hole E (subst-all e (x ...) (v ...))))
         (where (λ (x ..._1) e) (store-ref S l)))

   (-->λs (S (in-hole E (l v ...)))
         (S (error))
         (where (λ (x ...) e) (store-ref S l))
         (side-condition (term (arity-error (x ...) (v ...)))))

   (-->λs (S (in-hole E (l v ...)))
         (S (error))
         (where hv (store-ref S l))
         (side-condition (term (non-fv? hv))))))

(define λi->bools
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λs

   ;; Booleans
   (-->λs (S (in-hole E (if #f e_1 e_2)))
         (S (in-hole E e_2)))
   (-->λs (S (in-hole E (if v e_1 e_2)))
         (S (in-hole E e_1))
         (side-condition (term (non-false? v))))

   (-->λs (S (in-hole E (boolean? #t)))
         (S (in-hole E #t)))
   (-->λs (S (in-hole E (boolean? #f)))
         (S (in-hole E #t)))
   (-->λs (S (in-hole E (boolean? v)))
        (S (in-hole E #f))
        (side-condition (term (non-boolean? v))))))

(define λi->boxes
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λs

  ;; Boxes
  (-->λs (S (in-hole E (box v)))
        (S_1 (in-hole E lb))
        (fresh lb)
        (where S_1 (store-extend S (lb (box v)))))
  (-->λs (S (in-hole E (unbox l)))
        (S (in-hole E v))
        (where (box v) (store-ref S l)))
  (-->λs (S (in-hole E (unbox v)))
        (S (error))
        (side-condition (box-error? (term S) (term v))))
  (-->λs (S_1 (in-hole E (set-box! l v)))
        (S_2 (in-hole E (void)))
        (where S_2 (store-extend S_1 (l (box v)))))
  (-->λs (S (in-hole E (box? l)))
        (S (in-hole E #t))
        (where (box v) (store-ref S l)))
  (-->λs (S (in-hole E (box? v)))
        (S (in-hole E #f))
        (side-condition (box-error? (term S) (term v))))))

(define λi->pairs
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λs

   ;; Pairs
   (-->λs (S (in-hole E (pair v_1 v_2)))
         (S_1 (in-hole E lb))
         (fresh lb)
         (where S_1 (store-extend S (lb (pair v_1 v_2)))))
   (-->λs (S (in-hole E (first l)))
         (S (in-hole E v_1))
         (where (pair v_1 v_2) (store-ref S l)))
   (-->λs (S (in-hole E (second l)))
         (S (in-hole E v_2))
         (where (pair v_1 v_2) (store-ref S l)))
   (-->λs (S (in-hole E (pair? (pair v_1 v_2))))
         (S (in-hole E #t)))
   (-->λs (S (in-hole E (pair? v)))
         (S (in-hole E #f))
         (side-condition (term (non-pair? v))))
   (-->λs (S (in-hole E (second v)))
          (S (error))
          (side-condition (term (non-pair? v))))
   (-->λs (S (in-hole E (first v)))
          (S (error))
          (side-condition (term (non-pair? v))))
   ))

(define λi->error
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)

   #:arrow -->λs
   (-->λs (S (in-hole E (error))) (S (error)))))

(define λi->arith
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λs

   ;; Arith
   (-->λs (S (in-hole E (arith-op fixnum_1 fixnum_2)))
         (S (in-hole E v))
         (where v (denote arith-op fixnum_1 fixnum_2)))

   (-->λs (S (in-hole E (arith-op v_1 v_2)))
         (S (error))
         (side-condition (term (non-fixnum? v_1))))
   (-->λs (S (in-hole E (arith-op v_1 v_2)))
         (S (error))
         (side-condition (term (non-fixnum? v_1))))
   (-->λs (S (in-hole E (fixnum? fixnum_1)))
         (S (in-hole E #t)))
   (-->λs (S (in-hole E (fixnum? v)))
         (S (in-hole E #f))
         (side-condition (term (non-fixnum? v))))))

(define λi->eq
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)
   #:arrow -->λs

   ;; Eq
   (-->λs (S (in-hole E (eq? v v)))
         (S (in-hole E #t)))
   (-->λs (S (in-hole E (eq? v_1 v_2)))
          (S (in-hole E #f))
          (side-condition (term (not-equal? v_1 v_2))))))

(define λi->
  (union-reduction-relations
   λi->composition
   λi->proc
   λi->bools
   λi->boxes
   λi->pairs
   λi->arith
   λi->eq
   λi->error))

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

(define-metafunction λiL-eval
  eval/print-λiL : e -> e
  [(eval/print-λiL e)
   ,(let ([x (car (apply-reduction-relation* λi-> (term (() e))))])
      (term (print-λiL ,(car x) ,(cadr x))))])

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
                    (alpha-equivalent? λiL-eval (term (print-λiL ,(car x) ,(cadr x))) y))
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
                         (alpha-equivalent? λiL-eval (term (print-λiL ,(car x) ,(cadr x))) y))
          (term (() s-eg)) (term (pair 120 '())))
