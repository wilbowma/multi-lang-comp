#lang racket/base
(require redex/reduction-semantics)

(provide (all-defined-out))

; λsL is the λ-calculus surface language.
; It's a Scheme-like language, but could be ML like if given a type system
(define-language λsL
  [e ::= (λ (x ...) e) (e e ...) x
     (begin e ... e) (box e) (unbox e)
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
  [e ::= (letrec ([x (λ (x ...) e)] ...) e) (e e ...) x
     (let ([x e] ...) e) (error)
     (begin e ... e) (void)
     (box e) (unbox e) (set-box! e e)
     empty (pair e e) (first e) (second e)
     fixnum (arith-op e e)
     true false (if e e e)
     (< e e) (eq? e e)
     (tag-pred e)]
  [x ::= variable-not-otherwise-mentioned]
  [fixnum ::= integer]
  [arith-op ::= + - * /]
  [tag-pred ::= pair? fixnum? boolean?]
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))
  (letrec ([x any] ...) #:refers-to (shadow x ...)
          e #:refers-to (shadow x ...))
  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))

(define (int61? x) (<= (min-int 61) x (max-int 61)))
(define (max-int word-size) (sub1 (expt 2 (sub1 word-size))))
(define (min-int word-size) (* -1 (expt 2 (sub1 word-size))))

(define-extended-language λiL-eval λiL
  [S ::= any] ; must be a dict of labels to values
  [l ::= (variable-prefix l)]
  [v ::= fixnum true false empty (pair v v) (λ (x ...) e) (box v) l])

(define-metafunction λiL
  [(subst-all () () any) any]
  [(subst-all (x_1 x ...) (e_1 e ...) any)
   (subst-all (x ...) (e ...) (substitute any e_1 x_1))])

(require racket/syntax)
(define fresh-label
  (let ([x (box 0)])
    (lambda _
      (set-box! x (add1 (unbox x)))
      (format-symbol "l~a" (unbox x)))))

(define (box-error? S v)
  (or (not (redex-match? λiL-eval l v))
      (not (redex-match? λiL-eval (box v)
                         (dict-ref S v)))))

(define (boolean-error? v)
  (not (redex-match? λiL-eval boolean v)))

(define (pair-error? v)
  (not (redex-match? λiL-eval (pair e_1 e_2) v)))

(define (fixnum-error? v)
  (not (redex-match? λiL-eval fixnum v)))

(require racket/dict)
(define λi->
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)

   (--> (S ((λ (x ..._1) e) v ..._1))
        (S (subst-all (x ...) (v ...) e)))

   (--> (S ((λ (x ...) e) v ...))
        (S (error))
        (side-condition (not (eq? (length (term (x ...)))
                                  (length (term (v ...)))))))

   (--> (S (let ([x v] ...) e))
        (S (subst-all (x ...) (v ...) e)))

   (--> (S_1 (letrec ([x v] ...) e))
        (S_2 (let ([x l] ...) e))

        (where (l ...) ,(map fresh-label (term (x ...))))
        (where S_2 ,(append (term S_1) (term ((l v) ...)))))

   (--> (S (l v ...))
        (S (v_1 v ...))
        (where v_1 ,(dict-ref (term S) (term l))))

   ;; Booleans
   (--> (S (if #f e_1 e_2))
        (S e_2))
   (--> (S (if v e_1 e_2))
        (S e_1)
        (where (v_!_1 v_!_1) (v #f)))

   (--> (S (boolean? #t))
        (S #t))
   (--> (S (boolean? #f))
        (S #t))
   (--> (S (boolean? v))
        (S #f)
        (side-condition (boolean-error? (term v))))

  ;; Boxes
  (--> (S (box e))
       ((S (l (box e))) l)
       (where l ,(fresh-label)))
  (--> (S (unbox l))
       (S v)
       (where (box v) ,(dict-ref (term S) (term l))))
  (--> (S (unbox v))
       (S (error))
       (side-condition (box-error? (term S) (term v))))
  (--> (S_1 (set-box! l v))
       (S_2 (void))
       (where S_2 ,(dict-set (term S) (term l) (term (box v)))))
  (--> (S (box? l))
       (S #t)
       (where (box v) ,(dict-ref (term S) (term l))))
  (--> (S (box? v))
       (S #f)
       (side-condition (box-error? (term S) (term v))))

  ;; Pairs
  (--> (S (first (pair v_1 v_2)))
       (S v_1))
  (--> (S (first v))
       (S (error))
       (side-condition (pair-error? (term v))))
  (--> (S (second (pair v_1 v_2)))
       (S v_2))
  (--> (S (second v))
       (S (error))
       (side-condition (pair-error? (term v))))
  (--> (S (pair? (pair v_1 v_2)))
       (S #t))
  (--> (S (pair? v))
       (S #f)
       (side-condition (pair-error? (term v))))

  (--> (S (airth-op fixnum_1 fixnum_2))
       (S v)
       (where v (eval (term (arith-op fixnum_1 fixnum_2)))))

  (--> (S (airth-op v_1 v_2))
       (S (error))
       (side-condition (fixnum-error? (term v_1))))
  (--> (S (airth-op v_1 v_2))
       (S (error))
       (side-condition (fixnum-error? (term v_2))))
  (--> (S (fixnum? fixnum_1))
       (S #t))
  (--> (S (fixnum? fixnum_1))
       (S #f)
       (side-condition (fixnum-error? (term v_2))))))

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
