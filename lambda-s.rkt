#lang racket/base
(require
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
(define-language λiL
  [e ::= (letrec ([x (λ (x ...) e)] ...) e) (e e ...) x
     (let ([x e] ...) e) (error)
     (begin e ... e) (void)
     (box e) (unbox e) (set-box! e e)
     '() (pair e e) (first e) (second e)
     fixnum (binop e e)
     #t #f (if e e e)
     (tag-pred e)]
  [x ::= variable-not-otherwise-mentioned]
  [fixnum ::= integer]
  [arith-op ::= + - * / <]
  [binop ::= arith-op eq?]
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
  [l ::= (variable-prefix lb)]
  [E ::= hole
     (letrec ([x v] ...) E)
     (v ... E e ...)
     (let ([x v] ... [x E] [x e] ...) e)
     (let ([x v] ...) E)
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
  [v ::= fixnum #t #f '() (pair v v) (λ (x ...) e) (void) l])

(define-metafunction λiL
  [(subst-all () () any) any]
  [(subst-all (x_1 x ...) (e_1 e ...) any)
   (subst-all (x ...) (e ...) (substitute any x_1 e_1))])

(require racket/syntax)
(define fresh-label
  (let ([x (box 0)])
    (lambda ([name ""])
      (set-box! x (add1 (unbox x)))
      (format-symbol "lb~a~a" name (unbox x)))))

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

; For some reason, eval wouldn't work. *shrug*.
(define (arith-op->proc v)
  (case v
    [(-) -]
    [(+) +]
    [(*) *]
    [(/) /]
    [(<) <]))

(define λi->
  (reduction-relation
   λiL-eval
   #:domain (S e)
   #:codomain (S e)
   ;#:arrow ==>

   (--> (S (in-hole E (let ([x v] ...) e)))
        (S (in-hole E (subst-all (x ...) (v ...) e))))

   (--> (S_1 (in-hole E (letrec ([x v] ...) e)))
        (S_2 (in-hole E (subst-all (x ...) (l ...) e)))

        (where (l ...) ,(map fresh-label (term (x ...))))
        (where (v_1 ...) ((subst-all (x ...) (l ...) v) ...))
        ; A secret dict-merge option, if you break interfaces.
        (where S_2 ,(append (term S_1) (term ((l . v_1) ...)))))

   (--> (S (in-hole E (l v ..._1)))
        (S (in-hole E (subst-all (x ...) (v ...) e)))
        (where (λ (x ..._1) e) ,(dict-ref (term S) (term l))))

   (--> (S (in-hole E (l v ...)))
        (S (error))
        (where (λ (x ...) e) ,(dict-ref (term S) (term l)))
        (side-condition (not (eq? (length (term (x ...)))
                                  (length (term (v ...)))))))

   (--> (S (in-hole E (begin v ... e)))
        (S (in-hole E e)))

   ;; Booleans
   (--> (S (in-hole E (if #f e_1 e_2)))
        (S (in-hole E e_2)))
   (--> (S (in-hole E (if v e_1 e_2)))
        (S (in-hole E e_1))
        (where (v_!_1 v_!_1) (v #f)))

   (--> (S (in-hole E (boolean? #t)))
        (S (in-hole E #t)))
   (--> (S (in-hole E (boolean? #f)))
        (S (in-hole E #t)))
   (--> (S (in-hole E (boolean? v)))
        (S (in-hole E #f))
        (side-condition (boolean-error? (term v))))

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
       (side-condition (box-error? (term S) (term v))))

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
       (side-condition (pair-error? (term v))))

  ;; Arith
  (--> (S (in-hole E (arith-op fixnum_1 fixnum_2)))
       (S (in-hole E v))
       (where v ,((arith-op->proc (term arith-op))
                  (term fixnum_1) (term fixnum_2))))

  (--> (S (in-hole E (arith-op v_1 v_2)))
       (S (error))
       (side-condition (fixnum-error? (term v_1))))
  (--> (S (in-hole E (arith-op v_1 v_2)))
       (S (error))
       (side-condition (fixnum-error? (term v_2))))
  (--> (S (in-hole E (fixnum? fixnum_1)))
       (S (in-hole E #t)))
  (--> (S (in-hole E (fixnum? fixnum_1)))
       (S (in-hole E #f))
       (side-condition (fixnum-error? (term v_2))))

  ;; Eq
  (--> (S (in-hole E (eq? v v)))
       (S (in-hole E #t)))
  (--> (S (in-hole E (eq? v_!_1 v_!_1)))
       (S (in-hole E #f)))

  ;; Damn you Redex!
  #;with
  #;[(==> (S1 (in-hole E e1)) (S2 (in-hole e2)))
   (--> (S1 e1) (S2 e2))]))

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
                                (even? (- n 1))))])
             (pair
              (even? 5)
              (pair
               (even? 4)
               (pair (even? 0) '()))))))
         (term (pair #f (pair #t (pair #t '())))))

(test-->> λi->
          #:equiv (lambda (x y)
                    (alpha-equivalent? λiL (second x) y))
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
                         (alpha-equivalent? λiL (second x) y))
          (term (() s-eg)) (term (pair 120 '())))
