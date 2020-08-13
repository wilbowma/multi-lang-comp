#lang racket/base

(require
 redex/reduction-semantics
 racket/syntax
 "lambda-s.rkt"
 "lambda-a.rkt")

(provide (all-defined-out))

(set-cache-size! 1000)
(check-redundancy #t)

; Design pattern for a multi-language with syntactic distinction between source
; and target, but also a combined syntax.
(define-union-language tagANFL (S. λiL) (T. λaL))
(define-union-language mergeANFL λiL λaL)
(define-union-language preANFL mergeANFL tagANFL)
(define-extended-language ANFL preANFL
  #;[C ::= (compatible-closure-context e)] ;TODO Bug in Redex
  [C ::= T] #;(compatible-closure-context T)
  [E ::= hole
     (V ... E e ...)
     (primop V ... E e ...)
     (let ([x n]
           ...
           [x E]
           [x e] ...)
       e)
     (begin n ... E e ... e)
     (if E e e)]
  ; For left-to-right translation order, to make the translation faster and less
  ; non-deterministic.
  [T ::= hole
     (letrec ([T.x (λ (T.x ...) T.e)]
              ...
              [T.x (λ (T.x ...) T)]
              [x (λ (x ...) e)]
              ...)
       e)
     (letrec ([T.x (λ (T.x ...) T.e)] ...)
       T)
     (T.V ... T e ...)
     (primop T.V ... T e ...)
     (begin T.e ... T e ...)
     (if T e e)
     (if T.V T.e ... T e ...)
     (let ([T.x_1 T.n]
           ...
           [x_i T]
           [x_n e] ...)
       e)
     (let ([x_1 T.n] ...)
       T)])

; Ensures termination without some termination conditions?
; NOTE: NOPE. Maybe alpha-equivalence issues in the cache?
(current-cache-all? #t)

(define anf->
  (reduction-relation
   ANFL
   #:domain e
   #:codomain e

   (-->
    (in-hole E (let ([x e] ...) e_2))
    (let ([x e] ...) (in-hole E e_2))
    (where (E_!_1 E_!_1) (hole E)))

   (-->
    (in-hole E (if n e_1 e_2))
    (letrec ([j (λ (x) (in-hole E x))])
      (if n (j e_1) (j e_2)))
    (fresh j)
    (fresh x)
    (where (E_!_1 E_!_1) (hole E)))

   #;(-->
    (in-hole E (if n e_1 e_2))
    #;(if n (in-hole E e_1) (in-hole E e_2))
    ; Join-point Optimization
    (letrec ([j (λ (x) (in-hole E x))])
      (if n (j e_1) (j e_2)))
    ;    (fresh tmp)
    (fresh j)
    (fresh x)
    (where (E_!_1 E_!_1) (hole E)))

   (-->
    (in-hole E (begin e_s ... e))
    (begin e_s ... (in-hole E e))
    (where (E_!_1 E_!_1) (hole E)))

   (-->
    (in-hole E (letrec ([x any_1] ...) e))
    (letrec ([x any_1] ...) (in-hole E e))
    ; Termination
    (where (E_!_1 E_!_1) (hole E)))

   (--> (in-hole E n) (let ([x n]) (in-hole E x))
    (fresh x)
    ; Optimizations
    ; TODO: This optimization can be enabled for "predicates"?
    #;(side-condition
     (not (redex-match? ANFL (in-hole E_1 (if hole e_1 e_2)) (term E))))
    (side-condition
     (not (redex-match? ANFL (in-hole E_1 (begin e_1 ... hole e ... e_2)) (term E))))
    ; Termination conditions
    (where (E_!_1 E_!_1) (hole E))
    (side-condition
     (not (redex-match? ANFL (in-hole E_1 (let ([x_1 e_1] ... [x_2 hole] [x_3 e_3] ...) e_2)) (term E))))
    (side-condition
     (not (redex-match? ANFL V (term n)))))))

(define anf->+ (context-closure anf-> ANFL C))

(define-metafunction ANFL
  compile-anf : S.e -> T.e
  [(compile-anf S.e)
   ,(car (apply-reduction-relation* anf->+ (term S.e)))])

(module+ test
  (parameterize ([default-language ANFL])
    (test-->>
     anf->+
     #:equiv alpha-equivalent?
     (term
      (letrec ([fact (λ (n)
                       (if (eq? n 0)
                           1
                           (* n (fact (- n 1)))))])
        (fact 5)))
     (term
      (letrec ([fact (λ (n)
                       (let ([x (eq? n 0)])
                         (if x
                             1
                             (let ([x (- n 1)])
                               (let ([x2 (fact x)])
                                 (* n x2))))))])
        (fact 5))))

    (test-->>
     anf->+
     #:equiv alpha-equivalent?
     (term ((if ((x 5) 4) meow bark) 5 2))

     (term
      (let ((x1 (x 5)))
        (letrec ((j (λ (x2) (x2 5 2))))
          (let ((x3 (x1 4)))
            (if x3
                (j meow)
                (j bark))))))
     )
    #;(test-->>
       cc->+
       #:equiv alpha-equivalent?
       (term s-eg)
       (term
        (let ((x (box 0)))
          (pletrec
           ((factL
             (λ (c n)
               (let ((fact (closure-ref c 0)))
                 (if (eq? n 0)
                     1
                     (* n (apply-closure fact fact (- n 1))))))))
           (cletrec
            ((fact (closure factL fact)))
            (pletrec
             ((even?L
               (λ (c n)
                 (let ((odd? (closure-ref c 0)))
                   (if (eq? n 0)
                       #t
                       (apply-closure odd? odd? (- n 1))))))
              (odd?L
               (λ (c n)
                 (let ((even? (closure-ref c 0)))
                   (if (eq? n 0)
                       #f
                       (apply-closure even? even? (- n 1)))))))
             (cletrec
              ((even? (closure even?L odd?))
               (odd? (closure odd?L even?)))
              (begin
                (if (apply-closure
                     even?
                     even?
                     (apply-closure fact fact 5))
                    (pletrec
                     ((lengthL
                       (λ (c x)
                         (let ((length (closure-ref c 0)))
                           (pletrec
                            ((empty?L (λ (c x) (let () (eq? x '())))))
                            (cletrec
                             ((empty? (closure empty?L)))
                             (if (pair? x)
                                 (if (apply-closure empty? empty? x)
                                     0
                                     (+
                                      1
                                      (apply-closure
                                       length
                                       length
                                       (cdr x))))
                                 -1)))))))
                     (cletrec
                      ((length (closure lengthL length)))
                      (set-box!
                       x
                       (apply-closure length length (cons 1 '())))))
                    (set-box! x (cons 2 '())))
                (unbox x)))))))))))

;; TODO: Add reduction relations, do union-reduction-relation, and show simulation.
