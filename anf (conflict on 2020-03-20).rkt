#lang racket/base
(require
 racket/string
 racket/set)

(require
 redex/reduction-semantics
 racket/syntax
 "lambda-s.rkt"
 "lambda-a.rkt")

; Design pattern for a multi-language with syntactic distinction between source
; and target, but also a combined syntax.
(define-union-language tagANFL (S. λiL) (T. λaL))
(define-union-language mergeANFL λiL λaL)
(define-union-language preANFL mergeANFL tagANFL)
; For left-to-right translation order, to make the translation faster and less
; non-deterministic.
(define-extended-language ANFL preANFL
  ;[C ::= (compatible-closure-context S.e)]
  [E ::= hole
     (v ... E e ...)
     (kw v ... E e ...)
     (let ([x n]
           ...
           [x E]
           [x e] ...)
       e)
     (begin n ... E e ... e)
     (if E e e)]
  [T ::= hole
     (letrec ([T.x (λ (T.x ...) T.e)]
              ...
              [T.x (λ (T.x ...) T)]
              [x (λ (x ...) e)]
              ...)
       e)
     (letrec ([T.x (λ (T.x ...) T.e)] ...)
       T)
     (T.v ... T e ...)
     (kw T.v ... T e ...)
     (begin T.n ... T e ...)
     (if T e e)
     (if T.n T.e ... T e ...)
     (let ([T.x_1 T.n]
           ...
           [x_i T]
           [x_n e] ...)
       e)
     (let ([x_1 T.n] ...)
       T)]
  [kw ::= void eq? pair? fixnum? boolean? procedure? box? void? < + - *
      cons car cdr box unbox set-box!])

(define anf->
  (reduction-relation
   ANFL
   #:domain e
   #:codomain e

   (-->
    (in-hole E (let ([x e] ...) e_2))
    (let ([x e] ...)
      (in-hole E e_2))
    (where (E_!_1 E_!_1) (hole E)))

   (-->
    (in-hole E (if n e_1 e_2))
    (if n (in-hole E e_1) (in-hole E e_2))
    #;(letrec ([x_j (λ (x) (in-hole E x))])
      (if n (x_j e_1) (x_j e_2)))
    #;(fresh x_j)
    #;(fresh x)
    (where (E_!_1 E_!_1) (hole E)))

   (-->
    (in-hole E n)
    (let ([x n])
      (in-hole E x))
    (fresh x)
    (where (E_!_1 E_!_1) (hole E))
    (side-condition
     (not (redex-match? ANFL (in-hole E_1 (let ([x_1 e_1] ... [x_2 hole] [x_3 e_3] ...) e_2)) (term E))))
    (side-condition
     (not (redex-match? ANFL v (term n)))))))

#;(define anf->+ (compatible-closure anf-> ANFL S.e))
(define anf->+ (context-closure anf-> ANFL T))

(current-cache-all? #t)

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
            (unbox x))))))))))

;; TODO: Add reduction relations, do union-reduction-relation, and show simulation.
