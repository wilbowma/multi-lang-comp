#lang racket/base

(require
 redex/reduction-semantics
 racket/syntax
 "lambda-s.rkt"
 "lambda-a.rkt")

(provide (all-defined-out))

(set-cache-size! 1000)
(check-redundancy #t)
(current-cache-all? #t)

; Design pattern for a multi-language with syntactic distinction between source
; and target, but also a combined syntax.
(define-union-language tagANFL (S. λiL) (T. λaL))
(define-extended-language ANFL tagANFL
  ; NOTE: Hacks to get type setting to work
  [T.V ::= .... (TS S.e)]
  [T.n ::= .... (TS S.e)]
  [T.e ::= .... (TS S.e)]
  [T.x ::= .... ]
  [S.x ::= .... ]
  [S.e ::= .... (ST T.e)]
  [x ::= S.x T.x]
  [primop ::= T.primop S.primop]

  [e ::= S.e T.e]

  [T ::= (in-hole C (TS C))]
  #;[C ::= (compatible-closure-context T.e)]
  [C ::= hole
     (let ([x e] ...) C)
     (letrec ([x (λ (x ...) e)]
              ...
              [x (λ (x ...) C)]
              [x (λ (x ...) e)]
              ...) e)
     (letrec ([x (λ (x ...) e)] ...) C)
     (begin e ... C)
     (if e C e)
     (if e e C)]
  [En ::= hole
      (let ([T.x T.n] ... [x En] [x e] ...) e)
      (let ([T.x T.n] ...) En)
      (letrec ([T.x T.n] ...) En)
      (begin T.n ... En e ...)
      (begin T.n ... En)]
  [Em ::= hole (if T.V Em e) (if T.V e Em)
      (let ([T.x T.n] ...) Em)
      (letrec ([x any] ...) Em)
      (begin T.n ... Em)]
  [Ev ::= hole
     (T.V ... Ev e ...)
     (T.primop T.V ... Ev e ...)
     (let ([T.x T.n] ... [x En] [x e] ...) e)
     (begin T.n ... En e ...)
     (if Ev e e)])

(define anf->
  (reduction-relation
   ANFL
   ;#:domain T.e
   ;#:codomain T.e ;; One of these tests fail due to an apparent bug:
   ; reduction-relation: relation reduced to (TS (ST (letrec ((fact«614» (λ (n«615») (TS (if (eq? n«615» 0) 1 (* n«615» (fact«614» (- n«615» 1)))))))) (fact«614» 5)))) via an unnamed rule, which is outside its codomain
   ; > (redex-match? ANFL T.e '(TS (ST (letrec ((fact«614» (λ (n«615») (TS (if (eq? n«615» 0) 1 (* n«615» (fact«614» (- n«615» 1)))))))) (fact«614» 5)))))
   ; > #t
   #:arrow -->a

   (-->a T.e (ST T.e))

   (-->a
    (in-hole Ev (let ([T.x S.e] ...) S.e_2))
    (ST (let ([T.x (TS S.e)] ...) (TS (in-hole Ev S.e_2))))
    (where (Ev_!_1 Ev_!_1) (hole Ev)))

   (-->a
    (in-hole Ev (if T.V S.e_1 S.e_2))
    (ST (letrec ([j (λ (x) (in-hole Ev x))])
      (if T.V (TS (j S.e_1)) (TS (j S.e_2)))))
    (fresh j)
    (fresh x)
    (fresh x2)
    (side-condition (not (redex-match? ANFL Em (term Ev))))
    #;(where (Ev_!_1 Ev_!_1) (hole Ev)))

   (-->a
    (in-hole Em (if T.V S.e_1 S.e_2))
    (ST (if T.V (TS S.e_1) (TS S.e_2))))

   (-->a
    (in-hole Ev (begin S.e_r ... S.e))
    (ST (begin (TS S.e_r) ... (TS (in-hole Ev S.e))))
    #;(where (Ev_!_1 Ev_!_1) (hole Ev)))

   (-->a
    (in-hole Ev (letrec ([T.x (λ any S.e_1)] ...) S.e))
    (ST (letrec ([T.x (λ any (TS S.e_1))] ...) (TS (in-hole Ev S.e))))
    ; Termination
    #;(where (Ev_!_1 Ev_!_1) (hole Ev)))

   (-->a (in-hole Ev T.n) (ST (let ([x T.n]) (TS (in-hole Ev x))))
    (fresh x)
    ; Optimizations
    ; TODO: This optimization can be enabled for "predicates"?
    #;(side-condition
     (not (redex-match? ANFL (in-hole E_1 (if hole e_1 e_2)) (term E))))
    #;(side-condition
     (not (redex-match? ANFL (in-hole Ev_1 (begin T.n ... hole S.e ... S.e_2)) (term Ev))))
    ; Termination conditions
    #;(where (Ev_!_1 Ev_!_1) (hole Ev))
    #;(side-condition
     (not (redex-match? ANFL (in-hole Ev_1 (let ([T.x_1 T.n_1] ... [S.x_2 hole] [S.x_3 S.e_3] ...) S.e_2)) (term Ev))))
    (side-condition
     (not (redex-match? ANFL En (term Ev))))
    (side-condition
     (not (redex-match? ANFL T.V (term T.n)))))))

(define st->
  (reduction-relation
   ANFL
   #:domain T.e
   #:codomain T.e
   #:arrow -->st

   (-->st (in-hole C (TS (ST e))) (in-hole C e))
   (-->st (in-hole C (ST (TS e))) (in-hole C e))))

(define anf->+
  (union-reduction-relations
   (context-closure anf-> ANFL T)
   st->))

(define-metafunction ANFL
  compile-anf : S.e -> T.e
  [(compile-anf S.e)
   T.e
   (where (T.e) ,(apply-reduction-relation* anf->+ (term (TS S.e))))])

(define (step n x)
  (if (zero? n)
      x
      (step (sub1 n) (car (apply-reduction-relation anf->+ x)))))

(module+ test
  (parameterize ([default-language ANFL])
    (test-->>
     anf->+
     #:equiv alpha-equivalent?
     (term
      (TS (letrec ([fact (λ (n)
                       (if (eq? n 0)
                           1
                           (* n (fact (- n 1)))))])
        (fact 5))))
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
     (term (TS ((if ((x 5) 4) meow bark) 5 2)))

     (term
      (let ((x1 (x 5)))
        (let ((x3 (x1 4)))
          (letrec ((j (λ (x2) (x2 5 2))))
            (if x3
                (j meow)
                (j bark)))))))
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
