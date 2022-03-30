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
(define-union-language tagANFL (S. λiL-eval) (A. λaL-eval))
(define-extended-language ANFL tagANFL
  ; NOTE: Hacks to get type setting to work
  [A.x ::= .... ]
  [S.x ::= .... ]

  ;; Multi-language
  [A.v ::= .... (AS S.e)]
  [A.n ::= .... (AS S.e)]
  [A.e ::= .... (AS S.e)]
  [S.e ::= .... (SA A.e)]
  [x ::= S.x A.x]
  [primop ::= A.primop S.primop]
  [e ::= S.e A.e]

  #;[T ::= (in-hole C (AS A.Cm))]
  [T ::= (in-hole C (AS hole))
     (in-hole C (lambda (x ...) (AS hole)))]


  [C ::= A.Cv]

  [S ::= S.env]

  ; For display
  [H ::= S.env]
  [S.Γ ::= ∅]
  [A.Γ ::= ∅]
  [A.τ ::= ∅]
  [S.τ ::= ∅])

(define-metafunction ANFL
  [(non-Cn? any)
   ,(not (redex-match ANFL A.Cn (term any)))])

(define-metafunction ANFL
  [(non-Cm? any)
   ,(not (redex-match ANFL A.Cm (term any)))])

(define-metafunction ANFL
  [(non-Tv? any)
   ,(not (redex-match ANFL A.v (term any)))])

(define anf->
  (reduction-relation
   ANFL
   ; #:domain S.e
   ; #:codomain S.e
   ;; One of these tests fail due to an apparent bug:
   ; reduction-relation: relation not defined for (letrec ((fact«711» (λ (n«615») (let ((x (eq? n«615» 0))) (if x 1 (let ((x1 (- n«615» 1))) (let ((x2 (fact«711» x1))) (* n«615» x2)))))))) (fact«711» 5))
   ; > (redex-match? ANFL S.e '(letrec ((fact«711» (λ (n«615») (let ((x (eq? n«615» 0))) (if x 1 (let ((x1 (- n«615» 1))) (let ((x2 (fact«711» x1))) (* n«615» x2)))))))) (fact«711» 5)))
   ; #t
   #:arrow -->a

   (-->a A.e (SA A.e) "A-normal")

   (-->a
    (in-hole S.E (let ([A.x S.e] ...) S.e_2))
    (SA (let ([A.x (AS S.e)] ...) (AS (in-hole S.E S.e_2))))
    (side-condition (not (equal? (term hole) (term S.E))))
    "A-merge-l")

   (-->a
    (in-hole S.E (begin S.e_r ... S.e))
    (SA (begin (AS S.e_r) ... (AS (in-hole S.E S.e))))
    (side-condition (not (equal? (term hole) (term S.E))))
    "A-merge-b")

   (-->a
    (in-hole S.E (letrec ([A.x (λ any S.e_1)] ...) S.e))
    (SA (letrec ([A.x (λ any (AS S.e_1))] ...) (AS (in-hole S.E S.e))))
    "A-merge-r")

   (-->a
    (in-hole S.E (if A.v S.e_1 S.e_2))
    (SA (letrec ([j (λ (x) (in-hole S.E x))])
          (if A.v (AS (j S.e_1)) (AS (j S.e_2)))))
    (fresh j)
    (fresh x)
    (side-condition (term (non-Cn? S.E)))
    "A-join")

   (-->a
    (in-hole A.Cm (if A.v S.e_1 S.e_2))
    (SA (if A.v (AS S.e_1) (AS S.e_2)))
    "A-merge-if")

   (-->a (in-hole S.E A.n) (SA (let ([x A.n]) (AS (in-hole S.E x))))
    "A-lift"
    (fresh x)
    ; Optimizations
    ; TODO: This optimization can be enabled for "predicates"?
    #;(side-condition
     (not (redex-match? ANFL (in-hole E_1 (if hole e_1 e_2)) (term E))))
    #;(side-condition
     (not (redex-match? ANFL (in-hole S.E_1 (begin A.n ... hole S.e ... S.e_2)) (term S.E))))
    ; Termination conditions
    #;(where (S.E_!_1 S.E_!_1) (hole S.E))
    #;(side-condition
     (not (redex-match? ANFL (in-hole S.E_1 (let ([A.x_1 A.n_1] ... [S.x_2 hole] [S.x_3 S.e_3] ...) S.e_2)) (term S.E))))
    (side-condition
     (term (non-Cn? S.E)))
    (side-condition
     (term (non-Tv? A.n))))))

(define st->
  (reduction-relation
   ANFL
   ;#:domain A.e
   ;#:codomain A.e
   #:arrow -->st

   (-->st (in-hole C (AS (SA A.e))) (in-hole C A.e) "Boundary-1")
   (-->st (in-hole C (SA (AS S.e))) (in-hole C S.e) "Boundary-2")))

(define anf->+
  (union-reduction-relations
   (context-closure anf-> ANFL T)
   st->))

(define (maybe-apply-reduction-relation r e)
  (with-handlers ([values (lambda _ #f)])
    (apply-reduction-relation r e)))

(define-judgment-form ANFL
  #:mode (not-anf->+j I)

  [(where (#f) ,(maybe-apply-reduction-relation anf->+ (term e_1)))
   -------------------
   (not-anf->+j e_1)])

(define-judgment-form ANFL
  #:mode (anf->j I O)

  [(where (e_p ... e e_r ...) ,(maybe-apply-reduction-relation anf-> (term e_1)))
   -------------------
   (anf->j e_1 e)])

(define-judgment-form ANFL
  #:mode (st->j I O)

  [(where (e_p ... e e_r ...) ,(maybe-apply-reduction-relation st-> (term e_1)))
   -------------------
   (st->j e_1 e)])

(define-judgment-form ANFL
  #:mode (anf->+j I O)

  [(anf->j e_1 e)
   -------------------
   (anf->+j (in-hole T e_1) (in-hole T e))]

  [(st->j e_1 e)
   ----------------
   (anf->+j e_1 e)])

(define-judgment-form ANFL
  #:mode (anf->*j I O)

  [(where (e) ,(apply-reduction-relation* anf->+ (term e_1)))
   -------------------
   (anf->*j e_1 e)])

(define-judgment-form ANFL
  #:mode (anf-compile I O)

  [(anf->*j (AS S.e) A.e) (not-anf->+j A.e)
   ---------------------
   (anf-compile S.e A.e)])

(define-judgment-form ANFL
  #:mode (λi->j I O)

  [(where ((H_2 S.e_2)) ,(maybe-apply-reduction-relation λi-> (term (H_1 S.e_1))))
   -------------------
   (λi->j (H_1 S.e_1) (H_2 S.e_2))])

(define-judgment-form ANFL
  #:mode (λi->j* I O)

  [-------------------
   (λi->j* (H_1 S.e_1) (H_1 S.e_1))]

  [(λi->j (H_1 S.e_1) (H_2 S.e_2))
   (λi->j* (H_1 S.e_1) (H_3 S.e_3))
   -------------------
   (λi->j* (H_1 S.e_1) (H_3 S.e_3))])

(define-judgment-form ANFL
  #:mode (λa->j I O)

  [(where ((H e)) ,(maybe-apply-reduction-relation λa-> (term any_1)))
   -------------------
   (λa->j any_1 (H e))])

(define-judgment-form ANFL
  #:mode (λa->j* I O)

  [-------------------
   (λa->j* (H_1 S.e_1) (H_1 S.e_1))]

  [(λa->j (H_1 S.e_1) (H_2 S.e_2))
   (λa->j* (H_1 S.e_1) (H_3 S.e_3))
   -------------------
   (λa->j* (H_1 S.e_1) (H_3 S.e_3))])

(define-judgment-form ANFL
  #:mode (anf-eval->+ I O)

  [(λi->j (H_1 S.e_1) (H_2 S.e_2))
   ----------------------------- "S-Interp"
   (anf-eval->+ (H_1 S.e_1) (H_2 S.e_2))]

  [(λi->j (H_1 S.e_1) (H_2 S.e_2))
   ----------------------------- "AS-Interp"
   (anf-eval->+ (H_1 (AS S.e_1)) (H_2 (AS S.e_2)))]

  [(λa->j (H_1 A.e_1) (H_2 A.e_2))
   ----------------------------- "A-Run"
   (anf-eval->+ (H_1 A.e_1) (H_2 A.e_2))]

  [(λa->j (H_1 A.e_1) (H_2 A.e_2))
   ----------------------------- "SA-Run"
   (anf-eval->+ (H_1 (SA A.e_1)) (H_2 (SA A.e_2)))]

  [(anf->+j A.e_1 A.e_2)
   ;; TODO: Need to be able to translate the heap.
   ----------------------------- "JIT"
   (anf-eval->+ (H_1 A.e_1) (H_1 A.e_2))])

(define-judgment-form ANFL
  #:mode (anf-eval->* I O)

  [(anf-eval->+ (H_1 e_1) (H_2 e_2))
   (anf-eval->* (H_2 e_2) (H_3 e_3))
   -----------------------------
   (anf-eval->* (H_1 e_1) (H_3 e_3))]

  [-----------------------------
   (anf-eval->* (H e) (H e))])

(define-judgment-form ANFL
  #:mode (aot-normalize I O)
  #:contract (aot-normalize S.e A.e)

  [(where (A.e) ,(apply-reduction-relation* anf->+ (term (AS S.e))))
   ----------------------- "AOT"
   (aot-normalize S.e A.e)])

(define-metafunction ANFL
  compile-anf : S.e -> A.e
  [(compile-anf S.e)
   A.e
   (where (A.e) ,(apply-reduction-relation* anf->+ (term (AS S.e))))])

(define (step n x)
  (if (zero? n)
      x
      (step (sub1 n) (car (apply-reduction-relation anf->+ x)))))

(module+ test
  (parameterize ([default-language λaL])
    (test-->>
     anf->+
     #:equiv alpha-equivalent?
     (term
      (AS (letrec ([fact (λ (n)
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
     (term (AS ((if ((x 5) 4) meow bark) 5 2)))

     (term
      (let ((x1 (x 5)))
        (let ((x3 (x1 4)))
          (letrec ((j (λ (x2) (x2 5 2))))
            (if x3
                (j meow)
                (j bark)))))))
    (test-->>
     anf->+
     #:equiv alpha-equivalent?
     (term (AS (+ (if (let ([x #t]) x) 6 7) 1)))

     (term
      (let ([x #t])
        (letrec ([j (λ (x) (+ x 1))])
          (if x (j 6) (j 7))))))

    (test-judgment-holds
     (anf-eval->* (() (AS (+ (if (let ([x #t]) x) 6 7) 1)))
                  (_ 7)))

    (test-judgment-holds
     (anf-eval->* (() (AS (+ (if (let ([x #t]) x) 6 7) 1)))
                  (() (let ([x_2 #t])
                        (letrec ([x_3 (λ (x_1) (+ x_1 1))])
                          (if x_2 (x_3 6) (x_3 7)))))))

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
