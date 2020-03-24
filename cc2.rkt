#lang racket/base
(require racket/set)

(require
 redex/reduction-semantics
 "lambda-s.rkt"
 "lambda-cc.rkt")

(define-union-language preCCL (S. λiL) (T. λccL))

(define-extended-language CCL preCCL
  [S.e ::= .... (ST T.e)]
  [T.e ::= .... (TS S.e)]
  [TC ::= (compatible-closure-context T.e)]
  [e ::= S.e T.e]
  [T ::= hole
     (pletrec ([T.x (λ (T.x ...) T.e)]
               ...
               [T.x (λ (T.x ...) T)]
               [x (λ (x ...) e)]
               ...)
              e)
     (pletrec ([T.x (λ (T.x ...) T.e)] ...)
              T)
     (cletrec ([T.x (closure T.e ...)]
               ...
               [T.x (closure T.e ... T e ...)]
               [x (closure e ...)] ...)
              e)
     (cletrec ([T.x (closure T.e ...)] ...)
              T)
     (apply-closure T.e ... T e ...)
     (kw T.e ... T e ...)
     (let ([T.x_1 T.e]
           ...
           [x_i T]
           [x_n e] ...)
       e)
     (let ([T.x T.e] ...)
       T)]
  [kw ::= begin void eq? pair? fixnum? boolean? procedure? box? void? < + - * cons car cdr box unbox set-box! if]
  [terminal ::= number boolean x]
  [x ::= S.x T.x])

(define-metafunction CCL
  free-vars : any -> (x ...)
  [(free-vars x) (x)]
  [(free-vars (λ (x ...) e))
   (free-vars ((substitute e x 0) ...))]
  [(free-vars (letrec ([x_1 any_1] ...) e))
   (free-vars ((substitute e x_1 0)
               ...
               (substitute (any_1 ...) x_1 0)
               ...))]
  [(free-vars (pletrec ([x_1 any_1] ...) e))
   (free-vars ((substitute e x_1 0)
               ...
               (substitute (any_1 ...) x_1 0)
               ...))]
  [(free-vars (cletrec ([x_1 any_1] ...) e))
   (free-vars ((substitute e x_1 0)
               ...
               (substitute (any_1 ...) x_1 0)
               ...))]
  [(free-vars (let ([x_1 e_1] ...) e_2))
   (free-vars ((substitute e_2 x_1 0)
               ...
               e_1 ...))]
  [(free-vars (any ...))
   ,(set-union '() (term (x ... ...)))
   (where ((x ...) ...) ((free-vars any) ...))]
  [(free-vars any) ()])

(define cc->
  (reduction-relation
   CCL
   #:domain T.e
   #:codomain T.e

   (-->
    (TS (letrec ([x_f (λ (x ...) e_1)] ...)
          e_2))
    (pletrec ([x_fl (λ (x_c x ...)
                      (let ([x_f0 (closure-ref x_cc e_i)]
                            ...)
                        (TS e_1)))]
              ...)
             (cletrec ([x_f (closure x_fl x_f0 ...)]
                       ...)
                      (TS e_2)))
    (fresh ((x_fl ...) (x_f ...)))
    (fresh ((x_c ...) (x_f ...)))
    (where ((x_f0 ...) ...) ((free-vars (λ (x ...) e_1)) ...))
    (where ((x_cc ...) ...)
           ,(for/list ([ls (term ((x_f0 ...) ...))]
                       [x_c (term (x_c ...))])
              (for/list ([_ ls])
                x_c)))
    (where ((e_i ...) ...)
           ,(map (lambda (x) (build-list (length x) values)) (term ((x_f0 ...) ...)))))

   (--> (TS (e_1 e ...)) (apply-closure (TS e_1) (TS e_1) (TS e) ...))

   (--> (TS T.e) T.e)
   (--> (TS (ST e)) e)
   (--> (TS (in-hole T S.e)) (TS (in-hole T (ST (TS S.e))))
        (where (any_!_1 any_!_1) (hole T)))))

(define cc->+ (context-closure cc-> CCL T))

(current-cache-all? #t)

#;(parameterize ([default-language CCL])
  (test-->>
   cc->+
   #:equiv alpha-equivalent?
   (term
    (TS
     (letrec ([fact (λ (n)
                      (if (eq? n 0)
                          1
                          (* n (fact (- n 1)))))])
       (fact 5))))
   (term
    (pletrec ([fact-label
               (λ (c x)
                 (let ([fact (closure-ref c 0)])
                   (if (eq? x 0)
                       1
                       (* x (apply-closure fact fact (- x 1))))))])
             (cletrec ([fact (closure fact-label fact)])
                      (apply-closure fact fact 5))))))

