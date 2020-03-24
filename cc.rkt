#lang racket/base
(require
 racket/string
 racket/set)

(require
 redex/reduction-semantics
 racket/syntax
 "lambda-s.rkt"
 "lambda-cc.rkt")

(provide (all-defined-out))

; Design pattern for a multi-language with syntactic distinction between source
; and target, but also a combined syntax.
(define-union-language tagCCL (S. λiL) (T. λccL))
(define-union-language mergeCCL λiL λccL)
(define-union-language preCCL mergeCCL tagCCL)
; For left-to-right translation order, to make the translation faster and less
; non-deterministic.
(define-extended-language CCL preCCL
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
     (let ([x_1 T.e] ...)
       T)]
  [kw ::= begin void eq? pair? fixnum? boolean? procedure? box? void? < + - *
      cons car cdr box unbox set-box! if])

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

(define (redex-id-get-base-name x)
  (car (string-split (symbol->string x) "«")))

(define (fresh-id x)
  (format-symbol "~a" (redex-id-get-base-name x)))

(define (fresh-label x)
  (format-symbol "~aL" (redex-id-get-base-name x)))

(define cc->
  (reduction-relation
   CCL
   #:domain e
   #:codomain e

   (-->
    (letrec ([x_f (λ (x ...) e_1)] ...)
      e_2)
    (pletrec ([x_fl (λ (x_c x ...)
                      (let ([x_f0 (closure-ref x_cc e_i)]
                            ...)
                        e_1))]
              ...)
             (cletrec ([x_f (closure x_fl x_f0 ...)]
                       ...)
                      e_2))
    (where (x_fl ...) ,(map fresh-label (term (x_f ...))))
    (where (x_c ...) ,(map fresh-id (map (lambda _ 'c) (term (x_f ...)))))
    (where ((x_f0 ...) ...) ((free-vars (λ (x ...) e_1)) ...))
    (where ((x_cc ...) ...)
           ,(for/list ([ls (term ((x_f0 ...) ...))]
                       [x_c (term (x_c ...))])
              (for/list ([_ ls])
                x_c)))
    (where ((e_i ...) ...)
           ,(for/list ([ls (term ((x_f0 ...) ...))])
              (build-list (length ls) values))))

   (--> (e_1 e ...) (apply-closure e_1 e_1 e ...))))

#;(define cc->+ (compatible-closure cc-> CCL e))
(define cc->+ (context-closure cc-> CCL T))

(parameterize ([default-language CCL])
  (test-->>
   cc->+
   #:equiv alpha-equivalent?
   (term
    (letrec ([fact (λ (n)
                     (if (eq? n 0)
                         1
                         (* n (fact (- n 1)))))])
      (fact 5)))
   (term
    (pletrec ([fact-label
               (λ (c x)
                 (let ([fact (closure-ref c 0)])
                   (if (eq? x 0)
                       1
                       (* x (apply-closure fact fact (- x 1))))))])
             (cletrec ([fact (closure fact-label fact)])
                      (apply-closure fact fact 5)))))

  (test-->>
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
            (unbox x)))))))))
  )

;; TODO: Add reduction relations, do union-reduction-relation, and show simulation.
