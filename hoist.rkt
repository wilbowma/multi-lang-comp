#lang racket/base

(require
 redex/reduction-semantics
 "lambda-cc.rkt"
 "lambda-h.rkt")

(provide (all-defined-out))

; Design pattern for a multi-language with syntactic distinction between source
; and target, but also a combined syntax.
(define-union-language tagHL (S. λccL) (T. λhL))
(define-union-language mergeHL λccL λhL)
(define-union-language preHL mergeHL tagHL)

(define-extended-language HL preHL
  [p ::= .... e]
  [T ::= hole
     (with-labels ([T.x (λ (T.x ...) T.e)]
                   ...
                   [T.x (λ (T.x ...) T)]
                   [x (λ (x ...) e)]
                   ...)
              p)
     (with-labels ([T.x (λ (T.x ...) T.e)]
                   ...)
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
     (let ([T.x_1 T.e] ...)
       T)]
  [kw ::= begin void eq? pair? fixnum? boolean? procedure? box? void? < + - *
      cons car cdr box unbox set-box! if]

  ; Spec, but slow
  #;[C ::= (compatible-closure-context p #:wrt e)]
  [C ::= T])

(define h->
  (reduction-relation
   HL
   #:domain p
   #:codomain p

   (--> (in-hole C (pletrec ([x any_1] ...) e))
        (with-labels ([x any_1] ...)
          (in-hole C e)))

   (--> (with-labels ([x_1 any_1] ...)
          (with-labels ([x_2 any_2] ...)
            p))
        (with-labels ([x_2 any_2]
                      ...
                      [x_1 any_1]
                      ...)
          p))))

#;(define h->+ (context-closure h-> HL T))

(parameterize ([default-language HL])
  (test-->>
   h->
   #:equiv alpha-equivalent?
   (term cc-eg)
   (term
    (with-labels
      ((factL
              (λ (c n)
                (let ((fact (closure-ref c 0)))
                  (if (eq? n 0) 1 (* n (apply-closure fact fact (- n 1)))))))
       (even?L
               (λ (c n)
                 (let ((odd? (closure-ref c 0)))
                   (if (eq? n 0) #t (apply-closure odd? odd? (- n 1))))))
       (odd?L
              (λ (c n)
                (let ((even? (closure-ref c 0)))
                  (if (eq? n 0) #f (apply-closure even? even? (- n 1))))))
       (lengthL
                (λ (c x)
                  (let ((length (closure-ref c 0)))
                    (cletrec
                     ((empty? (closure empty?L)))
                     (if (pair? x)
                         (if (apply-closure empty? empty? x)
                             0
                             (+ 1 (apply-closure length length (cdr x))))
                         -1)))))
       (empty?L (λ (c x) (let () (eq? x '())))))
      (let ((x (box 0)))
        (cletrec
         ((fact (closure factL fact)))
         (cletrec
          ((even? (closure even?L odd?)) (odd? (closure odd?L even?)))
          (begin
            (if (apply-closure even? even? (apply-closure fact fact 5))
                (cletrec
                 ((length (closure lengthL length)))
                 (set-box! x (apply-closure length length (cons 1 '()))))
                (set-box! x (cons 2 '())))
            (unbox x)))))))))
