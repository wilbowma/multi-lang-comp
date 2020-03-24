#lang racket/base
(require
 redex/reduction-semantics)

(provide (all-defined-out))

; λccL is the closure-converted λ-calculus.
(define-language λccL
  [e ::= (pletrec ([x (λ (x ...) e)] ...)
                  e)
     (cletrec ([x (closure x e ...)]
               ...)
              e)
     ; Need distinct form syntax for applying closure to avoid infinite loop in
     ; normalization.
     ; Could also do type-directed, if types were different.
     ; Or.. maybe language tag of some kind
     ;   ((source #%app) e_1 e ...) -> ((target #%app) e_1 e_1 e ...)
     (apply-closure e e ...)
     ; should have more primitive apply to enable closure optimizations.
     x
     (begin e ... e) (box e) (unbox e)
     (set-box! e e) (cons e e) (car e) (cdr e) fixnum (+ e e) (- e e) (* e e)
     (let ([x e] ...) e)
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
     (closure-ref e e)
     boolean]
  [x ::= variable-not-otherwise-mentioned]
  [fixnum ::= number] ; TODO restrict to fixnum range
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))

  (pletrec ([x any_1] ...) #:refers-to (shadow x ...)
          e_2 #:refers-to (shadow x ...))

  (cletrec ([x any_1] ...) #:refers-to (shadow x ...)
           e_2 #:refers-to (shadow x ...))

  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))


(define-term cc-eg
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
          (unbox x))))))))
