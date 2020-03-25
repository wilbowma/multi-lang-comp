#lang racket/base

(require
 redex/reduction-semantics
 "lambda-b.rkt"
 "al.rkt")

(provide (all-defined-out))

; Design pattern for a multi-language with syntactic distinction between source
; and target, but also a combined syntax.
(define-union-language tagCGL (S. λbL) (T. aL))
(define-union-language mergeCGL λbL aL)
(define-union-language preCGL mergeCGL tagCGL)

(define-extended-language CGL preCGL
  #;[e ::= .... p]
  [T ::= hole
     (begin T.e ... T e ...)
     (with-label label T)]
  [C ::= T])

(define-metafunction CGL
  [(subst-all () () any) any]
  [(subst-all (r_1 r ...) (x_1 x ...) any)
   (subst-all (r ...) (x ...) (substitute any x_1 r_1))])

(define cg->
  (reduction-relation
   CGL
;   #:domain e
;   #:codomain e

   (--> (with-labels ([x_f (λ (x_a ...) e)] ...)
          e_2)
        (begin
          (with-label main
            (begin
              (push halt)
              e_2))
          (with-label x_f
            (begin
              (pop r_a) ...
              (subst-all (r_a ...) (x_a ...) e)
              #;(let ([rx ])
                (begin
                  (pop r)
                  (push rx)
                  (jump r)))))
          ...)
        #;(fresh ((r_a ...) ((x_a ...) ...)))
        (where ((r_a ...) ...)
               ,(for/list ([ls (term ((x_a ...) ...))])
                  (for/list ([_ ls])
                    (gensym 'ra))))
        #;(fresh ((rx ...) (x_f ...)))
        #;(fresh ((r ...) (x_f ...)))
        (fresh main))
   (--> (let ([x (call e_l e ...)])
          e_2)
        (begin
          (push e) ...
          (push label_r)
          (set! r e_l)
          (jump r)
          (with-label label_r
            (begin
              (pop r)
              (substitute e_2 x r))))
        (fresh r))
   (--> (let ([x n] ...)
          e_2)
        (subst-all
         (r ...)
         (x ...)
         (begin
           (set! r n) ...
           e_2))
        (fresh ((r ...) (x ...))))
   ; Boolean prim
   (--> (let ([x (compare (flag e_1 e_2) e_t e_f)])
          e)
        (substitute
         (begin
          (compare (flag e_1 e_2)
                   (begin
                     (set! r e_t))
                   (begin
                     (set! r e_f)))
          e)
         x
         r)
        (fresh r))
   (-->
    (compare (flag e_1 e_2) e_t e_f)
    (begin
      (jump-if (flag e_1 e_2) label_1)
      (jump label_2)
      (with-label label_1 e_t)
      (with-label label_2 e_f))
    (fresh label_1)
    (fresh label_2))
   (-->
    (call e_l e ...)
    (begin
      (pop r)
      (push e) ...
      (push r)
      (set! rl e_l)
      (jump rl))
    (fresh r)
    (fresh rl))
   (--> n
        (begin
          (pop r)
          (set! rv n)
          (push rv)
          (jump r))
        (fresh r)
        (fresh rv))))

(define cg->+ (context-closure cg-> CGL C))

(current-cache-all? #t)

#;(module+ test
  (parameterize ([default-language SL])
    (test-->>
     cg->+
     #:equiv alpha-equivalent?
     (term b-eg)
     )))
