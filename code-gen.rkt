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
     s->+
     #:equiv alpha-equivalent?
     (term h-eg)
     (term
      (with-labels
        ((factL
          (λ (c n)
            (let ((fact (mref c (immediate 0 'fixnum))))
              (compare
               (eq?
                (compare
                 (eq? n (immediate 0 'fixnum))
                 (immediate 1 'bool)
                 (immediate 0 'bool))
                (immediate 0 'bool))
               (*
                n
                (call
                 (mref fact (word 0))
                 fact
                 (- n (immediate 1 'fixnum))))
               (immediate 1 'fixnum)))))
         (even?L
          (λ (c n)
            (let ((odd? (mref c (immediate 0 'fixnum))))
              (compare
               (eq?
                (compare
                 (eq? n (immediate 0 'fixnum))
                 (immediate 1 'bool)
                 (immediate 0 'bool))
                (immediate 0 'bool))
               (call
                (mref odd? (word 0))
                odd?
                (- n (immediate 1 'fixnum)))
               (immediate 1 'bool)))))
         (odd?L
          (λ (c n)
            (let ((even? (mref c (immediate 0 'fixnum))))
              (compare
               (eq?
                (compare
                 (eq? n (immediate 0 'fixnum))
                 (immediate 1 'bool)
                 (immediate 0 'bool))
                (immediate 0 'bool))
               (call
                (mref even? (word 0))
                even?
                (- n (immediate 1 'fixnum)))
               (immediate 0 'bool)))))
         (lengthL
          (λ (c x)
            (let ((length (mref c (immediate 0 'fixnum))))
              (let ((s (word 1)))
                (let ((empty?«4487» (alloc s 'procedure)))
                  (begin
                    (begin
                      (mset! empty?«4487» (word 0) empty?L))
                    (compare
                     (eq?
                      (compare
                       (tag-eq? x 'pair)
                       (immediate 1 'bool)
                       (immediate 0 'bool))
                      (immediate 0 'bool))
                     (immediate -1 'fixnum)
                     (compare
                      (eq?
                       (call
                        (mref empty?«4487» (word 0))
                        empty?«4487»
                        x)
                       (immediate 0 'bool))
                      (+
                       (immediate 1 'fixnum)
                       (call
                        (mref length (word 0))
                        length
                        (mref x (word 1))))
                      (immediate 0 'fixnum)))))))))
         (empty?L
          (λ (c x)
            (let ()
              (compare
               (eq? x (immediate 0 'empty))
               (immediate 1 'bool)
               (immediate 0 'bool))))))
        (let ((x
               (let ((x1 (alloc (word 1) 'box)))
                 (begin
                   (mset! x1 (word 0) (immediate 0 'fixnum))
                   x1))))
          (let ((s1 (word 2)))
            (let ((fact«8489» (alloc s1 'procedure)))
              (begin
                (begin
                  (mset! fact«8489» (word 0) factL)
                  (mset! fact«8489» (word 1) fact«8489»))
                (let ((s2 (word 2)) (s3 (word 2)))
                  (let ((even?«8742» (alloc s2 'procedure))
                        (odd?«8743» (alloc s3 'procedure)))
                    (begin
                      (begin
                        (mset! even?«8742» (word 0) even?L)
                        (mset! even?«8742» (word 1) odd?«8743»))
                      (begin
                        (mset! odd?«8743» (word 0) odd?L)
                        (mset! odd?«8743» (word 1) even?«8742»))
                      (begin
                        (compare
                         (eq?
                          (call
                           (mref even?«8742» (word 0))
                           even?«8742»
                           (call
                            (mref fact«8489» (word 0))
                            fact«8489»
                            (immediate 5 'fixnum)))
                          (immediate 0 'bool))
                         (mset!
                          x
                          (word 0)
                          (let ((x (alloc (word 2) 'pair)))
                            (begin
                              (mset!
                               x
                               (word 0)
                               (immediate 2 'fixnum))
                              (mset!
                               x
                               (word 1)
                               (immediate 0 'empty))
                              x)))
                         (let ((s4 (word 2)))
                           (let ((length«12165»
                                         (alloc s4 'procedure)))
                             (begin
                               (begin
                                 (mset!
                                  length«12165»
                                  (word 0)
                                  lengthL)
                                 (mset!
                                  length«12165»
                                  (word 1)
                                  length«12165»))
                               (mset!
                                x
                                (word 0)
                                (call
                                 (mref length«12165» (word 0))
                                 length«12165»
                                 (let ((x
                                        (alloc (word 2) 'pair)))
                                   (begin
                                     (mset!
                                      x
                                      (word 0)
                                      (immediate 1 'fixnum))
                                     (mset!
                                      x
                                      (word 1)
                                      (immediate 0 'empty))
                                     x))))))))
                        (mref x (word 0)))))))))))))))
