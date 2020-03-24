#lang racket/base

(require
 redex/reduction-semantics
 "lambda-h.rkt"
 "lambda-b.rkt")

(provide (all-defined-out))

; Design pattern for a multi-language with syntactic distinction between source
; and target, but also a combined syntax.
(define-union-language tagSL (S. λhL) (T. λbL))
(define-union-language mergeSL λhL λbL)
(define-union-language preSL mergeSL tagSL)

(define-extended-language SL preSL
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
     (kw T.e ... T e ...)
     (let ([T.x_1 T.e]
           ...
           [x_i T]
           [x_n e] ...)
       e)
     (let ([T.x_1 T.e] ...)
       T)
     (alloc T tag)
     (compare (tag-eq? T tag) e ...)
     (compare (tag-eq? T.e tag) T.e ... T e ...)
     (compare (flag T.e ... T e ...) e ...)
     (compare (flag T.e ...) T.e ... T e ...)]
  [kw ::= begin + - * mref mset! call]

  ; Spec, but slow
  #;[C ::= (compatible-closure-context e) (compatible-closure-context p #:wrt e)]
  [C ::= T])

(define s->
  (reduction-relation
   SL
   #:domain p
   #:codomain p

   (--> (cletrec ([x (closure e ...)] ...)
                 e_2)
        (let ([s (word e_size)] ...)
          (let ([x (alloc s 'procedure)] ...)
            (begin
              (begin e_set ...)
              ...
              e_2)))
        (fresh ((s ...) (x ...)))
        (where (e_size ...) ,(map length (term ((e ...) ...))))
        (where ((e_index ...) ...)
               ,(for/list ([size (term (e_size ...))])
                  (build-list size values)))
        (where ((e_set ...) ...)
               ,(for/list ([x (term (x ...))]
                           [ils (term ((e_index ...) ...))]
                           [els (term ((e ...) ...))])
                  (for/list ([index ils]
                             [e els])
                    (term (mset! ,x (word ,index) ,e))))))
   (--> (closure-ref e_b e_i) (mref e_b e_i))
   (--> (apply-closure e e_a ...)
        (call (mref e (word 0)) e_a ...))
   (--> (procedure? e)
        (compare (tag-eq? e 'procedure) #t #f))

   (-->
    (box e)
    (let ([x (alloc (word 1) 'box)])
      (begin
        (mset! x (word 0) e)
        x))
    (fresh x))
   (-->
    (set-box! e_1 e_2)
    (mset! e_1 (word 0) e_2))
   (-->
    (unbox e)
    (mref e (word 0)))
   (-->
    (box? e)
    (compare (tag-eq? e 'box) #t #f))

   (--> #f (immediate 0 'bool))
   (--> #t (immediate 1 'bool))
   (--> (if e_1 e_2 e_3)
        (compare (eq? e_1 #f) e_3 e_2))
   (--> (eq? e_1 e_2)
        (compare (eq? e_1 e_2) #t #f))
   (--> (boolean? e)
        (compare (tag-eq? e 'bool) #t #f))

   (--> number (immediate number 'fixnum))
   (--> (fixnum? e)
        (compare (tag-eq? e 'fixnum) #t #f))

   (--> (void) (immediate 0 'void))
   (--> (void? e)
        (compare (tag-eq? e 'void) #t #f))

   (--> '() (immediate 0 'empty))
   (--> (empty? e)
        (compare (tag-eq? e 'empty) #t #f))

   (--> (cons e_1 e_2)
        (let ([x (alloc (word 2) 'pair)])
          (begin
            (mset! x (word 0) e_1)
            (mset! x (word 1) e_2)
            x)))
   (--> (car e_1) (mref e_1 (word 0)))
   (--> (cdr e_1) (mref e_1 (word 1)))
   (--> (pair? e)
        (compare (tag-eq? e 'pair) #t #f))


   ;; Commuting conversions
   ;; Since we're in ANF, we can either go the F-to-TAL route and explicitly
   ;; manage declarations.. or just have separate commuting conversions,
   ;; which are easier to specify, and let normalization take care of it.
   (--> (let ([x_1 (let ([x_2 e_2]) e_1)])
          e)
        (let ([x_2 e_2])
          (let ([x_1 e_1])
            e)))

   (--> (let ([x_1 (begin e_s ... e_1)])
          e)

        (begin e_s ...
               (let ([x_1 e_1])
                 e)))))

#|
(compare (flag e_1 e_2) e_t e_f)
-->
(begin (jmp-if flag l_t) (jmp l_f) (with-label l_t e_t) (with-label l_f e_f))


(in-hole nontail (call l e ...))
-->
(begin (push e) ... (push return) (jump l) (with-label return (pop x)) (in-hole nontail x))
|#
(define s->+ (context-closure s-> SL C))

(current-cache-all? #t)

(module+ test
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
        (let ((x1 (alloc (word 1) 'box)))
          (begin
            (mset! x1 (word 0) (immediate 0 'fixnum))
            (let ((x x1))
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
                            (mref x (word 0)))))))))))))))))
