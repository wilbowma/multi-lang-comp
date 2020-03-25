#lang racket/base
(require
 redex/reduction-semantics)

(provide (all-defined-out))

; λbL is the bit-specified λ-calculus.
(define-language λbL
  [p ::= (with-labels ([x (λ (x ...) e)] ...)
           p)
     e]
  [e ::= (call e e ...)
     x
     (begin e ... e)
     (alloc e tag)
     (immediate number tag) ; TODO restrict range
     (word number)
     (mref e e)
     (mset! e e e)
     (+ e e) (- e e) (* e e)
     (let ([x e] ...) e)
     (compare (flag e e) e e)
     (compare (tag-eq? e tag) e e)
     ]
  [flag ::= eq? <]
  ; TODO: Can't use 'bool?
  [tag ::= 'bool 'pair 'box 'void 'empty 'fixnum 'procedure]
  [x ::= variable-not-otherwise-mentioned]
  #:binding-forms
  (λ (x ...) e #:refers-to (shadow x ...))

  (with-labels ([x any_1] ...) #:refers-to (shadow x ...)
          e_2 #:refers-to (shadow x ...))

  (let ([x e_1] ...) e_2 #:refers-to (shadow x ...)))

(define-term b-eg
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
                        (mref x (word 0)))))))))))))
  )
