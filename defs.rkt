#lang racket/base

(require
 retex
 redex/pict
 redex/reduction-semantics
 file/convertible
 racket/function
 pict
 (prefix-in pict: pict)
 (only-in rackunit require/expose)
 pict/convert
 racket/format
 racket/match
 (for-syntax
  racket/base
  syntax/parse)
 scribble/base
 retex
 "lambda-s.rkt"
 (only-in
  scribble/core
  link-render-style
  current-link-render-style)
 (only-in scriblib/figure [Figure-ref pre:Figure-ref])
 (except-in scriblib/figure Figure-ref)
 with-cache)

(require/expose pict/private/pict (converted-pict-parent converted-pict?))

(provide
 (all-from-out scriblib/figure)
 (rename-out
  [_render-metafunction render-metafunction]
  [_render-judgment-form render-judgment-form])
 render-judgment-form-rows
 render-mathpar-judgment
 extend-language-show-union
 union-reduction-relations
 reduction-relation
 extend-language-show-extended-order
 term
 (all-defined-out))

(define ie (emph "i.e."))

(*use-cache?* #f)
(define source-lang (elem "λ" (elem #:style 'superscript "S")))
(define anf-lang (elem "λ" (elem #:style 'superscript "A")))
(define anf-multi-lang (elem "λ" (elem #:style 'superscript "sa")))

(define todo margin-note)

(define (Figure-ref e)
  (pre:Figure-ref e #:link-render-style (link-render-style 'default)))

(define-syntax-rule (render-language e ...)
  (with-paper-rewriters (render-language-cache e ...)))

(define-syntax-rule (_render-metafunction e ...)
  (with-paper-rewriters (render-metafunction e ...)))

(define-syntax-rule (_render-judgment-form e ...)
  (with-paper-rewriters (render-judgment-form e ...)))

(define-syntax-rule (render-reduction-relation e ...)
  (with-paper-rewriters (render-reduction-relation-cache e ...)))

(define-syntax-rule (render-term e ...)
  (with-paper-rewriters (render-term-cache e ...)))

(define-syntax-rule (render-src e)
  (render-term λiL e))

(define (apply-reduction-relation-n red n e)
  (apply-reduction-relation*
   red
   e
   #:stop-when
   (let ([b (box 0)])
     (lambda (x)
       (begin
         (set-box! b (add1 (unbox b)))
         (> (unbox b) n))))))

(define-syntax (render-step stx)
  (syntax-case stx ()
    [(_ lang red arrow n e)
     #`(with-paper-rewriters
         (vl-append
          (render-term lang e)
          #,@(for/list ([i (in-range 1 (add1 (syntax-e #'n)))])
               #`(hc-append
                  (pad-arrow arrow)
                  (with-paper-rewriters
                    (render-term/pretty-write
                     lang
                     (car (apply-reduction-relation-n red #,i (term e)))))))))]))

(define-syntax-rule (render-prefix-and-finish lang red arrow n e)
  (with-paper-rewriters
    (vl-append
     (render-step lang red arrow n e)
     (hc-append
      (pad-arrow (star-arrow arrow))
      (with-paper-rewriters (render-term/pretty-write lang (car (apply-reduction-relation* red (term e)))))))))

#;(default-font-size 12)
#;(metafunction-font-size 10)
#;(label-font-size 9)

(define Linux-Liberterine-name "Linux Libertine O")
(define Inconsolata-name "Inconsolata")
#;(define LatinModernMath-Regular-name "Latin Modern Math")
(require racket/draw)
(define (check-font name)
  (unless (member name (get-face-list))
    (error 'check-font "expected the font ~a to be installed\n" name)))
(check-font Inconsolata-name)
(check-font Linux-Liberterine-name)
#;(check-font LatinModernMath-Regular-name)

#;(define math-style Linux-Liberterine-name)

#;(greek-style 'roman)
#;(upgreek-style 'roman)
#;(metafunction-style 'swiss)
#;(label-style 'swiss)
#;(default-style math-style)
#;(literal-style math-style)
#;(paren-style 'roman)
#;(grammar-style (cons 'italic 'roman))

(define (replace-font param)
  (let loop ([x (param)])
    (cond
      [(pair? x) (cons (car x) (loop (cdr x)))]
      [else Linux-Liberterine-name])))

(define (def-t str) (text str (default-style) (default-font-size)))
(define (mf-t str) (text str (metafunction-style) (metafunction-font-size)))
(define (nt-t str) (text str (non-terminal-style) (default-font-size)))
(define (nt-sub-t str) (text str (cons 'subscript (non-terminal-style)) (default-font-size)))
(define (literal-t str) (text str (literal-style) (default-font-size)))


(struct pict+tag (pict tag)
  #:property prop:pict-convertible
  (lambda (x) (pict+tag-pict x))
  #:property prop:convertible
  (lambda (v r d)
    (case r
      [(text) (pict+tag-tag v)]
      [else (convert (pict+tag-pict v) r d)])))

(define (compute-tag base ss)
  (define (to-string x)
    ((match x
       [(? string?) values]
       [(or (? number?) (? symbol?)) ~a]
       [(? lw?) (const "")]
       [(? pict+tag?) pict+tag-tag]
       [(? pict?) compute-tag2])
     x))
  (apply
   string-append
   (to-string base)
   (map to-string ss)))

(define (compute-tag2 p)
  (or (compute-tag2* p) ""))

(define (compute-tag2* p)
  (cond
    [(and (converted-pict? p)
          (pict+tag? (converted-pict-parent p)))
     (pict+tag-tag (converted-pict-parent p))]
    [else
     (let loop ([v #f]
                [l (pict-children p)])
       (cond
         [(null? l) v]
         [else
          (define x (compute-tag2 (child-pict (car l))))
          (define next
            (cond
              [(and x v)
               (string-append v x)]
              [else (or x v)]))
          (loop next (cdr l))]))]))

(define (lift-to-taggable pict tag)
  (if (pict+tag? pict)
      (pict+tag (pict+tag-pict pict) tag)
      (pict+tag pict tag)))

(define (text t f [s 12] #:kern? [kern? #t])
  (lift-to-taggable
   (if kern?
       (kern-text t f s)
       (pict:text t f s))
   t))

(define (kern-text t f s)
  (define split (breakout-manual-adjustment t))
  (apply hbl-append
         (for/list ([segement (in-list split)])
           (if (or (pict-convertible? segement) (pict? segement))
               segement
               (pict:text segement f s)))))

(define hookup
  (drop-below-ascent
   (text "⇀" Linux-Liberterine-name (default-font-size) #:kern? #f)
   2))
(define hookdown
  (drop-below-ascent
   (text "⇁" Linux-Liberterine-name (default-font-size)  #:kern? #f)
   2))
(define right
  (text "⟶" Linux-Liberterine-name (default-font-size)  #:kern? #f))

;; TODO Should be a parameter.
(define adjustment-table
  (hash
   #\⇀ hookup
   #\⇁ hookdown
   #\⟶ right))

(define (breakout-manual-adjustment t)
  (define (stringify x)
    (apply string (reverse x)))
  (for/fold ([current '()]
             [all '()]
             #:result (reverse (cons (stringify current) all)))
            ([c (in-string t)])
    (match (hash-ref adjustment-table c c)
      [(or (? pict-convertible? x) (? pict? x))
       (values '() (list* x (stringify current) all))]
      [(? char? c) (values (cons c current) all)])))

(define (words str)
  (text str (default-style) (default-font-size)))

#;(define (typeset-supers s)
  (render-word-sequence (blank) s +2/5))
#;(define (typeset-subs s)
  (render-word-sequence (blank) s -2/5))
#;(define (render-word-sequence base s l)
  (define p
    (for/fold ([p base])
              ([s (in-list s)])
      (hbl-append
       p
       (scale
        (cond [(string? s) (words s)]
              [(or (number? s) (symbol? s)) (words (~a s))]
              [(pict-convertible? s) s]
              [(lw? s) (render-lw (default-language) s)]
              [else (error 'render-op "don't know how to render ~v" s)])
        .7))))
  (lift-bottom-relative-to-baseline
   p
   (* l (pict-height p))))

(define (render-op p [x #f])
  (define s (~a (if x x p)))
  (define head
    (hbl-append
     (if x p (blank))
     (match (regexp-match* #rx"^[^^_]*" s)
       [(cons r _) (words r)]
       [_ (blank)])))
  (define tails (regexp-match* #rx"(_|\\^)[^^_]*" s))
  (render-op/instructions head tails))

(define (render-op/instructions base ss)
  (define-values (supers subs seq)
    (for/fold ([super '()]
               [sub '()]
               [seq '()]
               #:result (values (reverse super) (reverse sub) (reverse seq)))
              ([s (in-list ss)])
      (match s
        [(or (regexp #rx"\\^(.*)" (list _ r))
             (list 'superscript r))
         (values (cons r super) sub (cons r seq))]
        [(or (regexp #rx"_(.*)" (list _ r))
             (list 'subscript r))
         (values super (cons r sub) (cons r seq))])))
  (define the-super ""#;(typeset-supers supers))
  (define the-sub ""#;(typeset-subs subs))
  (lift-to-taggable
   (inset
    (refocus
     (hbl-append
      (refocus (hbl-append base the-sub) base)
      the-super)
     base)
    0
    0
    (max (pict-width the-sub) (pict-width the-super))
    0)
   (compute-tag base seq)))

(define (collapse-consecutive-spaces l)
  (match l
    [(or (list _) (list)) l]
    [(list* "" "" r)
     (collapse-consecutive-spaces (cons "" r))]
    [(cons a b)
     (cons a (collapse-consecutive-spaces b))]))

(define (binop op lws)
  (define left (list-ref lws 2))
  (define right (list-ref lws 3))
  (append (do-binop op left right)
          (list right "")))

(define (do-binop op left right [splice #f])
  (define space (text " " (default-style) (default-font-size)))
  (append (list  "")
          (if splice (list splice (just-after left splice)) (list left))
          (list
           (just-after
            (hbl-append
             space
             (if (pict-convertible? op) op (render-op op))
             space)
            left))
          (list "")))

(define (infix op lws)
  (define all (reverse (cdr (reverse (cdr (cdr lws))))))
  (collapse-consecutive-spaces
   (let loop ([all all])
     (match all
       [(list* x (and dots (struct* lw ([e (or '... "...")]))) y rst)
        (append (do-binop op dots y x) (list "")
                (loop (cons y rst)))]
       [(list* x (and dots (struct* lw ([e (or '... "...")]))) rst)
        (list x dots "")]
       [(list* x y rst)
        (append (do-binop op x y) (list "")
                (loop (cons y rst)))]
       [(list x) (list x "")]))))


(define (name-arrow name base [r 2] [t -3])
  (with-paper-rewriters
    (pin-over
     base
     r t
     (text name Linux-Liberterine-name 7))))

(define (star-arrow base)
  (hbl-append base (inset (def-t "*") -2 0 0 0)))

(define (λs->-arrow)
  (name-arrow "λs" (def-t "→")))

(define (λa->-arrow)
  (name-arrow "λa" (def-t "→")))

;; Rewriters!
(set-arrow-pict!
 '-->
 (lambda ()
   (with-paper-rewriters/proc
     (lambda ()
       (def-t "→")))))

(set-arrow-pict! '-->λs λs->-arrow)
(set-arrow-pict! '-->λa λs->-arrow)

(define (a->-arrow) (with-paper-rewriters (def-t "→ᵃ")))
(define (st->-arrow) (with-paper-rewriters (def-t "→ˢᵗ")))

(set-arrow-pict! '-->a a->-arrow)

(set-arrow-pict! '-->st st->-arrow)

(define (ANFL->-arrow)
  (name-arrow "λsa" (def-t "⇒") 1))

(define (ANFL->*-arrow)
  (with-paper-rewriters
    (star-arrow (ANFL->-arrow))))

(define (anf->+-arrow)
  (with-paper-rewriters (def-t "ˢ→ᵃ")))

(define (pad-arrow p)
  (hbl-append (def-t " ") p (def-t " ")))

(define (anf-compile-arrow)
  (with-paper-rewriters (def-t "⇓ᵃⁿᶠ")))

(define (with-paper-rewriters/proc thunk)
  (with-compound-rewriters
    (['≡
      (curry binop "≡")]
     ['not-equal?
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " ≢ ")
              (list-ref lws 3)
              ""))]
     ['substitute
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t "[")
              (list-ref lws 3)
              (def-t " := ")
              (list-ref lws 4)
              ""))]
     ['subst-all
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t "[")
              (list-ref lws 3)
              (def-t " := ")
              (list-ref lws 4)
              ""))]
     ['non-Cn?
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " ∉ ")
              (nt-t "T.Cn")))]
     ['non-Cm?
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " ∉ ")
              (nt-t "T.Cm")))]
     ['non-Tv?
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " ∉ ")
              (nt-t "T.Tv")))]
     ['non-boolean?
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " ∉ ")
              (nt-t "boolean")))]
     ['non-fixnum?
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " ∉ ")
              (nt-t "fixnum")))]
     ['non-false?
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " ≠ ")
              (literal-t "#f")))]
     ['non-fv?
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " ∉ ")
              (nt-t "fv")))]
     ['→
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " → ")
              (list-ref lws 3)
              ""))]
     ['λi->j
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (λs->-arrow))
              (list-ref lws 3)
              ""))]
     ['λi->j*
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (star-arrow (λs->-arrow)))
              (list-ref lws 3)
              ""))]
     ['λa->j
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (λa->-arrow))
              (list-ref lws 3)
              ""))]
     ['λa->j*
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (star-arrow (λa->-arrow)))
              (list-ref lws 3)
              ""))]
     ['anf->+j
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (anf->+-arrow))
              (list-ref lws 3)
              ""))]
     ['anf->*j
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (def-t " ˢ→ᵃ* ")
              (list-ref lws 3)
              ""))]
     ['anf->j
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (a->-arrow))
              (list-ref lws 3)
              ""))]
     ['st->j
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (st->-arrow))
              (list-ref lws 3)
              ""))]
     ['not-anf->+j
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (def-t "ˢ↛ᵃ"))
              ""))]
     ['anf-compile
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (anf-compile-arrow))
              (list-ref lws 3)
              ""))]
     ['anf-eval->+
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (ANFL->-arrow))
              (list-ref lws 3)
              ""))]
     ['anf-eval->*
      (λ (lws)
        (list ""
              (list-ref lws 2)
              (pad-arrow (ANFL->*-arrow))
              (list-ref lws 3)
              ""))]
     ['→*
        (λ (lws)
          (list ""
                (list-ref lws 4)
                (hbl-append (def-t " →")
                            (inset (def-t "*") -2 0 0 0)
                            (def-t " "))
                (list-ref lws 5)
                ""))]
     ['ANFL-types
      (λ (lws)
        (list ""
              (list-ref lws 2)
              " ⊢ "
              (list-ref lws 3)
              " : "
              (list-ref lws 4)))]
     ['λiL-types
      (λ (lws)
        (list ""
              (list-ref lws 2)
              " ⊢ "
              (list-ref lws 3)
              " : "
              (list-ref lws 4)))]
     ['λaL-types
      (λ (lws)
        (list ""
              (list-ref lws 2)
              " ⊢ "
              (list-ref lws 3)
              " : "
              (list-ref lws 4)))]
     )
    (with-atomic-rewriters
      (;; because · renders as {} for environment sets.
       ['dot (λ () (text "·" (default-style) (default-font-size)))]
       ;; render nat and mat as n and m for the proofs
       ['nat (λ () (text "n" (non-terminal-style) (default-font-size)))]
       ['hole (λ () (def-t "[·]"))])
      (begin
        (define owsb (white-square-bracket))
        (parameterize* ([default-font-size (get-the-font-size)]
                        [metafunction-font-size (get-the-font-size)]
                        [label-style Linux-Liberterine-name]
                        [grammar-style Linux-Liberterine-name]
                        [paren-style Linux-Liberterine-name]
                        [literal-style Linux-Liberterine-name]
                        [metafunction-style (cons 'bold Linux-Liberterine-name)
                                            #;(cons 'italic Linux-Liberterine-name)]
                        [non-terminal-style (cons 'italic
                                                  Linux-Liberterine-name)
                                            #;(cons 'bold Linux-Liberterine-name)]
                        [non-terminal-subscript-style (replace-font non-terminal-subscript-style)]
                        [non-terminal-superscript-style (replace-font non-terminal-superscript-style)]
                        [default-style Linux-Liberterine-name]
                        [white-square-bracket
                         (lambda (open?)
                           (let ([text (current-text)])
                             (define s (ghost (owsb open?)))
                             (refocus
                              (lbl-superimpose
                               (scale
                                (text (if open? "⟬" "⟭")
                                      (default-style)
                                      (default-font-size))
                                1.05)
                               s)
                              s)))])
          (thunk))))))

(define in-footnote? (make-parameter #f))
(define (get-the-font-size) (if (in-footnote?) 9 12))

(define-syntax-rule (-note . args)
  (parameterize ([in-footnote? #t])
    (note . args)))

(define-syntax with-paper-rewriters
  (syntax-parser
    [(_ e1 e ...)
     (quasisyntax/loc this-syntax
       (with-paper-rewriters/proc
         #,(syntax/loc this-syntax (λ () e1 e ...))))]))
