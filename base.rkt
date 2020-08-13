#lang racket/base

(require
 redex/reduction-semantics
 racket/dict)

(provide (all-defined-out))

(define-language baseL
  [fixnum ::= integer]
  [arith-op ::= + - * / <]
  [binop ::= arith-op eq?]
  [tag-pred ::= pair? fixnum? boolean?]
  [env ::= any] ; must be a dict
  [x ::= variable-not-otherwise-mentioned]

  [l ::= (variable-prefix lb)]

  [primop ::= void binop tag-pred pair first second box unbox set-box!]
  )

(require racket/syntax)
(define (fresh-prefixed-variable-maker prefix)
  (let ([x (box 0)])
    (lambda ([name ""])
      (set-box! x (add1 (unbox x)))
      (format-symbol "~a~a~a" prefix name (unbox x)))))

(define-metafunction baseL
  fresh-labels : x ... -> (l ...)
  [(fresh-labels x ...)
   ,(map fresh-label (term (x ...)))])

(define fresh-label (fresh-prefixed-variable-maker 'lb))

(define (int61? x) (<= (min-int 61) x (max-int 61)))
(define (max-int word-size) (sub1 (expt 2 (sub1 word-size))))
(define (min-int word-size) (* -1 (expt 2 (sub1 word-size))))

(define-metafunction baseL
  [(subst-all () () any) any]
  [(subst-all (x_1 x ...) (any_1 any_more ...) any)
   (subst-all (x ...) (any_more ...) (substitute any x_1 any_1))])

(define-metafunction baseL
  env-extend : env (l any) ... -> env
  [(env-extend env (l any) ...)
   ,(append (term env) (term ((l . any) ...)))])

(define-metafunction baseL
  env-ref : env l -> any
  [(env-ref env l)
   ,(dict-ref (term env) (term l))])

(define (fixnum-error? v)
  (not (redex-match? baseL fixnum v)))

(define-metafunction baseL
  non-fixnum? : any -> boolean
  [(non-fixnum? any)
   ,(fixnum-error? (term any))])

; For some reason, eval wouldn't work. *shrug*.
(define (arith-op->proc v)
  (case v
    [(-) -]
    [(+) +]
    [(*) *]
    [(/) /]
    [(<) <]))

(define-metafunction baseL
  denote : arith-op fixnum ... -> fixnum
  [(denote arith-op fixnum ...)
   ,(apply (arith-op->proc (term arith-op)) (term (fixnum ...)))])

(define (boolean-error? v)
  (not (redex-match? baseL boolean v)))
