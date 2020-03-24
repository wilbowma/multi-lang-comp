#lang racket/base

(require
 redex/reduction-semantics
 "lambda-s.rkt"
 "anf.rkt"
 "cc.rkt"
 "hoist.rkt"
 "specify.rkt"
 "code-gen.rkt"
 "al.rkt")

;(define-union-language CompileL ANFL CCL)
;
;(define anf-compile-> (extend-reduction-relation anf-> CompileL))
;(define cc-compile-> (extend-reduction-relation cc-> CompileL))
;
;(define compile-> (union-reduction-relations anf-compile-> cc-compile->))
;
;(define anf-compile->+ (extend-reduction-relation anf->+ CompileL))
;(define cc-compile->+ (extend-reduction-relation cc->+ CompileL))
;
;(define compile->+ (union-reduction-relations anf-compile->+ cc-compile->+))

(current-cache-all? #t)
(define (compile t)
  (for/fold ([t t])
            ([pass (list anf->+ cc->+ h-> s->+ cg->+ #;flatten->+)])
    (car (apply-reduction-relation* pass t))))
