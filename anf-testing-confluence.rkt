#lang racket/base

(require
 redex/reduction-semantics
 "anf.rkt"
 redex/gui)

;; Confluence fixed!
;(stepper anf->+ (term (AS (let ([x (let ([y true]) y)]) x))))

;(stepper anf->+ (term (AS (let ([x true]) x))))
;(stepper anf->+ (term (AS (let ([x (+ 1 2)]) x))))

;(stepper anf->+ (term (AS (let ([x (SA (AS (let ([y true]) y)))]) x))))

;(stepper anf->+ (term (AS (let ([x (begin (set! y true) y)]) x))))

;\not->

;; invalid, since merge-l only applies to a term without an empty evaluation
;; context; we're forced to focus on the begin in evaluation position, first.
(stepper anf->+ (term (AS (SA (let ([x (AS (begin (set! y true) y))]) x)))))

;(stepper anf->+ (term (AS (+ (if (let ([x #t]) x) 6 7) 1))))

;; Is this a valid T[p]? No; translation context cannot have any boundaries,
;; except the AS boundary. Definition of C (A.Cv) doesn't have any boundary
;; terms with a context or hole under them.

; (SA (let ([x (AS (SA (AS e1)))])
;       (AS e2)))

#|
(in-hole (SA (let ([x e]) (AS hole)))
         e2)

C = (SA (let ([x e]) hole)) ; <- invalid C
T = (AS hole)
p = e2

(in-hole (SA (let ([x e]) (AS hole)))
         e2)

(let ([x (AS (SA (AS e1)))])
   (AS e2))

C = (let ([x e]) hole) ; <- valid C
T = (AS hole)
p = e2


C = (let ([x hole]) (AS hole)) ; <- valid C
T = (AS hole)
p = (SA (AS e1))

|#
