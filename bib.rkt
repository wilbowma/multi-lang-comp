#lang racket/base

(require
 scriblib/autobib
 scriblib/bibtex
 scribble/html-properties
 scribble/latex-properties
 setup/main-collects
 scribble/core)

(provide
 (all-defined-out))

(define-cite acite acitet generate-bibliography)
(define-bibtex-cite* "wilbowma.bib" acite acitet ~cite citet)

#|
;; fixup issue with autobib when bibliography not generated
(define autobib-style-extras
  (let ([abs (lambda (s)
               (path->main-collects-relative
                (collection-file-path s "scriblib")))])
    (list
     (make-css-addition (abs "autobib.css"))
     (make-tex-addition (abs "autobib.tex")))))

(define-syntax-rule (~cite any ...)
  (make-element
   (make-style #f autobib-style-extras)
   (a~cite any ...)))

(define-syntax-rule (citet any ...)
  (make-element
   (make-style #f autobib-style-extras)
   (acitet any ...)))
|#
