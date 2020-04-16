#lang scribble/acmart @acmsmall @nonacm @screen
@(require
   "lambda-s.rkt"
   "defs.rkt")

@title{A-normalization}
Most compiler correctness papers use CPS as the first pass@todo{...}, but we use
ANF since there is already a presentation of ANF as a reduction relation.
We extend the A-reductions to support some Scheme-like imperative features.
