#lang scribble/acmart @acmsmall @nonacm @screen
@(require
   redex/pict
   "lambda-s.rkt"
   "defs.rkt")

@title{A-normal Form}
We start by presenting the source language and the ANF "translation".
Most compiler correctness papers use CPS at the first pass, but we use ANF since
there is already a presentation of ANF as a reduction relation.
We extend the A-reductions to support some Scheme-like imperative features.

@section{Source Language: @source-lang}

@(render-language λiL)
