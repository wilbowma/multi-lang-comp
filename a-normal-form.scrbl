#lang scribble/acmart @acmsmall @nonacm @screen
@(require
  "lambda-s.rkt"
  "lambda-a.rkt"
  "anf.rkt"
  "defs.rkt")

@title{A-normalization}
Our first pass translates to A-normal form (ANF) to make control flow explicit
in the syntax.
Most compiler correctness papers use CPS as this first pass@todo{cite f-to-tal,
perconti ahmed, pilsner?, kennedy?, ...}.
We use ANF since there is already a presentation of ANF as a reduction relation,
namely, the A-reductions@todo{cite amr, flannegan}.

We extend the A-reductions to support some Scheme-like imperative features.
This is a contribution insofar as it has not in published models, although the
reduction are probably known to compiler implementers.

As this is our first pass, we take care to carefully define the source/target
multi-language.
For brevity, we take some liberties in the presentation of future multi-language
pairs.

@section{ANF Language}
@figure["fig:anf-syntax" @~a{@|anf-lang| Syntax}
  (render-language λaL #:nts '(V n e))
]

We specify the target language as essentially the source language but with the
syntax restricted to A-normal form.
This is defined in @Figure-ref{fig:anf-syntax}.

ANF specifies a syntactic distinction between values @render-src[v],
computations @render-src[n], and configurations @render-src[e].
We can consider the form as a canonicalized monadic form for the continuation
monad, where @tt{bind} is implemented with @render-src[let] and
@render-src[begin] and all @tt{bind}s are left-associated, computations are
monadic operations, and @tt{return} is implicit.
All elimination forms work directly on values rather than arbitrary expressions,
so control must be manually composed using @render-src[let] and
@render-src[begin].
@todo{It's not canonical; begin can have nested expressions in it. Maybe you mean canonical w.r.t. a specific reduction?}

@section{Dynamic Semantics}
Since control flow is encoded in the syntax, the semantics are straight-forward
to implement as an abstract machine.
However, we continue to use (a vastly simplified) evaluation contexts.
This is primarily to enable support multi-arity @render-src[let] and
@render-src[begin]; the machine would be simpler with single-arity.
There's also no particular advantage to trying to accomplish this; ANF still
accomplishes its primary goal of simplifying translation into an assembly
language.
@todo{So why not simplify it? Add the reductions (let ([x n] [x_more n_more] ...) e) -> (let ([x n]) (let ([x_more n_more]) e)), (let () e) -> e, (begin e e_more ...) -> (begin e (begin e_more ...)), (begin) -> (void)}
We again implement the standard left-to-right call-by-value evaluation.

Note that unlike CPS, ANF does not make evaluation order explicit, so we could
still specify a call-by-name semantics in our reduction relation.
By contrast, the CPS translation would be responsible for encoding call-by-name
semantics, and the evaluation order of reduction relation would be irrelevant.
This is a minor advantages of using ANF to implement lazy languages, as the
compiler does not need to change in order to change evaluation strategy.

@todo{Is it evaluation order that is explicit and not control flow? Need to sort
that out.}

@section{A-reduction}
@figure["fig:a-red" @~a{The A-reductions}
  (render-reduction-relation anf-> #:style 'horizontal)
]

@(require (only-in redex/pict render-term/pretty-write) (only-in redex/reduction-semantics term))
@(define-syntax-rule (render-anf-eg e)
   (nested #:style 'code-inset
     (para "Example:")
     (tabular #:row-properties '((top)) (list (list "> " (render-term λaL e))))
     (with-paper-rewriters (render-term/pretty-write λaL (term (compile-anf e))))))


@render-anf-eg[
(letrec ([fact (λ (n)
                 (if (eq? n 0)
                     1
                     (* n (fact (- n 1)))))])
  (fact 5))
]
