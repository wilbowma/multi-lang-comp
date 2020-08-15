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
namely, the A-reductions@todo{cite amr, flannegan}, which served as inspiration
for the present work and a good starting point.

We extend the A-reductions to support some Scheme-like imperative features.
This is a contribution insofar as it has not appeared in published models,
although the reduction are probably known to compiler implementers.

@section{ANF Language}
@figure["fig:anf-syntax" @elem{@|anf-lang| Syntax}
  (render-language λaL #:nts '(V n e))
]

We specify the target language as essentially the source language but with the
syntax restricted to A-normal form.
This is defined in @Figure-ref{fig:anf-syntax}.

ANF specifies a syntactic distinction between values @render-term[λaL V],
computations @render-term[λaL n], and configurations @render-term[λaL e].
All elimination forms work directly on values rather than arbitrary expressions,
so control must be manually composed using @render-term[λaL let] and
@render-term[λaL begin].

We can consider ANF as normalized monadic form for the continuation monad.
The monad implements @render-term[λaL bind] as @render-term[λaL let] and
@render-term[λaL begin] and @render-term[λaL return] is implicit by the include
of @render-term[λaL V] in the operations of the monad @render-term[λaL n].
The form is normal with respect the following commuting conversion.
@(require redex/reduction-semantics)
@render-reduction-relation[
  (reduction-relation
    λaL
    (--> (bind ([x_1 (bind ([x_2 n_2]) e_2)]) e_1)
         (bind ([x_2 n_2]) (bind ([x_1 e_2]) e_1))))
  #:style 'horizontal
]

@section{Dynamic Semantics}
@figure["fig:anf-lang-red" @elem{@|anf-lang| Syntax}
  (render-reduction-relation λa->)
]
@figure["fig:anf-eval-syn" @elem{@|anf-lang| Evaluation Contexts}
  (render-language λaL-eval #:nts '(E v))
]
Since control and data flow are explicit in the syntax, we no longer need a
complex evaluation context to specify these.
Instead, we only need to choose evaluation order.
In @Figure-ref{fig:anf-lang-syn}, we define (a vastly simplified) evaluation
context @render-term[λaL-eval E], and a separate class of run-time values
@render-term[λaL-eval v].
@todo{That the run-time values are different is a flaw. Should only need labels, and then be able to eliminate pairs and lambdas are values. Instead, they get allocated in the store. This seems strange, but makes equality work better and reflects that pair is not truely a value in ANF but an operation that allocates.}
We could eliminate the evaluation context entirely by removing multi-arity
@render-term[λaL let] and @render-term[λaL begin] from the language, but this
only obscures the fact that evaluation order---left-to-right,
call-by-value---must still be specified in ANF.
There's also no particular advantage to trying to simplify the evaluation
context.

Note that, by contrast, the CPS translation would be responsible for encoding
evaluation order in the syntax as well as control and data flow.
This is a minor advantages of using ANF to implement lazy languages, as the
compiler does not need to change the syntax in order to change evaluation
strategy.

@section{The @|source-lang|/@|anf-lang| multi-language}
@(require
  (only-in redex/pict extend-language-show-union extend-language-show-extended-order))
@figure["fig:anf-multi-syn" @elem{@|anf-multi-lang| Syntax (excerpts)}
  (parameterize ([extend-language-show-union #t]
                 [extend-language-show-extended-order #t])
    (render-language ANFL #:nts '(T T.e T.n T.V S.e e)))
]

Next we define the @|source-lang| + @|anf-lang| multi-language,
@|anf-multi-lang|.
We define the syntax of the @|anf-multi-lang| in @Figure-ref{fig:anf-multi-syn}.
The syntax is defined essentially by merging the syntax of
@|source-lang| and @|anf-lang|.
First, we introduce tagged non-terminals: @render-term[ANFL S.e] for purely
source and @render-term[ANFL T.e] for purely target terms.
These are each extended with a boundary term: @render-term[ANFL (ST T.e)] for an
embedding of a target term in a source term (Source on the outside, Target on
the inside), and @render-term[ANFL (TS S.e)] for embedding a target term in a
source term (Target on the outside, Source on the inside).
Then we define the multi-language expressions @render-term[ANFL e] as either a
source or target term.

@figure["fig:anf-boundary-red" @elem{@|anf-lang| Boundary Reductions}
  (render-reduction-relation st->)
]
In this multi-language, we define reduction as applying any of the
@|source-lang| reductions to @render-term[ANFL S.e] redex, and any of the
@|anf-lang| reductions to any @render-term[ANFL T.e].
We also add the standard boundary cancelation reductions, defined in
@Figure-ref{fig:anf-boundary-ref}.

In the terms of @todo{citet matthews2007}, this is similar to a natural embedding.
However, as our goal is compilation rather than interoperability, we give only a
single directly to the natural embedding: source terms can be translated to
target terms.

@section{A-reductions}
@figure["fig:a-red" @elem{The A-reductions}
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
