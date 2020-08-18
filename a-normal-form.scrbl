#lang scribble/acmart @acmsmall @nonacm @screen
@(require
  scriblib/footnote
  latex-utils/scribble/theorem
  latex-utils/scribble/utils
  "lambda-s.rkt"
  "lambda-a.rkt"
  "anf.rkt"
  "defs.rkt")

@title{A-normalization}
Our first pass translates to A-normal form (ANF) to make data flow explicit
in the syntax.
Most compiler correctness papers use CPS as this first pass@todo{cite f-to-tal,
perconti ahmed, pilsner?, kennedy?, ...}.
CPS has the advantage of making both control flow and data flow explicit in the
syntax.
ANF, meanwhile, leaves some aspects of control flow implicit, in particular the
call-and-return structure of non-tail function calls, and evaluation order.
We use ANF since there is already a presentation of ANF as a reduction relation,
namely, the A-reductions@todo{cite amr, flannegan}, which served as inspiration
for the present work and a good starting point.

We extend the A-reductions to support some Scheme-like imperative features, and
make explicit the multi-language nature of the reduction system that was
implicit in earlier presentations of the A-reductions.

@section{ANF Language}
@figure["fig:anf-syntax" @elem{@|anf-lang| Syntax}
  (render-language λaL #:nts '(v n e))
]

We specify the target language as essentially the source language but with the
syntax restricted to A-normal form.
This is defined in @Figure-ref{fig:anf-syntax}.
For simplicity, we abstract all primitive operations into @render-term[λaL n],
but still require each operator is applied to the correct number of operands.
@todo{Should move that to source}

ANF specifies a syntactic distinction between values @render-term[λaL v],
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

@figure["fig:anf-eval-syn" @elem{@|anf-lang| Evaluation Contexts}
  (render-language λaL-eval #:nts '(E v))
]
Since data flow is explicit in the syntax, we no longer need a complex
evaluation context to specify how to compute values from subexpressions.
Instead, we only need to choose the evaluation order of simple computations.
In @Figure-ref{fig:anf-lang-syn}, we define the evaluation context
@render-term[λaL-eval E], and a separate class of run-time values
@render-term[λaL-eval v].
@todo{That the run-time values are different is a flaw. Should only need labels, and then be able to eliminate pairs and lambdas as values. Instead, they get allocated in the store. This seems strange, but makes equality work better and reflects that pair is not truely a value in ANF but an operation that allocates.}
@note{We could eliminate the evaluation context entirely by removing multi-arity
@render-term[λaL let] and @render-term[λaL begin] from the language, but this
only obscures the fact that evaluation order---left-to-right,
call-by-value---must still be specified in ANF.
There's also no particular advantage to trying to simplify the evaluation
context.}

Note that, by contrast, the CPS translation would be responsible for encoding
control flow information, including evaluation order, in the syntax as and data
flow.
Using ANF offers a minor advantage to to implementing lazy languages, as the
compiler does not need to change the syntax in order to change evaluation
strategy.

@(require (only-in pict vc-append vl-append hc-append))
@figure["fig:anf-lang-red" @elem{@|anf-lang| Reduction}
  (render-reduction-relation
    (union-reduction-relations λa->composition λa->admin λa->bools)
    #:style 'horizontal)
]

The reduction system for @|anf-lang| is not significantly different from @|source-lang|.
We give the key rules in @Figure-ref{fig:anf-lang-red}.
The main differences are in the definition of the evaluation contexts, and in
the reduction rules for function calls and composition forms.
The composition forms @render-term[λaL letrec], @render-term[λaL let], and
@render-term[λaL begin] now only appear at the top-level and not under an
evaluation, as does @render-term[λaL if].

@figure["fig:anf-lang-hcomp" @elem{@|anf-lang| Heterogeneous Composition}
  (render-metafunction hcompose)
]

The definition of β-reduction is slightly complicated since substitution must
replace a value, the @render-term[λaL hole] of the evaluation context, by a
configuration @render-term[λaL e] from the body of the function.
This is not well-defined using standard substition in ANF (although it is in
monadic form), since it would not preserve the normal form.
Instead, we define a heterogeneous substitution metafunction @render-term[λaL
hcompose] in @Figure-ref{fig:anf-lang-hcomp}.
Note that this definition duplicates code in the branches of @render-term[λaL
if]; this is intentional in the specification of the ANF semantics, but we avoid
it by using join-point optimization during compilation to ANF.

@section{The @|source-lang|/@|anf-lang| multi-language}
@figure["fig:anf-multi-syn" @elem{@|anf-multi-lang| Syntax (excerpts)}
  (parameterize ([extend-language-show-union #t]
                 [extend-language-show-extended-order #t])
    (render-language ANFL #:nts '(T.e T.n T.v S.e e)))
]

Next we define the @|source-lang| + @|anf-lang| multi-language,
@|anf-multi-lang|.
We start by defining standard multi-language features, then present the unique
changes for modeling compilation as a multi-language semantics.

We define the standard multi-language syntax for @|anf-multi-lang| in
@Figure-ref{fig:anf-multi-syn}.
The syntax is defined essentially by merging the syntax of
@|source-lang| and @|anf-lang|.
First, we introduce tagged non-terminals: @render-term[ANFL S.e] for purely
source and @render-term[ANFL T.e] for purely target terms.
These are each extended with a boundary term: @render-term[ANFL (ST T.e)] for an
embedding of a target term in a source term ("Source on the outside, Target on
the inside"), and @render-term[ANFL (TS S.e)] for embedding a target term in a
source term ("Target on the outside, Source on the inside").
Then we define the multi-language expressions @render-term[ANFL e] as either a
source or target term.

@figure["fig:anf-boundary-red" @elem{@|anf-multi-lang| Boundary Reductions}
  (render-reduction-relation st-> #:style 'horizontal)
]

We also define the mostly standard boundary cancelation reductions in
@Figure-ref{fig:anf-boundary-red}.
We depart slightly by allowing reduction in arbitrary program contexts rather
than evaluation context, reflecting the fact that compilation happens for any
subterm rather than only those being evaluated.

@section{Multi-language A-reductions}
@;In this multi-language, we define reduction as applying any of the
@;@|source-lang| reductions to @render-term[ANFL S.e] redex, and any of the
@;@|anf-lang| reductions to any @render-term[ANFL T.e].
@;We also add the standard boundary cancelation reductions, defined in
@;@Figure-ref{fig:anf-boundary-ref}.
@;
@;In the terms of @todo{citet matthews2007}, this is similar to a natural embedding.
@;However, as our goal is compilation rather than interoperability, we give only a
@;single directly to the natural embedding: source terms can be translated to
@;target terms.
@figure["fig:a-red" @elem{The A-reductions}
  (render-reduction-relation anf-> #:style 'horizontal)
]

Now we can define the A-reductions, given in @Figure-ref{fig:a-red}.
The translation is defined over @render-term[ANFL S.e] expressions, that is,
source expressions in the multi-language.
The first rule reduces any term that happens to also be a target language
expression and wraps it in an @render-term[ANFL ST] boundary, embedding the
target expression properly.
This step was implicit in by the reflexive closure of the A-reductions in the
original presentation.
The rest follow the same pattern as the original reductions.
When a @render-term[ANFL let] expression appears in evaluation contexts, we
merge the code across the declaration (implicitly renaming if necessary).
Similarly with @render-term[ANFL letrec] and @render-term[ANFL begin].
We can also understand these as normalizing all commuting conversions.
For @render-term[ANFL if], we merge code across the branches of the
@render-term[ANFL if] expression.
Unlike @todo{flanagan1993}, we use the join-point optimization to prevent code
duplication.
When the @render-term[ANFL if] appears in non-tail position with respect to the
evaluation context, we introduce a join point, a local explicit continuationm
and call the join point in the branches.
When the @render-term[ANFL if] appears in tail position, we need not push the
evaluation context into the branches.
In turns out that this can only happen when the evaluation context is trivial.
Finally, when a (non-value) computation appears in evaluation position, and in a
non-bind context, we name the intermediate computation explicitly pass the value
to the evaluation context.

In addition to perform the standard A-reductions, we mark each language boundary
explicitly. After A-reducing a @render-term[ANFL let], for exameple, the
@render-term[ANFL let] itself is in the target language, so we use the
@render-term[ANFL ST] boundary to embed the now-target term it its source
context.
However, its subexpressions are still source expressions, so we embed them in
the now-target @render-term[ANFL let] using the @render-term[ANFL TS] boundary.
Note that this makes the subexpression appear in translation context, while the
@render-term[ANFL ST] boundary means the @render-term[ANFL let] itself does not
appear in translation context.

@;Typically, we would next define reduction in the multi-language system.
@;In the terms of @todo{citet matthews2007}, we would choose between a lump
@;embedding or a natural embedding, to define the interoperability semantics of
@;our multi-language system.

In a typical multi-language semantics, we might allow the multi-language
reductions to happen under either a source or target evaluation context.
However, our goal is compilation rather than interoperability.
We are not defining evaluation, but translation, so we design a more general
program context, which we call the translation context.

@;@figure["fig:anf-multi-trans-ctxt" @elem{@|anf-multi-lang| Translation Context}
@;  (parameterize ([extend-language-show-union #t]
@;                 [extend-language-show-extended-order #t])
@;    (render-language ANFL #:nts '(T)))
@;]

In @Figure-ref{fig:anf-trans-red}, we define a translation context
@render-term[ANFL T].
This is a program context, a subset of general program context, under which a
source term appears and should be translated into a target term.
The definition is complicated slightly by the particulars of ANF, and is simpler
in other translations.

A translation context is any non-evaluation target languge context
@render-term[ANFL T.Cm] appearing under a boundary @render-term[ANFL TS],
written @render-term[ANFL (TS T.Cm)].
This can further be nested in an arbitrary multi-language program context,
written @render-term[ANFL (in-hole C (TS T.Cm))].
The context @render-term[ANFL T.Cm] corresponds to any target language context in
which a valid program can be constructed by plugging a configuration into the
hole.
@todo{Formally defined in hte appdendix.}
@;  @(render-language λaL #:nts '(Cm))
The inner context must be restricted to a non-evaluation context because the
A-reduction manipulate the evaluation context, so the evaluation context must be
part of the redex.
The outer context is arbitrary, indicating that translation can proceed under
any context

@figure["fig:anf-trans-red" @elem{@|anf-multi-lang| Translation Reduction System}
  (hc-append 60
   (parameterize ([extend-language-show-union #t]
                  [extend-language-show-extended-order #t])
     (render-language ANFL #:nts '(T)))
   (with-paper-rewriters (render-judgment-form-rows anf->+j '(2))))
]
We define the translation reduction @(anf->+-arrow) in
@Figure-ref{fig:anf-trans-red}, which combines either an A-reduction in
translation context, or a boundary cancellation step.

To see how the translation-as-reduction works, consider the following example,
taken from @todo{cite flanagan1993}:
@(require
  (only-in redex/pict render-term/pretty-write)
  (only-in redex/reduction-semantics term))

@(require (for-syntax racket/base))
@(define-syntax (render-step stx)
   (syntax-case stx ()
     [(_ n e)
      #`(with-paper-rewriters
          (vl-append
           (render-term ANFL e)
           #,@(for/list ([i (in-range 1 (add1 (syntax-e #'n)))])
                #`(hc-append
                   (anf->+-arrow)
                   (with-paper-rewriters (render-term/pretty-write ANFL (step #,i (term e))))))))]))

@(define-syntax-rule (render-prefix-and-finish n e)
   (with-paper-rewriters
     (vl-append
      (render-step n e)
      (hc-append
       (anf->+-arrow)
      (with-paper-rewriters (render-term/pretty-write ANFL (car (apply-reduction-relation* anf->+ (term e)))))))))

@(render-prefix-and-finish 6 (TS (+ (+ 2 2) (let ([x 1]) (f 1)))))

We begin translation by embedding the source term in the multi-language in
translation context, using the @render-term[ANFL TS] boundary.
We contract the @render-term[ANFL let] redex, which adds the @render-term[ANFL
ST] boundary around the whole expression, and wraps the
subexpressions with the @render-term[ANFL TS] boundary.
The next redex we contract is boundary cancellation.
We proceed with another @render-term[ANFL let] redex, which merges the addition
into the body of the declaration.
Reduction continues until we reach ANF.

@(require rackunit)
@(check-exn values (lambda () (step 11 (term (TS (+ (+ 2 2) (let ([x 1]) (f 1))))))))
This example finishes in 3 steps in @todo{cite flanagan}, but takes 10 steps in
our multi-language presentation.
This is because we make explicit the translation of source values into target
values, and require extra boundary cancellation steps.
In fact, we take a few short-cuts by allowing an arbitrary target term to reduce
rather than reducing only target values, which would be more faithful for the
multi-language interoperability semantics of @todo{matthews2007}, but is not
really required for reduction as compiliation.

@(define-syntax-rule (render-anf-eg e)
   (nested #:style 'code-inset
     (para "Example:")
     (tabular #:row-properties '((top)) (list (list "> " (render-term λaL (step (TS e))))))
     (with-paper-rewriters (render-term/pretty-write λaL (term (compile-anf e))))))

We can define compilation as normalization with respect to the A-reductions and
boundary reductions.

@mdef["ANF Compilation by Normalization"]
@render-judgment-form[anf-compile]

@section{Compiler Correctness as Confluent Multi-Language Reduction}
The multi-language semantics allows us to define a reduction system in which
confluence is compiler correctness.
The intuition is simple.
We define a reduction system in which any embedded source term can either take a
step in the source semantics, or take a translation step.
Any target term can take a step in the target semantics.
Confluence tells us that if we take a source step, then translate, then reduce,
that's the same as translating then reducing, @ie confluence is forward
simulation.

@figure["fig:anf-multi-red" @elem{@|anf-multi-lang| Multi-language Reduction}]{
  @(with-paper-rewriters (render-judgment-form-rows anf-eval->+'(2 2 1)))
}
First we define the multi-language reduction system (@Figure-ref{fig:anf-multi-red}}).
The reduction system captures the the intution described above.
If we have a source term, and it takes a step in the source semantics, then it
takes a step in the multi-language reduction.
We extend source reduction to apply under a @render-term[ANFL TS] boundary,
essentially implementing the new @render-term[ANFL TS] evaluation context give
the standard multi-language semantics.
We analogous enable multi-language terms to reduce in the target semantics.
And finally, we enable a term to take a step translation step, either performing
an A-reduction or boundary cancellation step.
This system defines the single-step relation, and we take its reflexive
transitive closure to define the full multi-language evaluator.

Now we can define compiler correctness as confluence.

@mthm[@elem{Confluence} #:tag "thm:anf:confluence"]{
If @render-term[ANFL (anf-eval->* (S e) (S_1 e_1))] and
@render-term[ANFL (anf-eval->* (S e) (S_2 e_2))] then @exact{\\}
@render-term[ANFL (anf-eval->* (S_1 e_1) (S_3 e_3))] and
@render-term[ANFL (anf-eval->* (S_2 e_2) (S_3 e_3))]
}

@mcor[@elem{Whole-Program Correctness} #:tag "thm:anf:correct"]{
If
@render-term[ANFL (λi->j* (() S.e) (S S.v))] and
@render-term[ANFL (anf-compile S.e T.e)] then
@render-term[ANFL (λa->j* (() T.e) (S T.v))] such that
@render-term[ANFL T.v] is equal to
@render-term[ANFL S.v].
}
@tprf["Proof."]{
Note that @render-term[ANFL (λi->j* (() S.e) (S S.v))] implies
@render-term[ANFL (anf-eval->* (() S.e) (S S.v))].
Similarly, @render-term[ANFL (anf-eval->* (S S.e) (S T.e))].
By confluence, there must exist some @render-term[ANFL S_3] and
@render-term[ANFL e_3] such that
@render-term[ANFL (anf-eval->* (S S.v) (S_3 e_3))] and
@render-term[ANFL (anf-eval->* (S T.e) (S_3 e_3))].
Since values cannot step, we know @render-term[ANFL e_3] must be
@render-term[ANFL S.v].
Since values are shared across languages, we pick @render-term[ANFL T.v] to be
@render-term[ANFL S.v] and the goal is complete.
}

@;Unforunately, this may not save us much proof effort.
@;The single-step reduction is not confluent, since a transation step may need to
@;be followed by boundary cancelation before a target step can take place, so the
@;proof of confluence of the evaluate is non-trivial.
@;The simplest approach may be Takahashi's "universal common reduct", which
@;essentially forces us to define the compiler as a translation.

@section{Multi-Language Reduction as JIT Compilation}
The multi-language evaluator captures the semantics of JIT compilation: at any
point, a source expression can instead be translated to the target language,
after which time it runs in the target language semantics.
We could model speculative optimization as a simple @render-term[ANFL if]
expression: the term @render-term[ANFL (ST (if e_p (TS e) e))], where
@render-term[ANFL e_p] encodes the dynamic assumption under which the variant
@render-term[ANFL (TS e)] is executed.
Initially, this is just an embedded copy of the original unoptimized code.
However, the multi-language evaluator semantics allow us to compile it.

This is not a particularly realistic model of speculative execution.
In particular, it does not capture fine-grained composable assumptions, nor
deoptimization from models such as @todo{cite fluckiger}.
However, the approach is more general: many compiler translations are easily
modeled (as we show later) as multi-language semantics, and so we easily derive
a model of source-to-assembly JIT compiler.
Interesting future work would equip the multi-language semantics with better
semantics for speculative optimization.
