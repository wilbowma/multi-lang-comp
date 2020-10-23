#lang scribble/acmart @sigplan @nonacm @screen

@title{Compilation as Multi-Language Semantics}
@(require
  (only-in pict vc-append vl-append hc-append)
  "bib.rkt"
  scriblib/footnote
  latex-utils/scribble/theorem
  latex-utils/scribble/utils
  "lambda-s.rkt"
  "lambda-a.rkt"
  "anf.rkt"
  "defs.rkt")

@author[
#:orcid "0000-0002-6402-4840"
#:affiliation "University of British Columbia, CA"
#:email (email "wjb@williamjbowman.com")
]{William J. Bowman}

@;@abstract{
@;We design a compiler from a Scheme-like language to an x86-64-like assembly
@;language.
@;The compiler performs the A-normal-form translation, closure conversion, heap
@;allocation and representation specification, hoisting, and code generation.
@;The novelty in the design is that the compiler is not a translation between
@;languages, but a reduction relation in a multi-language semantics.
@;
@;Formalizing the compiler as a reduction system in a multi-language semantics
@;provides interesting semantic insights, presentation benefits, and
@;verification benefit.
@;Normalization of the cross-language redexes performs ahead-of-time (AOT)
@;compilation.
@;Evaluation in the multi-language models just-in-time (JIT) compilation.
@;Confluence of multi-language reduction implies compiler correctness.
@;Subject reduction of the multi-language reduction implies type-preservation of
@;the compiler.
@;The reduction systems compose easily, enabling simple vertical composition of
@;separate passes.
@;Horizontal composition (linking) is enabled easily by embedding in the
@;multi-language.
@;The multi-language semantics is already a starting point for certain approaches
@;to secure compilation, so this could simplify approaches to secure compilation
@;based on multi-language semantics.
@;}


@;
@; - Theorem 3 looks formatted weird, idk

@section{Extended Abstract}
Multi-language semantics were introduced as a syntactic method for modeling the
semantics of inter-language interopability@~cite{matthews2007}, but have been
applied to syntactic approaches to compiler correcntess and secure
compilation@~cite["ahmed2011" "perconti2014" "ahmed2015:snapl" "new2016a"
"patterson2017:linkingtypes"].
They are useful for modeling cross-language linking and secure compilation since
all terms can be syntactically embedded in a single language, rather than
requiring a separate semantic notion of interoperability.

However, multi-language semantics duplicate some effort.
The compiler is defined twice: once on open terms as a syntactic
translation, and once on closed terms as a multi-language boundary reduction.
The two definitions occasionally differ slightly@~cite["ahmed2011" "new2016a"].
One must also prove correspondances between the multi-language reduction and the
compiler, increasing validation effort.

Intsead, we can model the compiler as a reduction system (over open terms) in a
multi-language semantics, reducing duplication and providing interesting
semantic insights.
Normalization of the cross-language redexes performs ahead-of-time (AOT)
compilation; the normal form with respect to these redexes is a target language
term.
We can model just-in-time (JIT) compilation as nondeterministic evaluation in
the multi-language: a term can either step in the source, or translate then step
in the target.
Various compiler correctness theorems are implied by standard semantics results.
For example, confluence of multi-language reduction implies compositional
compiler correctness, and subject reduction implies type-preservation of the
compiler.

The semantics retains properties valued for compiler validation.
Reduction systems compose easily, ensuring vertical composition of
separate passes.
Strong horizontal composition is enabled easily by embedding in the
multi-language and syntactic linking.

@;In this talk, I'll describe part of a compiler from a Scheme-like language to an
@;x64-64-like language designed completely as a series of multi-language
@;semantics.
@;I'll focus on a single pass to describe the approach to designing a compiler as
@;multi-language reduction, and formalize several definitions derived from the
@;multi-language semantics.

@subsubsub*section{An example instance: Reduction to A-normal form}
@;@figure["fig:src-syntax" @elem{@|source-lang| Syntax}
@;  (render-language λiL #:nts '(e x tag-pred arith-op))
@;]

The approach generalalizes from high-level to low-level transformations of a
wide array of lanugage features.
We have developed a 5-pass model compiler from a Scheme-like language to an
x86-64-like language.
Below, we model one interesting compiler pass: reduction to A-normal form (ANF).
This pass is particularly interesting, since its reduction rules must
manipulate the context.

The source is a standard dynamically typed functional imperative language,
modeled on Scheme.
It has a standard call-by-value heap-based small-step semantics,
@render-term[ANFL (λi->j (H S.e_1) (H S.e_2))], where @render-term[ANFL H]
represents the heap and @render-term[ANFL S.e] is represents a source
expression.@note{
We use a prefix followed by a dot (.) to distinguish terms in each language.
The prefix @emph{S} a source term and the prefix @emph{A} ANF intermediate
language term.
}
We omit the syntax and reduction rules for brevity.

@;@figure["fig:anf-syntax" @elem{@|anf-lang| Syntax}
@;  (render-language λaL #:nts '(v n e))
@;  (render-language λaL-eval #:nts '(E v))
@;]

The target language is essentially the same, but the syntax is restricted to
A-normal form: all elimination forms (meta-variable @render-term[ANFL A.n]) work
directly on values @render-term[ANFL A.v], expressions @render-term[ANFL A.e]
cannot be nested but instead sub-expressions must be manually bound to names
similar to monadic form.
The reduction relation, written @render-term[ANFL (λa->j (H A.e_1) (H A.e_2))],
takes advantage of this restriction and requires fewer congruence rules.
Viewed as an abstract machine, the reduction relation no longer requries a
computation stack as this is now encoded in the syntax.

@figure["fig:anf-multi-syn" @elem{@|anf-multi-lang| Syntax (excerpts)}
  (parameterize ([extend-language-show-union #t]
                 [extend-language-show-extended-order #t])
    (render-language ANFL #:nts '(A.e A.n A.v S.e e)))
]

To develop a multi-language semantics, we embed syntactic terms from each
language into a single syntax, defined in @Figure-ref{fig:anf-multi-syn}.
We extend each meta-variable with boundary terms @render-term[ANFL (SA A.e)]
("Source on the outside, ANF on the inside") and @render-term[ANFL (AS S.e)]
("ANF on the outside, Source on the inside").

@(require (only-in redex/pict render-reduction-relation-rules))
@figure["fig:a-red" @elem{The A-reductions (excerpts)}
  (parameterize ([render-reduction-relation-rules '("A-normal" "A-merge_l" "A-merge_b" "A-join" "A-lift")])
    (render-reduction-relation anf-> #:style 'compact-vertical))
]
The translation to ANF can be viewed as a reduction system in the multi-language.
In fact, the original presentation of ANF was as a reduction system, and this is
where A-normal form derives its name---the normal form with respect to the
A-reductions@~cite{flanagan1993}.
We define the A-reduction in @Figure-ref{fig:a-red}.
These are essentially standard, but we modify them to make boundary transitions
explicit.
The A-reductions have the form @render-term[ANFL (anf->j S.e S.e)], reducing
source expressions in the multi-language.
A-normal form corresponds to a @render-term[ANFL SA] boundary around a purely
ANF expression, with no boundary terms as subexpressions.
Each A-reduction rewrites a source expression in a source evaluation context,
rewriting the term to make evaluation order explicit.
We deviate from the standard presentation by making explicit boundary
transition.
For example, the A-lift rule lifts a trivial computation, let-binding it and
providing the let-bound name (a value) in evaluation position, explicitly
sequencing the computation @render-term[ANFL A.n] with the evaluation context
@render-term[ANFL S.E].
The side-conditions syntactically encode termination conditions, preventing
A-reductions in certain empty or trivial evaluation contexts.

@figure["fig:anf-boundary-red" @elem{@|anf-multi-lang| Boundary Reductions}
  (render-reduction-relation st-> #:style 'horizontal)
]

We supplement the multi-language A-reductions with the standard boundary
cancellation reductions, given in @Figure-ref{fig:anf-boundary-red}.
These apply under any multi-language context @render-term[ANFL C].


@figure["fig:anf-trans-red" @elem{@|anf-multi-lang| Translation Reduction System}
  (hc-append 60
   (parameterize ([extend-language-show-union #t]
                  [extend-language-show-extended-order #t])
     (render-language ANFL #:nts '(T)))
   (with-paper-rewriters (render-judgment-form-rows anf->+j '(2))))
]

In @Figure-ref{fig:anf-trans-red} we define the translation reduction system.
This extends the A-reduction to apply under any translation context
@render-term[ANFL T].
This construction of the translation context for ANF is a little unusual, but
the intuition is simple: a translation context identifies a pure source
expression under any context, including under a target/source boundary.
The context @render-term[ANFL A.Cm] corresponds to an ANF context that can have
any expression in the hole.
In one step, the translation reduction system can perform either one A-reduction
or one boundary cancellation.

From the translation reduction, we can derive ahead-of-time (AOT) compilation as
normalization with respect to translation reductions.
@mdef["ANF Compilation by Normalization"]
@render-judgment-form[anf-compile]

@figure["fig:anf-multi-red" @elem{@|anf-multi-lang| Multi-language Reduction}]{
  @(with-paper-rewriters (render-judgment-form-rows anf-eval->+'(2 2 1)))
}

Finally, we define the multi-language semantics in
@Figure-ref{fig:anf-multi-red}.
This defines all possible transitions in the multi-language.
A term can either take a step in the source language, or a step in the
translation reduction, or a step in the target language.
The multi-language reduction is indexed by a heap, @render-term[ANFL H], which
is used by the the source and target reduction semantics but not the translation
reductions.

Note that terms already in the heap are not translated, which corresponds to an
assumption that the language memory models are identical.
We could lift this restriction by extending translation reduction to apply in
the heap, which significantly complicates the semantics.

We can intuitively understand how the multi-language semantics models
just-in-time (JIT) compilation.
The definition allows running an interpreter (reducing in the source), or
JIT compilation (translation then reducing in the target).
This does not model speculative optimization; equipping the source with
assumption instructions as done by @citet{flueckiger2018:jit} might support
modeling this.

We derive compiler correctness from confluence.

@mthm[@elem{Confluence} #:tag "thm:anf:confluence"]{
If @render-term[ANFL (anf-eval->* (H e) (H_1 e_1))] and
@render-term[ANFL (anf-eval->* (H e) (H_2 e_2))] then
@render-term[ANFL (anf-eval->* (H_1 e_1) (H_3 e_3))] and
@render-term[ANFL (anf-eval->* (H_2 e_2) (H_3 e_3))]
}

Note the multi-language semantics can reduce open terms, so confluence implies
both compositional correctness of the AOT and JIT compilers.
As an example, whole-program correctness is a trivial corollary.

@mcor[@elem{Whole-Program Correctness} #:tag "thm:anf:correct"]{
If
@render-term[ANFL (λi->j* (() S.e) (H S.v))] and
@render-term[ANFL (anf-compile S.e A.e)] then
@render-term[ANFL (λa->j* (() A.e) (H A.v))] such that
@render-term[ANFL A.v] is equal to
@render-term[ANFL S.v].
}

Similarly, subject reduction of the multi-language semantics implies
type-preservation of the compiler.
This is not very interesting for our present compiler, since the type system is
simple, but the same idea applies to languages with more complex type systems.

@mthm[@elem{Subject Reduction implies Type Preservation} #:tag "thm:type-pres-type-pres"]{
If (@render-term[ANFL (ANFL-types Γ e_1 τ)] and @render-term[ANFL (anf->*j e_1 e_2)]
implies @render-term[ANFL (ANFL-types Γ e_2 τ)]) then
if (@render-term[ANFL (λiL-types S.Γ S.e S.τ)] and @render-term[ANFL (anf-compile S.e A.e)] then
∃@render-term[ANFL A.Γ],@render-term[ANFL A.τ].
@render-term[ANFL (λaL-types A.Γ A.e A.τ)]).
}

@(generate-bibliography)
