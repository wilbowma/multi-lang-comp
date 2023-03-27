#lang scribble/acmart @sigplan @nonacm @screen @review

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
#:affiliation
@affiliation[
#:institution "University of British Columbia"
#:city "Vancouver"
#:state "BC"
#:country "CA"
]
#:email (email "wjb@williamjbowman.com")
]{William J. Bowman}

@;{abstract
Modeling interoperability between programs in different languages is a key
problem when modeling compositional and secure compilation, which has been
successfully addressed using multi-language semantics.
Unfortunately, existing models of compilation using multi-language semantics
define two variants of each compiler pass are defined: a syntactic translation
on open terms, and a run-time translation of closed terms at multi-language
boundaries

We introduce a novel work-in-progress approach to uniformly model a compiler
entirely as a reduction system on open term in a multi-language semantics,
rather than as a syntactic translation.
This simultaneously defines the compiler and the interoperability semantics,
reducing duplication.
It also provides interesting semantic insights.
Normalization of the cross-language redexes performs ahead-of-time (AOT)
compilation.
Evaluation in the multi-language models just-in-time (JIT) compilation.
Confluence of multi-language reduction implies compiler correctness.
Subject reduction of the multi-language reduction implies type-preservation of
the compiler.
This model provides a strong attacker model through contextual equivalence,
retaining its usefulness for modeling secure compilation as full abstraction.
}

@section{Extended Abstract}
Modeling interoperability between programs in different languages is a key
problem when modeling compositional and secure compilation.
Multi-language semantics provide a syntactic method for modeling language
interopability@~cite{matthews2007}, and has proven useful in compiler
correctness and secure compilation@~cite["ahmed2011" "perconti2014"
"ahmed2015:snapl" "new2016" "patterson2017:linkingtypes"].

Unfortunately, existing models of compilation using multi-language semantics
duplicate effort.
Two variants of each compiler pass are defined: a syntactic translation on open
terms, and a run-time translation of closed terms at multi-language
boundaries@~cite["ahmed2011" "new2016"].
One must then prove that both definitions coincide.

We introduce a novel work-in-progress approach to uniformly model both variants
as a single reduction system on open terms in a multi-language semantics.
This simultaneously defines the compiler and the interoperability semantics.
It also has interesting semantic consequences: different reduction
strategies model different compilation strategies, and standard theorems about
reduction imply standard compiler correctness theorems.
For example, we get a model of ahead-of-time (AOT) compilation by normalizing
cross-language redexes; the normal form with respect to these redexes is a
target language term.
We model just-in-time (JIT) compilation as nondeterministic evaluation in the
multi-language: a term can either step in the source, or translate then step in
the target.
We prove that confluence of multi-language reduction implies compiler
correctness and part of full abstraction; and that subject reduction
implies type-preservation of the compiler.

@;The model also retains properties valued for compiler construction and validation.
@;Reduction systems compose easily, ensuring vertical composition of
@;separate passes.
@;Strong horizontal composition is enabled easily by embedding in the
@;multi-language and syntactic linking.

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

Our approach generalizes from high-level to low-level transformations of a
wide array of language features.
To demonstrate this, we have developed a 5-pass model compiler from a
Scheme-like language to an x86-64-like language.
Here, we model one interesting compiler pass: reduction to A-normal form (ANF).
This pass is a good example and stress test.
The A-reductions are tricky to define because they reorder a term with respect
to its context, while the other passes locally transform a term in an arbitrary
context.

The source is a standard dynamically typed functional imperative language,
modeled on Scheme.
It has a call-by-value heap-based small-step semantics,
@render-term[ANFL (λi->j (H S.e_1) (H S.e_2))], where @render-term[ANFL H]
represents the heap and @render-term[ANFL S.e] is represents a source
expression.@note{
We use a prefix followed by a dot (.) to distinguish terms in each
language---the prefix @emph{S} for source terms and the prefix @emph{A} for ANF
terms.
}
We omit the syntax and reduction rules for brevity.

@;@figure["fig:anf-syntax" @elem{@|anf-lang| Syntax}
@;  (render-language λaL #:nts '(v n e))
@;  (render-language λaL-eval #:nts '(E v))
@;]

The target language is essentially the same, but the syntax is restricted to
A-normal form: all computations @render-term[ANFL A.n] require values
@render-term[ANFL A.v] as operands; expressions @render-term[ANFL A.e]
cannot be nested and only explicitly compose and sequence intermediate
computations @render-term[ANFL A.n].
The reduction relation, @render-term[ANFL (λa->j (H A.e_1) (H A.e_2))],
does not require a control stack.

@figure["fig:anf-multi-syn" @elem{@|anf-multi-lang| Syntax (excerpts)}
  (parameterize ([extend-language-show-union #t]
                 [extend-language-show-extended-order #t])
    (hc-append 40
      (render-language ANFL #:nts '(A.e A.n A.v))
      (render-language ANFL #:nts '(S.e e))))
]

To develop a multi-language semantics, we embed syntactic terms from each
language into a single syntax, defined in @Figure-ref{fig:anf-multi-syn}.
We extend each meta-variable with boundary terms @render-term[ANFL (SA A.e)]
(``Source on the outside, ANF on the inside'') and @render-term[ANFL (AS S.e)]
(``ANF on the outside, Source on the inside'').

@(require (only-in redex/pict render-reduction-relation-rules))
@figure["fig:a-red" @elem{The A-reductions (excerpts)}
  (parameterize ([render-reduction-relation-rules '("A-normal" "A-merge-l" "A-merge-b" "A-join" "A-lift")])
    (render-reduction-relation anf-> #:style 'compact-vertical))
]

The translation to ANF can be viewed as a reduction system in the
multi-language.
@;In fact, the original presentation of ANF was as a reduction system, and this is
@;where A-normal form derives its name---the normal form with respect to the
@;A-reductions@~cite{flanagan1993}.
We define the A-reductions in @Figure-ref{fig:a-red}.
These rules are essentially standard@~cite{flanagan1993}, but we modify them to
make boundary transitions explicit.
The A-reductions have the form @render-term[ANFL (anf->j S.e S.e)], reducing
source expressions in the multi-language.
Each A-reduction rewrites a source expression in a source evaluation context,
transforming the control stack into a data stack.
For example, the A-lift rule lifts a trivial computation, let-binding it and
providing the let-bound name (a value) in evaluation position, explicitly
sequencing the computation @render-term[ANFL A.n] with the evaluation context
@render-term[ANFL S.E].
The side-conditions syntactically encode termination conditions, preventing
A-reductions of target redexes and in empty evaluation contexts.

@figure["fig:anf-boundary-red" @elem{@|anf-multi-lang| Boundary Reductions}
  (render-reduction-relation st-> #:style 'horizontal)
]

We supplement the multi-language A-reductions with the standard boundary
cancellation reductions, given in @Figure-ref{fig:anf-boundary-red}.
These apply under any multi-language context @render-term[ANFL C].

@figure["fig:anf-trans-red" @elem{@|anf-multi-lang| Translation Reductions}
  (hc-append 60
   (parameterize ([extend-language-show-union #t]
                  [extend-language-show-extended-order #t])
     (render-language ANFL #:nts '(T)))
   (with-paper-rewriters (render-judgment-form-rows anf->+j '(2))))
]

In @Figure-ref{fig:anf-trans-red} we define the translation reductions.
These extend the A-reductions to apply under any translation context
@render-term[ANFL T].
The construction of the translation context for ANF is a little unusual, but
the intuition is simple: a translation context identifies a pure source
expression under any context, including under a target/source boundary.
The context @render-term[ANFL A.Cm] corresponds to an ANF context that can have
any expression in the hole.
In one step, the translation reductions can perform either one A-reduction
or one boundary cancellation.

From the translation reductions, we derive AOT compilation as
normalization with respect to translation reductions.
@mdef["ANF Compilation by Normalization"]
@render-judgment-form[anf-compile]

@figure["fig:anf-multi-red" @elem{@|anf-multi-lang| Multi-language Reduction}]{
  @(with-paper-rewriters (render-judgment-form-rows anf-eval->+'(2 2 1)))
}

Finally, we define the multi-language semantics in
@Figure-ref{fig:anf-multi-red}.
This defines all possible transitions in the multi-language.
A term can either take a step in the source language, or a translation step, or
a step in the target language.
Multi-language reduction is indexed by a heap, @render-term[ANFL H], which
is used by the source and target reductions but not the translation reductions.

Note that terms already in the heap are not translated, which corresponds to an
assumption that the language memory models are identical.
We could lift this restriction by adding multi-language boundaries to heap
values and extending translation reductions to apply in the heap.

The multi-language reduction allows reducing in the source, modeling
interpretation, or translating then reducing in the target, modeling
JIT compilation before continuing execution.
This does not model speculative optimization; equipping the multi-language with
assumption instructions as done by @citet{flueckiger2018:jit} might support
modeling this.

Standard meta-theoretic properites of reduction impliy standard compiler
correctness results.

Subject reduction of the multi-language semantics implies type-preservation of
the compiler.
This is simple for our present compiler, since the type system is simple, but
the theorems applies for more complex type systems.

@mthm[@elem{Subject Reduction implies Type Preservation} #:tag "thm:type-pres-type-pres"]{
If (@render-term[ANFL (ANFL-types Γ e_1 τ)] and @render-term[ANFL (anf->*j e_1 e_2)]
implies @render-term[ANFL (ANFL-types Γ e_2 τ)]) then@exact{\\}
(@render-term[ANFL (λiL-types S.Γ S.e S.τ)] and @render-term[ANFL (anf-compile S.e A.e)] implies
∃@render-term[ANFL A.Γ],@render-term[ANFL A.τ].
@render-term[ANFL (λaL-types A.Γ A.e A.τ)]).
}

We derive compiler correctness from confluence.

@mconj[@elem{Confluence} #:tag "thm:anf:confluence"]{
If @render-term[ANFL (anf-eval->* (H e) (H_1 e_1))] and @exact{\\}
@render-term[ANFL (anf-eval->* (H e) (H_2 e_2))] then
@render-term[ANFL (anf-eval->* (H_1 e_1) (H_3 e_3))] and
@render-term[ANFL (anf-eval->* (H_2 e_2) (H_3 e_3))]
}

Note the multi-language semantics can reduce open terms, so confluence implies
correctness of both the AOT and the JIT compiler.
As an example, whole-program correctness is a trivial corollary of confluence.

@mcor[@elem{Whole-Program Correctness} #:tag "thm:anf:correct"]{
@exact{\mbox{}\\}
If
@render-term[ANFL (λi->j* (() S.e) (H S.v))] and
@render-term[ANFL (anf-compile S.e A.e)] then
@render-term[ANFL (λa->j* (() A.e) (H A.v))] such that
@render-term[ANFL A.v] is equal to
@render-term[ANFL S.v].
}

Multi-language semantics provide a strong attacker model through contextual
equivalence.
A context @render-term[ANFL C] models an attacker that can provide
either source or target code or data as input and observe the result.
Contextual equivalence is extended to relate reduction configurations, not
just terms, to enable the definition to apply to the JIT model.

@mdef["Contextual Equivalence"]{
@render-term[ANFL (H_1 e_1)] @exact{$\mathrel{\approx}$} @render-term[ANFL (H_2 e_2)]
if for all multi-language contexts @render-term[ANFL C], @render-term[ANFL
(H_1 (in-hole C e_1))] and @render-term[ANFL (H_2 (in-hole C e_2))] co-terminate
in @(ANFL->-arrow).}

We define secure compilation of both the AOT and JIT models as full abstraction:
contextual equivalence is preserved and reflected through multi-language
reduction.

@mthm["Full Abstraction (multi-language)"]{
Suppose
@render-term[ANFL (anf-eval->+ (H_1 e_1) ((prime H_1) (prime e_1)))] and
@render-term[ANFL (anf-eval->+ (H_2 e_2) ((prime H_2) (prime e_2)))].
@exact{\\}Then
@render-term[ANFL (H_1 e_1)] @exact{$\mathrel{\approx}$} @render-term[ANFL (H_2 e_2)]
if and only if
@render-term[ANFL ((prime H_1) (prime e_1))] @exact{$\mathrel{\approx}$}
@render-term[ANFL ((prime H_2) (prime e_2))].
}

The normally easy part of full abstraction, within the multi-language, is now a
direct consequence of confluence, since both compilation and contextual
equivalence are defined by multi-language reduction.
The hard part, showing any multi-language context (attacker) is emulated by a
source context, remains.

@;{
Theorem (Contextual Equivalence implies Full Abstraction): If (e1 \approx e2) then (Suppose and e1 \Rightarrow e1' and e2 \Rightarrow e2'. e1 \approx e2 and e1 \Rightarrow e1' and e2 \Rightarrow e2' if and only iff e1' \approx e2') (where \approx is contextual equivalence, and \Rightarrow is single-step multi-language reduction).

This theorem is a bit silly. Under the first premise, the first premise of full abstraction is completely unnecessary, so this statement devolves into the statement for full abstraction, I think. We can immediately simplify:

It suffices to prove just full abstraction: (Suppose and e1 \Rightarrow e1' and e2 \Rightarrow e2'. Then e1 \approx e2  if and only iff e1' \approx e2') (where \approx is contextual equivalence, and \Rightarrow is single-step multi-language reduction).

Now, we can easily prove the if case. Assume e1 \approx e2 and e1 \Rightarrow
e1' and e2 \Rightarrow e2'. We must show e1' \approx e2'.
Assume an arbitrary context C, we must show C[e1'] and C[e2'] co-terminate.
Instantiate our hypothesis e1 \approx e2 with C; we learn that C[e1] and C[e2] co-terminate.
Observe that reduction in the multi-language is the same relation used by
contextual equivalence (I think this is what you were trying to observe). Since
e1 \approx e2, we know that C[e1] \Rightarrow* v and C[e2] \Rightarrow* v, or
both diverge. In the former case, by confluence, C[e1] \Rightarrow e1'
\Rightarrow* v and C[e2] \Rightarrow e2' \Rightarrow* v, so clearly C[e1]
\approx C[e2']. Similarly in the latter case.

We must now show the only-if case: Assuming C[e1'] \approx C[e2'] and e1 \Rightarrow e1' and e2 \Rightarrow e2', we must show C[e1] \approx C[e2]. The proof is similar to the previous case.

Unfortunately, even this isn't quite full abstraction. Really, we want the statement to be purely in terms of source and target contexts. Ideally, this theorem would imply that theorem.

But that seems unlikely; this theorem is extremely strange. We never once had to reason about the translation itself or make any assumptions. Full abstraction just holds by construction. This is worrying. Either we have a bug in the proof, or our definitions make full abstraction an uninteresting property.
}

@(generate-bibliography)
