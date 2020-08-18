#lang scribble/acmart @acmsmall @nonacm @screen
@(require
  (only-in pict vc-append)
  (only-in scribble/manual deftech tech)
  "lambda-s.rkt"
  "defs.rkt")

@(require (only-in redex/pict render-term/pretty-write) (only-in redex/reduction-semantics term))
@(define-syntax-rule (render-src-eg e)
   (nested #:style 'code-inset
     (para "Example:")
     (tabular #:row-properties '((top)) (list (list "> " (render-src e))))
     (with-paper-rewriters (render-term/pretty-write λiL (term (eval/print-λiL e))))))

@title{Source Language: @source-lang}
We start by briefly introducing the source language, @|source-lang|.
The language includes a handful of standard features and is loosely inspired by
Scheme.
Each feature is choosen to make our compiler more @deftech{interesting}, meaning
realistic compilation to an assembly language requires additional non-trivial
compilation passes.

@section{Syntax}
@figure["fig:src-syntax" @elem{@|source-lang| Syntax}
  (render-language λiL #:nts '(e x tag-pred arith-op))
]

We present the syntax of @source-lang in @Figure-ref{fig:src-syntax}

Mutually recursive multi-arity functions are introduced by @render-src[letrec].
For simplicity of presentation, we require functions are named; it is simple to
translate from a language with anonymous functions.

We include an error primitive, @render-src[error], which simply raises an
uncatachable error with no associated information.
It would make our compiler more @tech{interesting} to include a catchable error,
but maybe too interesting for our purposes.
Adding associated information to the error does not make the compiler more
@tech{interesting}.

Mutable references are introduced by @render-src[box], updated with
@render-src[set-box!], and dereferenced by @render-src[unbox].
Purely to support imperative features, we include @render-src[(void)] and the
@render-src[begin] form.
@render-src[begin] allows executing a sequence of imperative expressions
without @render-src[let]-binding their unimportant result, and
@render-src[(void)] represents the unit value, and is implicitly returned by an
imperative primitive.

Immutable pairs are introduced with @render-src[pair] and @render-src['()] (the
empty pair), and destructed with @render-src[first] and @render-src[second].
We depart from the usual Scheme names, @tt{cons}, @tt{car}, and @tt{cdr}, that
serve only to evoke past mistakes and confuse the uninitiated.
Pairs serve to represent arbitrary sized, structured, non-immediate data that
must be heap allocated by the compiler.
Mutable references already force us to deal with allocation, but are
insufficient to represent @tech{interesting} data structures.

The language supports literal fixed-sized integers, @render-src[fixnum]s, and a
few arithmetic operations, @render-src[arith-ops]: addition, subtraction,
mulitplication, and division.
In practice, @render-src[fixnum]s are less than the machine word-size due to
object tagging, but this is not important for our model.
We do not specify their range, but consider the language parameterized by
some @render-src[fixnum] range.

The language includes booleans literals @render-src[#t] for true and
@render-src[#f] for false, eliminated by @render-src[if].
Booleans introduce a second immediate data type, and branching introduces minor
but non-trivial complications in some passes.
Both are useful for making the model compiler more @tech{interesting}.
We also include two predicates, @render-src[<] for comparing
@render-src[fixnum]s, and @render-src[eq?] for comparing two values for
identity (pointer equality rather than structural equality).

Finally, we add predicates for checking the tag on each of our data types.
This forces our compiler to model object tagging, a detail often ignored in
models, and definitely @tech{interesting}.

The binding forms, @render-src[letrec], @render-src[let], and @render-src[λ],
support multi-arity bindings that are assumed to be disjoint.

@section{Static Semantics}
We could add an ML-style type system if we wanted to study compilation with
types, but that is not the focus of the present work, so we do not.

All programs must be well bound, implementing The Scheme Type system.
This is completely standard and we omit it for brevity.

@section{Dynamic Semantics}
@figure["fig:src-red-comp" @elem{@|source-lang| Reduction (excerpts)}
(vc-append
 25
 (render-language λiL-eval #:nts '(E S v fv hv))
 (render-reduction-relation
  (union-reduction-relations
   λi->composition
   λi->arith
   λi->pairs
   λi->eq) #:style 'horizontal))
]

We present the reduction system using evaluation context@todo{cite}.
The language has completely standard left-to-right call-by-value operational
semantics, specified in the evaluation context.
For brevity, we abstract all primitive operators using @render-term[λiL primop].
We use a store to model @render-src[letrec]@todo{cite}, in addition to mutable
references, which is entirely standard.
The store @render-term[λiL-eval S] maps an abstract label to heap values
@render-term[λiL-eval S].
We define values to be the base values, plus labels.
We allow names to be values for technical reasons discussed later, although they
should never appear in evaluation position for whole programs.
Heap values include all values, functions, pairs, and mutable boxes.

Note that we do not consider funtions or pairs values in the usual sense.
Instead, they act as effectful operators that perform allocation.
This is more faithful to the how they are implemented in the compiler, and
simplifies the implementation of various semantics, such as the @render-term[λiL
eq?] operator.

The reduction rules are standard, so we give a selection of rules.
@render-term[λiL-eval letrec] allocates the entire mutually recursive block of
functions at once, resolving all names in the block to their labels.
Pair allocates a fresh label, while the first and second projections dereference
the label from the heap.

All operations are dynamically checked to ensure type safety.

@section{Examples}
The language allows us to implement favorite example programs from the compilers
literature, such as factorial.

@(render-prefix-and-finish λiL-eval λi-> (λs->-arrow) 3
  (()
   (letrec ([fact (λ (n)
                    (if (eq? n 0)
                        1
                        (* n (fact (- n 1)))))])
     (fact 5))))

Mutable references let us implement the standard example of two
hopefully-observationally-equivalent counters that use local state.
The below example is rendered with an implementation of a printer for the
language which prints pairs properly.

@render-src-eg[
(let ([counter (let ([b (box 0)])
                 (letrec ([counter-proc
                           (λ ()
                             (begin
                               (set-box! b (+ 1 (unbox b)))
                               (unbox b)))])
                   counter-proc))]
      [slow-counter (let ([b (box 0)])
                      (letrec ([slow-counter-proc
                                (λ ()
                                  (begin
                                    (set-box! b (+ 2 (unbox b)))
                                    (/ (unbox b) 2)))])
                        slow-counter-proc))])
  (pair (counter)
        (pair (counter)
              (pair (slow-counter) (slow-counter)))))
]

@;We can also express weird programs that appear in real languages but rarely in
@;papers, like using intensional polymorphism to define @render-src[++] as the
@;commutative operation on all our data types:
@;
@;@render-src-eg[
@;(letrec ([++ (λ (d1 d2)
@;               (if (fixnum? d1)
@;                   (+ d1 d2)
@;                   (if (boolean? d1)
@;                       (or d1 d2)
@;                       (if (list? d1)
@;                           (append d1 d2)
@;                           (void)))))]
@;         [or (λ (b1 b2) (if b1 b1 b2))]
@;         [and (λ (b1 b2) (if b1 b2 false))]
@;         [list? (λ (l)
@;                  (if (eq? empty l)
@;                      true
@;                      (and (pair? l) (list? (second l)))))]
@;         [append (λ (l1 l2)
@;                   (if (eq? l1 empty)
@;                       l2
@;                       (pair (first l1) (append (second l1) l2))))])
@;  (pair (++ 5 6)
@;        (pair
@;         (++ true false)
@;         (++ (pair 2 empty) (pair 1 empty)))))
@;]
