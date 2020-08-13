#lang scribble/acmart @acmsmall @nonacm @screen
@(require
  (only-in scribble/manual deftech tech)
  "lambda-s.rkt"
  "defs.rkt")

@(require (only-in redex/pict render-term/pretty-write) (only-in redex/reduction-semantics term))
@(define-syntax-rule (render-src-eg e)
   (nested #:style 'code-inset
     (para "Example:")
     (tabular #:row-properties '((top)) (list (list "> " (render-src e))))
     (with-paper-rewriters (render-term/pretty-write λiL (term (eval-λiL e))))))

@title{Source Language: @source-lang}
We start by briefly introducing the source language, @|source-lang|.
The language includes a handful of standard features and is loosely inspired by
Scheme.
Each feature is choosen to make our compiler more @deftech{interesting}, meaning
realistic compilation to an assembly language requires additional non-trivial
compilation passes.

@section{Syntax}
We present the syntax of @source-lang in @Figure-ref{fig:src-syntax}

@figure["fig:src-syntax" @~a{@|source-lang| Syntax}
  (render-language λiL #:nts '(e x tag-pred arith-op))
]

Mutually recursive multi-arity functions are introduced by @render-src{letrec}.
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
Mutable reference complicate several standard compiler translations, such as
ANF, compared to their usual presentation in the literature.

Immutable pairs are introduced with @render-src[pair] and @render-src['()] (the
empty pair), and destructed with @render-src[first] and @render-src[second].
We depart from the usual Scheme names, @tt{cons}, @tt{car}, and @tt{cdr}, that
serve only to evoke past mistakes and confuse the uninitiated.
Pairs serve to represent arbitrary sized, structured, non-immediate data that
must be heap allocated by the compiler.
Mutable references already force us to deal with allocation, but are
insufficient to represent @tech{interesting} data structures.

The language supports literal fixed-sized integers, @render-src[fixnum]s, and a
few arithmetic operations, @render-src{arith-ops}: addition, subtraction,
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
@figure["fig:src-red-comp" @~a{@|source-lang| Reduction (composition rules)}
  (render-reduction-relation λi->composition #:style 'horizontal)
]

@figure["fig:src-red-arith" @~a{@|source-lang| Reduction (arithmetic rules)}
(render-reduction-relation λi->arith #:style 'horizontal)
]

@figure["fig:src-pairs" @~a{@|source-lang| Reduction (pair rules)}
(render-reduction-relation λi->pairs #:style 'horizontal)
]

The language has completely standard left-to-right call-by-value operational
semantics.
All operations are dynamically checked to ensure type safety.
We present the reduction system using evaluation context@todo{cite}.
@render-src[error] simply throws away the the current evaluation context.
We use a store to model @render-src[letrec]@todo{cite}, in addition to mutable
references, which is entirely standard.

For brevity, we give some representative examples rules, but relegate the
complete definition the appendix.


@section{Examples}
The language allows us to implement favorite example programs from the compilers
literature, such as factorial:

@render-src-eg[
(letrec ([fact (λ (n)
                 (if (eq? n 0)
                     1
                     (* n (fact (- n 1)))))])
  (fact 5))
]


Or even and odd:

@render-src-eg[
(letrec ([not (λ (n) (if n #t #t))]
         [even (λ (n)
                 (if (eq? n 0)
                     #t
                     (not (odd (- n 1)))))]
         [odd (λ (n)
                (if (eq? n 0)
                    #f
                    (not (even (- n 1)))))])
  (pair (even 0) (pair (odd 0) (pair (even 1) (odd 1)))))
]

In this example, we return a list of answers since our language does lack the
ability to print to the sreen (or, paper).

Mutable references lets us implement the standard example of two
hopefully-observationally-equivalent counters that use local state.

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

