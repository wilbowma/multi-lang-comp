# Abstract
System F to Typed Assembly Language is the standard reference for compiler
correctness.
This is unfortunate, since this was not what the paper was designed to
accomplish.
System F is a peculiar choice of language, the paper does not discuss many
important issues of correctness or optimization, it lacks many formal details,
and does not compare to many alternative design choices.
This makes sense, since the paper was about type-preserving compilation.
Unfortunately, it makes a poor standard reference.

In this little document, I explore a not-necessarily-typed translation from a
lambda calculus to an assembly language.
I then layer a type system over the translations, to show they can also be type
preserving.
I briefly explore several alternative options and some implications, but do not
explore them fully.

The following came to me in a dream, resulting from thinking about teaching
introduction to compiler construction for a million hours a week.

# Sketch
Most of the compiler correctness literature focuses on two issues:
control flow (ANF and CPS), and higher-order functions (closure conversion).
Typically, we first perform ANF or CPS, then closure conversion.
This is because ANF and CPS can introduce new closures.
Next, the compiler will specify representation of various data types, manually
allocating heap data structures, etc.
Finally, the compiler performs code generation.

In short, the standard model is

1. CPS Translation
2. Closure Conversion
3. Hoist Procedures
4. Explicit Allocation
5. Code generation

Interestingly, this model differs significantly from the performance-oriented
Chez Scheme compiler, which uses a model somewhat like:

1. Closure Conversion
2. Hoist Procedures
3. Explicit Allocation
4. Monadic Form Transformation
5. Code generation

CPS and ANF are avoided, and monadic form is used instead.
Contrary to arguments about the benefits of CPS and ANF in the compiler
correctness literature, monadic form offers apparent advantages in optimization.
For example, compared to ANF, code duplication is avoided by making the code
generator aware of monadic patterns.
No join points need to be introduced, avoiding additional closure indirection,
and the cost of optimizing additional closures.

More important, perhaps, by supporting algebraic expressions until quite late in
the compiler intermediate languages, the design of several compiler passes is
simplified.
The monadic form translation itself is simpler than CPS or ANF.
Explicit allocation in a production compiler is non-trivial and involves many
intermediate computations, and algebraic expressions simplify its implementation.

A sketch of the key translation steps follows:

## Closure Conversion
Closure conversion assumes all functions bound in a `letrec` form.
A simple transformation on the surface language can deal with elaborating
anonymous lambdas.

The target language binds all closed lambdas (procedures) in a `letrec` form,
and binds all closures in a `letrec` form, as closures could be mutually
recursive.
For clarity, we name these `pletrec`, for procedure `letrec`, and `cletrec`, for
closure `letrec`.
Procedures now take an extra argument, the closure, and dereference previously
free variables from the closure.
The representation of closure is kept abstract.

Binding procedures in a `letrec` form is odd, since the procedures are now closed.
However, further optimization may inline closures, and thus free references to
other procedures.
We use a `letrec` form to enable this.

Distinguishing the `pletrec` and `cletrec` encodes the semantic distinction
between the two in syntax, simplifying the next transformation.

```
(letrec ([f (λ (x ...) e)] ...)
  body)
->
(pletrec ([f$label (λ (c x ...)
                     (let ([fx0 (closure-ref cp 0)]
                           ...
                           [fxn (closure-ref cp n)])
                       e))] ...)
  (cletrec ([f (closure f$label fx0 ... fxn)] ...)
     body))
```

Application is translated simply by passing the applying the closure to itself
and its formal parameters.
```
(e e1 ... en)
->
(e e e1 ... en))
```
The semantics of application is applying the procedure at the label of the
closure.

## Hoisting
Hoisting lifts all, now closed, procedures to the top-level.
Syntactically, this amounts to hoisting and merging all `pletrec` forms.

We can specify this as the following rewrite system:
```
C[(letrec ([f (λ (x ...) e)] ...)
    body)]
->
(pletrec ([f (λ (x ...) e)] ...) C[body])


(pletrec ([f (λ (x ...) e)] ...)
  (pletrec ([g (λ (x' ...) e')])
    body))
->
(pletrec ([f (λ (x ...) e)]
          ...
          [g (λ (x' ...) e')])
  body)
```
Hoisting is the transformation that produces the normal form for this rewrite
system.

## Explicit Allocation
The next pass explicitly allocates closures and structured data.
In a production compiler, it is usually part of the pass that specifies the bit
representation of all data structures, including immediate data.
This involves tagging objects.
Most compiler correctness paper ignore the details of object tagging.

The transformation is straight-forward.
Each data structure introduction form allocates a fresh pointer and initializes
it.
Each elimination form is transformed into a pointer dereference.
We use `(mset! base offset e)` to represent setting the pointer at base `base`
and offset `offset` to the value of `e`, and `(mref base offset)` to dereferene
a pointer.
The form `(allocate bytes)` allocates a number of bytes, returning the pointer to
the base of the allocated memory.
I use Scheme-style `unquote` to indicate computations that we can stage, i.e.,
those that depend only on static values.

```
(closure label fx0 ... fxn)
->
(let ([c (allocate ,(* word-size (+ 1 n))))])
  (begin
    (mset! c ,(* 0 word-size) label)
    (mset! c ,(* 1 word-size) fx0)
    ...
    (mset! c ,(* n word-size) fxn)
    c))
```

```
(cons e1 e2)
->
(let ([c (allocate ,(* word-size 2))])
  (begin
    (mset! c ,(* 0 word-size) e1)
    (mset! c ,(* 1 word-size) fx0)
    c))
```

```
(car e)
->
(mref e ,(* 0 word-size))
```

```
(cdr e)
->
(mref e ,(* 1 word-size))
```

```
#f -> 0
```

```
(if e1 e2 e3) -> (if (neq? e1 0) e2 e3)
```

From the above translation, it's not obvious why algebraic expressions would
simplify the translation.
The computed offsets are all constant (although we have expressed them as
equations), and if the source operands were values, so would the target opands
be.
This is because, in keeping with compiler correctness literature, we have
ignored object tagging and complex data types.
The problem is simple to see when we add a data type like vectors or arrays:

```
(make-vector e)
->
(let ([c (allocate (* ,word-size e))])
  (begin
    (mset! c ,(* 0 word-size) e)
    (init-vector c e)
    c))
```
where `init-vector` initializes the vector fields to 0.

Now, we must compute the number of bytes to allocate dynmically.
We could express this in a CPS or ANF language, but would have to bind the
computation `(* word-size e)` to an auxiliary name.
This needless complicates part of the translation.

The situation is worse when we consider adding object tags.
For eample, when we add taging, the translation of `cons` and `car` become:

```
(cons e1 e2)
->
(let ([c (bitwise-ior (allocate ,(* word-size 2)) ,pair-tag)])
  (begin
    (mset! (bitwise-and c ,pair-mask) ,(* 0 word-size) e1)
    (mset! (bitwise-and c ,pair-mask) ,(* 1 word-size) fx0)
    c))
```

```
(car e)
->
(mref (bitwise-and e ,pair-mask) ,(* 0 word-size))
```

We tag the pointer by adding a tag using bitwise inclusive or.
To reference the correct address, we mask off the tag bits using bitwise and.
Again, this is simplifies by algebraic expressions.
While the few example seems easy, a real compiler has many data types to manage,
and the compiler writer does not want to manually program in ANF or CPS to
manage these auxiliary computations.
The compiler should compile those for them.

## Monadic Form Transformation
Now that most* (many things happened in the production compiler that are not of
particular interest for the model compiler) of the compiler is done, we can make
precise the order of evaluation.
We use a monadic form transformation.

I give a few representative cases.
I use semantic brackets to indicate the translation as a meta-function on syntax.

```
〚(e1 e2)〛= (let ([x1 〚e1〛])
               (let ([x2 〚e2〛])
                 (x1 x2)))
```

```
〚(if e e1 e2)〛= (let ([x 〚e〛])
                    (if x 〚e1〛〚e2〛))
```

```
〚(let ([x e] ...) body)〛= (let ([x 〚e〛] ...)
                              〚body〛)
```

```
〚(mset! e1 e2 e3)〛= (let ([x1 〚e1〛])
                        (let ([x2 〚e2〛])
                          (let ([x3 〚e3〛])
                            (mset! x1 x2 x3))))
```

The monadic transformation, as is plain to see, is considerably simpler than a
CPS translation or ANF translation.
Unlike CPS, the translation itself does not necessarily fix a call-by-value or
call-by-name evaluation strategy; this can be determined by a later pass that
implements the semantics of `let`.
Unlike ANF, the translation does not duplicate code (even without considering
join points), and the translation does not require the compiler writer to write
with procedural accumulators or return lists of bindings.

The translation is obviously compositional, unlike CPS and ANF.

Some arguments against the use of monadic form, including one by this very
author, are that the machine for the monadic intermdiate language (MIL) requires
more stack usage (in its abstract machine) than ANF or CPS.
This is a red-herring.
While true at the intermediate language level, the compiler writer does not care
about IL stack usage, since only the target language will use stack.
The code generate can do a fine job optimizing monadic form; even better, it
seems, than ANF or CPS.

## Code Generation.
In the production compiler, a lot takes place between monadic form and code gen.
In the model, we don't care about these things.

Normally, code generation is considered as one step.
We break it into a couple steps.
First we lower into an imperative language with registers and `if`.
Then we deal with commuting conversion.
The commuting conversions are necessary due to the remaining nesting from
monadic normal form.
Finally, we perform code gen, remove `if`, generating labels and jumps, and end
in a TAL-esque target.

We follow TAL and assume infinite registers.

### lower
```
〚(if pred e1 e2)〛= (if pred 〚e1〛 〚e2〛)
```

```
〚(let ([x e] ...) body)〛= (begin (set! r_x 〚e〛) ... 〚body〛)
```

### commute
We specify the commuting conversions as a system of rewrites again:
```
(set! x (if pred e1 e2)) -> (if pred (set! x e1) (set! x e2))
```

```
(set! x (begin c ... body)) = (begin c ... (set! x body))
```

Notice that this transformation would have duplicates code if performed at a
higher-level of abstraction.

```
(let ([x (if pred e1 e2)]) body) -> (if pred (let ([x e1]) body) (let ([x e2]) body))
```

It's the ability to use mutable global variables (registers) that enables the
optimization.
This suggests we can recover the optimization at a higher level of abstraction
using mutable state, simplifying code generation.

This may be more difficult to prove compositionally correct or secure.
We would need to introduce abstraction boundaries to avoid leaking the value of
the global variable previously hidden by lexical scope.
Well-bracketed state may allow proving this compositionally correct or secure.

It's possible to avoid the code duplication using a join-point, ala ANF, or via
continuations, in CPS:
```
(let ([x (if pred e1 e2)]) body) -> (let ([k (lambda (x) body)]) (if pred (k e1) (k e2)))
```

However, this necessarily creates a closures, which may be difficult to optimize
away, and at the very least costs time to optimize.

### code gen
```
〚(if (,cmp v1 v2) e1 e2)〛= (begin (compare v1 v2) (jump-if cmp L1) (with-label L2 〚e2〛) (with-label L1 〚e1〛))
```

```
〚(pletrec ([x (λ () e)] ...) body)〛= (begin (with-label main 〚body〛) (with-label x 〚e〛) ...)
```
