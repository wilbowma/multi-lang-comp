- Compilers are normalizing reductions in multi-language rewrite systems?
- Could be used to model semantics of JIT, macro systems, and languages with embedded assembly.
  Multi-language semantics have already been used this way, but usually have
  quite rigid restricts at the language boundaries.
  For example, (one of Amal's paper) allows a closure-converted language to
  interroperate with a functional source language, but it assumes all functions
  are closed during reduction. This semantics forbids embedding "open" functions
  (implicit closures) (TODO check that).
  Instead, treating the entire compiler as the multi-language reduction system
  provides a unified semantics for both execution and translation between languages.
- seems related to meta-circular interpreters, but with a fixed hierarchy. Can
  escape up or down the tower, but not extend the tower.
- expressed this way, inherently compositional. guarantees if correct then correct w.r.t. separate compilation.
  (w.r.t. compositional correctness.. harder to say. secure compilation? depends
  on ability to enforce boundaries... certainly not guaranteed)
- correctness amounts to Church-Rosser in the multi-language.
- Requires careful choice of syntax. Want to each syntax to correspond to reduction in 1 language.
  Multi-language boundaries could help here, but a bit tedious to write
  translation once explicit boundary terms get involved.
  Can no longer rely on compatible-closure to specify translation, but need
  administrative rules for managing boundary terms.
- The nanopass library and Lisp-style macro systems are close to an
  implementation technique. Each allows expressing transformations on syntax as
  local rewrites, and automatically runs the rewrites to a normal form.
  However, the set of rewrites expressible is limited.
  In particular, context sensitive rewrites are often not expressible.
  
  Racket's macro system is close to enabling the context sensitive rewrites.
  The macro system tracks various context, such as expression context and
  definition context, and macros can provide hooks to perform context sensitive
  rewrites.
  
  Macro systems differ in a key way: they are open recursive.
  This allows macros to generate new macros.
  Supporting this would require the reduction system be open recursive and
  support a first-class notion of reduction rule.
  This is unlike anything the author has seen in programming languages theory,
  and seems likely to be quite difficult to reason about.
  
  In other respects, macro systems are similar.
  Macro system elaborate all code through a series reductions to a normal form,
  after which a traditional interpreter or compiler takes over.
  The process of macro expansion is performed left-to-right, outside-in, like
  most implementations of reduction systems.


  The nanopass framework supports a sophisticated pattern language for expressing
  transformations that is quite like the deterministic implementation of rewrite
  systems we presented.
  Each translation defines one translation helper for each non-terminal in the language.
  The pattern language supports a catamorphism pattern, which applies the
  appropriate translation helper for the sub-expression's non-terminal.
  This nearly allows the compiler writer to express the compiler as a reduction
  system, although the compiler writer is not free to rely on non-deterministic
  rules, or to write multi-language terms that normalize to the target language.
- The semantics goes someway to providing insight into the process of
  bootstrapping, the often mind-bending process of compiling a compiler with
  itself.
  Bootstrapped compilers can include kind of mysterious translations, such as:
  ```
  (match x
     ['#t #t]
     ['#f #f]
     ...)
  ```
  which we all know to be generating the bit-level representation of booleans
  from their symbolic representation.
  This relies on the fact that the bootstrapped compiler already knows how to
  compile the symbol '#t to the bit-level representation #b000110, which we can
  refer to directly by the symbol #t.
  In a normalizing rewrite system, we can generate #t in the multi-language
  reduction relying on the reduction system to normalize that to its bit-level
  representation in a later step of normalization.
