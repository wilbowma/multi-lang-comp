#lang scribble/acmart @acmsmall @nonacm @screen

@title{Correct Compilation as Multi-Language Normalization}
@(require
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

@abstract{
We design a compiler from a Scheme-like language to an x86-64-like assembly
language.
The compiler performs the A-normal-form translation, closure conversion, heap
allocation and representation specification, hoisting, and code generation.
The novelty in the design is that the compiler is not a translation between
languages, but a reduction relation in a multi-language semantics.

Formalizing the compiler as a multi-language semantics provides
interesting semantic insights, presentation benefits, and verification benefit.
Normalization of the cross-language redexes performs ahead-of-time (AOT)
compilation.
Evaluation in the multi-language models just-in-time (JIT) compilation.
Confluence of multi-language reduction implies compiler correctness.
Subject reduction of the multi-language reduction implies type-preservation of
the compiler.
The reduction systems compose easily, enabling simple vertical composition of
separate passes.
Horizontal composition (linking) is enabled easily be embedding in the
multi-language.
The multi-language semantics is already a starting point for certain approaches
to secure compilation, so this could simplify approaches to secure compilation
based on multi-language semantics.
}

@section{Introduction}
Multi-language semantics were introduced as a syntactic method for modeling the
semantics of inter-language interopability@todo{CITE}.
Since then, they have been widely applied to syntactic approaches to compiler
correcntess and secure compilation@todo{CITE}.
Multi-language semantics are useful for modeling cross-language linking, since
the boundary terms are clearly defined and the pattern for translating
terms across this boundary is straightforward, essentially following the
definition of the compiler at least for simple compositional transformations.

However, multi-language semantics also duplicate effort.
The compiler is essentially defined twice: once on open terms as a syntactic
translation, and once on closed terms as a multi-language boundary reduction.
The two definitions occassionally differ slightly.
For example, defining multi-language closure conversion requires taking
advantage of the fact that the term must be closed, while the normal definition
as a translation is very focused on free variables@todo{CITE}.
One must also prove correspondances between the multi-language reduction and the
compiler, increasing validation effort.

This duplication is unnecessary, since a compiler can be defined as a reduction
system (over open terms) in a multi-language semantics.
This reduces duplication in the definition of the compiler and removes the
duplication in validation.

Viewing a compiler as a multi-language semantics provides interesting semantics
insights.
Normalization of the cross-language redexes performs ahead-of-time (AOT)
compilation; the normal form with respect to these redexes is a target language
term.
Nondeterministic evaluation in the multi-language models just-in-time (JIT)
compilation, as a term can either step in the source, or translatem then step in
the target.
Various compiler correctness theorems are implied by standard semantics results.
For example confluence of multi-language reduction implies compositional
compiler correctness.
Subject reduction of the multi-language reduction implies type-preservation of
the compiler.

The semantics also has useful properties valued for compiler validation.
The reduction systems compose easily, enabling simple vertical composition of
separate passes.
Strong horizontal composition is enabled easily be embedding in the
multi-language.
Multi-language semantics have already been used as a framework for studying full
abstraction, so specifying the compiler as a multi-language semantics fits
neatly into an existing framework for secure compilation, although I have not
discovered any simplications yet.

In this talk, I'll describe part of a compiler from a Scheme-like language to an
x64-64-like language designed completely as a series of multi-language
semantics.
I'll focus on a single pass to describe the approach to designing a compiler as
multi-language reduction, and formalize several definitions derived from the
multi-language semantics.
