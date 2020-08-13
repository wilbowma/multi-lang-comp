#lang scribble/acmart @acmsmall @nonacm @screen

@title{Compilation by Normalization}

@author[
#:orcid "0000-0002-6402-4840"
#:affiliation "University of British Columbia, CA"
#:email (email "wjb@williamjbowman.com")
]{William J. Bowman}

@abstract{
We present a compiler from a Scheme-like language to an x86-64-like assembly
language.
The compiler performs the A-normal-form translation, closure conversion, heap
allocation and representation specification, hoisting, and code generation.

The novelity in the design is that the compiler is not a translation between
languages.
Instead, the compiler is reduction relation in a multi-language semantics.
Normalization of the cross-language redexes performs ahead-of-time (AOT)
compilation.
Evaluation in the multi-language can be see as a specification for just-in-time
(JIT) compilation.

Formalizing the compiler as a multi-language semantics provides interesting
semantic insights, presentation benefits, and verification benefit.
For example, (whole-program) compiler correctness is strong normalization in the
source/target multi-language semantics.
The semantics provides interesting insight into bootstrapping compilers, and may
provide insights into the semantics of JIT compilation and macro systems.
}

@include-section{source.scrbl}
@include-section{a-normal-form.scrbl}
