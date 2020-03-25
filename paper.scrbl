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

Contrary to expectation, the compiler is not a translation between languages.
Instead, the compiler is specified as a reduction relation in a multi-language
semantics.
Normalization of the reduction relation performs compilation.

Formalizing the compiler as a multi-language semantics provides interesting
semantic insights and presentation benefits.
For example, compiler correctness is strong normalization in the source/target
multi-language semantics.
The semantics provides interesting insight into bootstrapping compilers, and may
provide insights into the semantics of JIT compilation and macro systems.
}

@include-section{a-normal-form.scrbl}
