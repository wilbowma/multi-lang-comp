#lang scribble/acmart @acmsmall @nonacm @screen

@title{Compilation as Multi-Language Semantics}
@(require "bib.rkt")

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
languages, but a reduction relation in a multi-language semantics.
Formalizing the compiler as a multi-language semantics provides interesting
semantic insights, presentation benefits, and verification benefit.
Normalization of the cross-language redexes performs ahead-of-time (AOT)
compilation.
Evaluation in the multi-language models just-in-time (JIT) compilation.
Confluence of multi-language reduction implies compiler correctness.
The reduction systems compose easily, enabling simple veritcal composition of
separate passes.
Horizontal composition (linking) is enabled easily be embedding in the
multi-language.
}

@include-section{source.scrbl}
@include-section{a-normal-form.scrbl}
@(generate-bibliography)
