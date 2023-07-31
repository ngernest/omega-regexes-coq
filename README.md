# Verified Equivalence Checker for Omega-Regular Expressions

This repository contain the full Coq development of my bachelor thesis.

It is hosted here: https://ioku00001.github.io/bachelor-thesis/toc.html

We use [coqdoc](https://github.com/coq-community/coqdocjs) to generate the html files.

Abstract: 

Languages over infinite words are important in computer science, for example in verification, reactive synthesis and algebra. Therefore, designing suitable representations and reliable algorithms for languages is crucial to these fields. 

For many of these applications, languages over infinite words are modeled as automata, although reasoning formally about automata is hard. In contrast, omega-regular expressions, another representation of languages over infinite words, have the advantage that they are syntactic objects and therefore easier to reason about. In particular, they are easier to formalize in an interactive proof assistant. 

In this thesis, we study the semantics of omega-regular expressions in the Coq proof assistant as well as develop and verify an equivalence checker on them. The equivalence checker is proven sound, but not complete, and extracted to an executable OCaml program.



