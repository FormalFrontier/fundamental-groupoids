# Contributors and mathematical sources

Authors: Formal Frontier Agents.

Formal Frontier AI agents contributed the Lean proofs, characteristic APIs,
verification examples and mathematical documentation for endomorphism transport,
chosen-vertex equivalences, connectedness, small-path generation and strict
open-cover descent. The library uses the `FundamentalGroupoids` module root and
the `FundamentalGroupoidsTest` verification root; module imports and the
project-specific test namespace have been adapted to those roots. One test proof
uses `simp` in place of `simpa`.

J. Peter May's *A Concise Course in Algebraic Topology*, revised author PDF,
Chapter 1, §3 and Chapter 2, §§5, 7, supplies mathematical motivation and
arguments. The book is published by the University of Chicago Press.
Commutative transport is expressed for arbitrary categories; open-cover descent
allows arbitrary indexed covers and arbitrary target categories. The book is
cited for its mathematics, not reproduced here. Author hosting does not grant
permission to redistribute the PDF or copied excerpts.

The formalization builds on [Mathlib](https://github.com/leanprover-community/mathlib4).
In particular, it uses Mathlib's canonical endomorphism monoids and groups,
conjugation, one-object categories, connected categories, path-homotopy classes,
open subspaces, equality transport and colimits rather than defining replacements.
The source modules retain the following specific credits:

- Shing Tak Lam: Mathlib's fundamental groupoids.
- Kim Morrison: pairwise diagrams and open-subspace functors.
- David Loeffler: open covers.
- Patrick Massot and Kim Morrison: interval subdivision.
- Sebastian Kumar: subpaths and concatenation.
- Andrew Yang, Joël Riou and Aras Ergus: morphism-property composition,
  strict images and multiplicative closure.

All authentic source headers and module references are retained. The code is
licensed under Apache-2.0; see [LICENSE](LICENSE).
