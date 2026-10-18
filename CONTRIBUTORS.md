# Contributors and mathematical sources

Authors: Formal Frontier Agents.

Formal Frontier AI agents contributed the Lean proofs, characteristic APIs,
verification examples and mathematical documentation for endomorphism transport,
chosen-vertex equivalences, connectedness, small-path generation and strict
open-cover descent. The library uses the `FundamentalGroupoids` module root and
the `FundamentalGroupoidsTest` verification root; module imports and the
project-specific test namespace have been adapted to those roots. One test proof
uses `simp` in place of `simpa`.

The components-of-elements equivalences, their representative and naturality
APIs, and the two-value and empty-diagram examples are by Formal Frontier Agents.
They build on Mathlib's categories of elements (Kim Morrison and Joël Riou),
connected components (Bhavik Mehta), quotient-type colimits (Joël Riou) and
colimits in `Type` (Kim Morrison, Reid Barton and Joël Riou).

The generic covering-space formalizations originate in
[sphere-topology](https://github.com/FormalFrontier/sphere-topology), authored by
Formal Frontier Agents. Its `CoveringLifting`, `CoveringEquivalence`,
`CoveringMonodromy`, `DeckGroup` and `DeckMonodromy` modules are the source of
`FundamentalGroupoids.Topology.Covering.{Lifting,Equivalence,Monodromy,DeckGroup,DeckMonodromy}`.
Their Apache-2.0 and authorship notices are retained, as are the mathematical
references and credits to prior formalizations.

J. Peter May's *A Concise Course in Algebraic Topology*, revised author PDF,
Chapter 1, §3 and Chapter 2, §§5, 7, supplies mathematical motivation and
arguments. The book is published by the University of Chicago Press.
Commutative transport is expressed for arbitrary categories; open-cover descent
allows arbitrary indexed covers and arbitrary target categories. The book is
cited for its mathematics, not reproduced here. Author hosting does not grant
permission to redistribute the PDF or copied excerpts.
The covering modules draw on Chapter 3, §§2–4, 7 for monodromy, based lifting
and maps of covers. They state the asymmetric connectivity and local path
connectedness hypotheses explicitly; the equal-image homeomorphisms are over a
fixed base, not an unbased classification.

The formalization builds on [Mathlib](https://github.com/leanprover-community/mathlib4).
In particular, it uses Mathlib's canonical endomorphism monoids and groups,
conjugation, one-object categories, connected categories, path-homotopy classes,
open subspaces, equality transport and colimits rather than defining replacements.
The source modules retain the following specific credits:

- Shing Tak Lam: Mathlib's fundamental groupoids.
- Bhavik Mehta: categorical sigma descent and restriction isomorphisms.
- Johannes Hölzl, Mario Carneiro and Yury Kudryashov: connected-source
  factorization through a summand of a topological sigma type.
- Kim Morrison: pairwise diagrams, open-subspace functors and deck transformations.
- David Loeffler: open covers.
- Patrick Massot and Kim Morrison: interval subdivision.
- Sebastian Kumar: subpaths and concatenation.
- Andrew Yang, Joël Riou and Aras Ergus: morphism-property composition,
  strict images and multiplicative closure.
- Junyan Xu: covering-space lifting and monodromy in
  `Mathlib.Topology.Homotopy.Lifting`, and separated-map uniqueness in
  `Mathlib.Topology.SeparatedMap`.
- Kenny Lau and Antoine Chambert-Loir: equivariant maps in
  `Mathlib.GroupTheory.GroupAction.Hom`.
- Chris Hughes and Yury Kudryashov: pretransitive actions in
  `Mathlib.Algebra.Group.Action.Pretransitive`.

All authentic source headers and module references are retained. The code is
licensed under Apache-2.0; see [LICENSE](LICENSE).
