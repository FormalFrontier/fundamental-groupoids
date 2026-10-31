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

The directed-cover fundamental-group colimit proof uses Mathlib's compact
directed-cover containment and path-homotopy quotient, and Joël Riou's
heterogeneous type-colimit descent and representative APIs. Its subspace path
corestriction is shared with the fundamental-group image criterion and
open-cover groupoid descent.

The pullback component comparisons reuse the independent-universe
orbit–stabilizer equivariance and product-coset orbit/double-coset constructions
from [GroupTheory](https://github.com/FormalFrontier/group-theory), formalized by
Formal Frontier Agents. The covering-space results compose these algebraic
constructions with the canonical monodromy and induced fundamental-group images.

The generic covering-space formalizations originate in
[sphere-topology](https://github.com/FormalFrontier/sphere-topology), authored by
Formal Frontier Agents. Its `CoveringLifting`, `CoveringEquivalence`,
`CoveringMonodromy`, `DeckGroup` and `DeckMonodromy` modules are the source of
`FundamentalGroupoids.Topology.Covering.{Lifting,Equivalence,Monodromy,DeckGroup,DeckMonodromy}`.
Their Apache-2.0 and authorship notices are retained, as are the mathematical
references and credits to prior formalizations.

The signed-period additive-circle and complex-circle integer coordinates,
including their loop, inverse, endpoint and homeomorphism-compatibility APIs,
originate in [Sphere Topology's circle formalization](https://github.com/FormalFrontier/sphere-topology/blob/4a2b822f12e7f2b4255dfea5363265277defa35e/SphereTopology/Homotopy/Circle.lean)
by Formal Frontier Agents. The definitions and proofs retain their authorship and
Apache-2.0 notice. They compose Mathlib's quotient-covering calculation, the
integer period-range equivalence and the fundamental-group equivalence induced
by the additive-circle homeomorphism. May's Chapter 1, §5, pp. 8–9 supplies the
positive circle normalization; the all-integer power-map consumer follows the
signed-loop formula and the power maps of Chapter 1, §7, p. 10.

The based-postcomposition definitions and proofs for generalized loops and
homotopy groups originate in
[Restricted Product Duality's homotopy-map formalization](https://github.com/FormalFrontier/restricted-product-duality/blob/4e17b1b82a95873b94d6f8f9f236658fbf7bb7eb/RestrictedProductDuality/HomotopyMaps.lean)
by Formal Frontier Agents. The generic part through the fundamental-group
compatibility theorem supplies
`FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map`, with the same names,
statements and proofs and retained Apache-2.0 and authorship notices. Its imports
and module documentation describe the generalized-loop and homotopy-group API
independently of restricted products. It builds on Roberto Alvarez's generalized
loops and homotopy groups, Mark Lavrentyev's fundamental groups, and Shing Tak
Lam's relative and path homotopies in Mathlib. The identity, composition,
representative and based-homotopy laws use the existing homotopy quotient and
canonical positive group structures; the dimension-one theorem compares with
Mathlib's fundamental-group map.

The path-component map and its representative, identity, composition and
homotopy-invariance laws also originate in Restricted Product Duality's
`RestrictedProductDuality.HomotopyMaps`, by Formal Frontier Agents. They supply
`FundamentalGroupoids.Topology.Connected.PathConnected` as `ZerothHomotopy.map`,
`map_mk`, `map_id`, `map_comp` and `map_eq_of_homotopy`, retaining the proofs,
pointwise identity/composition statements and Apache-2.0 and authorship notices.
They reuse Mathlib's path components and `Joined.map` by Patrick Massot and
contributors, homotopies by Shing Tak Lam and contributors, and quotient maps.

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
