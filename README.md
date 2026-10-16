# Fundamental Groupoids

Fundamental groupoids, categorical endomorphism transport, and strict descent
along indexed open covers in Lean. The library extends Mathlib's existing
categories, path-homotopy classes and open-cover APIs; it introduces no replacement
fundamental group or one-object category.

## Headline results

- **Comparison of endomorphism transports**
  ([`CategoryTheory.Iso.conj_eq_iff_mem_center`](FundamentalGroupoids/CategoryTheory/Endomorphism/Conjugation.lean)).
  In any category, two isomorphisms `α β : X ≅ Y` induce the same endomorphism
  transport exactly when the relative loop `α.hom ≫ β.inv` is central in `End X`.
  Commutativity of `End X` makes transport independent of the isomorphism.
  In a groupoid, independence of all transports to a fixed, explicitly isomorphic
  target conversely characterizes commutativity. Loop transport agrees with
  Mathlib's `MulAut.conj`.
- **Equivalence with a chosen vertex group**
  ([`CategoryTheory.SingleObj.isEquivalence_functor_id`](FundamentalGroupoids/CategoryTheory/SingleObj.lean)).
  For a chosen object `x` in a preconnected groupoid, the existing functor
  `SingleObj.functor (MonoidHom.id (End x))` is an equivalence.
  It is full and faithful in every category; only essential surjectivity needs
  the preconnected-groupoid hypothesis.
- **Path connectedness and categorical connectedness**
  ([`FundamentalGroupoid.pathConnectedSpace_iff_isConnected`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Connected.lean)).
  A topological space is path connected if and only if its fundamental groupoid
  is connected, with nonemptiness on both sides. No local path connectedness or
  separation condition is needed.
- **Generation by small paths**
  ([`FundamentalGroupoid.morphismProperty_of_isOpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCover.lean)).
  For an indexed open cover, a composition-stable morphism property holding on
  every local inclusion image holds on every global arrow. Separate identity
  and inverse stability, connectedness and faithful inclusion are unnecessary.
  The local images generate all arrows under multiplicative closure.
  Objectwise components natural on those images extend to a unique natural
  transformation between global functors into any category.
- **Constructed strict open-cover descent and colimits**
  ([`FundamentalGroupoid.descOfIsOpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCoverDescent.lean)).
  Local functors agreeing by equality on every ordered pairwise intersection
  extend to a uniquely determined global functor into any category.
  Restriction and uniqueness are equalities, not merely natural isomorphisms.
  The inclusion cocones are colimits in Mathlib's `Grpd` and `Cat`.

## Using the library

The Lake package is `fundamental-groupoids`. Import the complete interface with:

```lean
import FundamentalGroupoids
```

Individual modules can also be imported separately. In particular,
`FundamentalGroupoids.CategoryTheory.Endomorphism.Conjugation` is topology-free
and independent of the other modules. The chosen-vertex module is also
Mathlib-only; connectedness imports it, but neither depends on the conjugation
companion. Strict descent depends locally only on the small-path generation module.

For a path-connected space and chosen point `x`, apply `Functor.asEquivalence` to
`SingleObj.functor (MonoidHom.id (End (FundamentalGroupoid.mk x)))`.
The [interval client](FundamentalGroupoidsTest/AlgebraicTopology/FundamentalGroupoid/Connected.lean)
uses this construction: its arrow map is the identity, while the other endpoint
is in its essential image but not its object image.

For descent, supply `hU : IsOpenCover U`, local functors `F i`, and equations

```text
(openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
  (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j
```

Then `descOfIsOpenCover hU F hF` is the global functor. Use
`inclusion_comp_descOfIsOpenCover` for restriction, `descOfIsOpenCover_obj` for
object values, and `descOfIsOpenCover_map` or `descOfIsOpenCover_map_fromPath`
for local arrows, including their equality transports. The theorem
`descOfIsOpenCover_unique` identifies any functor with the prescribed restrictions.
For bundled cocones use `isColimitOpenCoverCocone` or
`isColimitOpenCoverCatCocone` through the usual `IsColimit.desc`, `fac` and `uniq`.

## Building

Lean is pinned to `leanprover/lean4:v4.34.0-rc2`; Mathlib is pinned to
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. Mathlib is the only direct package
dependency. The resolved dependencies are recorded in `lake-manifest.json`.

```sh
lake exe cache get
lake build FundamentalGroupoids FundamentalGroupoidsTest
```

Both roots are default build targets. `FundamentalGroupoidsTest` contains the
verification examples, not additional prerequisites for the library.

## Contents

| Module under `FundamentalGroupoids` | Contents |
| --- | --- |
| [`CategoryTheory.Endomorphism.Conjugation`](FundamentalGroupoids/CategoryTheory/Endomorphism/Conjugation.lean) | Pointwise commutation criterion, centrality, commutative transport and group conjugation |
| [`CategoryTheory.SingleObj`](FundamentalGroupoids/CategoryTheory/SingleObj.lean) | Fullness, faithfulness and the chosen-vertex equivalence |
| [`AlgebraicTopology.FundamentalGroupoid.Connected`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Connected.lean) | Path connectedness and connected groupoids |
| [`AlgebraicTopology.FundamentalGroupoid.OpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCover.lean) | Small-path generation and construction of natural transformations |
| [`AlgebraicTopology.FundamentalGroupoid.OpenCoverDescent`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCoverDescent.lean) | Pairwise diagrams, strict descent, characteristic equations and `Grpd`/`Cat` colimits |

## Examples and boundaries

The four clients under [`FundamentalGroupoidsTest`](FundamentalGroupoidsTest.lean)
exercise the advertised interfaces:

- The integer one-object groupoid has a nonidentity loop with identity transport;
  transpositions in the symmetric group on three letters give changed conjugation
  and a noncentral loop.
- The unit interval gives the chosen-vertex equivalence. In `Discrete Bool`, the
  vertex functor is full and faithful but not essentially surjective. The empty
  space and its fundamental groupoid both fail the corresponding connectedness condition.
- Two proper overlapping opens in the interval generate a crossing arrow lying
  in neither single local image. An endpoint property true on every local image
  fails after composition, showing why composition stability is needed.
- Over the real cover `(-∞, 1), (-1, ∞)`, compatible local functors into `Type w`
  descend a mixed arrow `-2 → 0 → 2` to translation by one on lifted integers,
  after the prescribed object transports. This action is not the identity,
  although neither chart contains both endpoints. Empty-space and empty-index
  examples allow arbitrary targets, including the empty category, and use both
  bundled colimit interfaces.

## Conventions and limitations

Production declarations retain Mathlib's mathematical namespaces
`CategoryTheory.Iso`, `CategoryTheory.SingleObj` and `FundamentalGroupoid`.
For an arrow in one chart, the descent map is the local map conjugated by
`eqToHom` of its object-value equalities. Chart compatibility is strict;
compatibility given only by natural isomorphisms is not an input to this API.

The space, cover index, target-object and target-hom universes are independent
in the arbitrary-category descent theorem. The bundled colimits lie in
`Grpd.{u, u}` and `Cat.{u, u}`. The pairwise diagram has chart objects and
ordered pairwise-intersection objects, including empty intersections, but no
object for an intersection of the empty family. No connectedness,
inhabited-intersection, nonempty-target or faithful-inclusion condition is assumed.

These are all-point groupoid constructions. A based fundamental-group pushout
in `GrpCat`, wedge calculations, and covering-space classification are not part
of this interface. The small-path module on its own proves generation and
naturality, not functor descent. The translation example does not assert
nonidentity chart-object casts.

## References

- J. Peter May, *A Concise Course in Algebraic Topology*, revised author PDF,
  Chapter 1, §3 and Chapter 2, §§5, 7 (the groupoid colimit discussion is on
  printed p. 17). [Author's revised text](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf).
  Published by the University of Chicago Press. The categorical transport
  results and the arbitrary-cover, arbitrary-category
  descent statements generalize the corresponding topological results.
- [Mathlib](https://github.com/leanprover-community/mathlib4), especially its
  fundamental groupoid, conjugation, one-object category, open-cover,
  interval-subdivision, subpath, morphism-property and colimit APIs.

## Credits and license

Authors: Formal Frontier Agents. AI agents contributed Lean formalization,
examples and mathematical documentation. May supplies mathematical motivation
and arguments; Mathlib supplies the underlying constructions and APIs.
Individual Mathlib contributions used in the proofs are credited in the module
documentation and [CONTRIBUTORS.md](CONTRIBUTORS.md).
Licensed under Apache-2.0; see [LICENSE](LICENSE).
