# Fundamental Groupoids

Fundamental groupoids, categorical endomorphism transport, strict open-cover
descent, based van Kampen, covering spaces and semilocal simple connectivity in
Lean. The library extends Mathlib's categories, path-homotopy classes and covering
maps rather than introducing replacement structures. The
[mathematical guide](docs/mathematical-guide.md) gives detailed statements, API
directions, examples, conventions and credits.

## Headline results

- **Endomorphism transport** ([`Conjugation`](FundamentalGroupoids/CategoryTheory/Endomorphism/Conjugation.lean)).
  In any category, transports along `α β : X ≅ Y` agree iff
  `α.hom ≫ β.inv` is central in `End X`. Commutativity makes transport independent;
  in a groupoid the converse holds for a fixed explicitly isomorphic target.
  Loop transport agrees with Mathlib's `MulAut.conj`.
- **Chosen vertex group** ([`SingleObj`](FundamentalGroupoids/CategoryTheory/SingleObj.lean)).
  For a chosen object `x` in a preconnected groupoid,
  `SingleObj.functor (MonoidHom.id (End x))` is an equivalence; it is full and
  faithful in every category, without preconnectedness.
- **Categorical monodromy and preconnectedness** ([`Covering`](FundamentalGroupoids/CategoryTheory/Groupoid/Covering.lean)).
  A quiver-covering functor `E ⥤ B` between categories gives a canonical left
  `Aut b`-action on its fiber. It is pretransitive if `E` is a preconnected
  groupoid. Conversely, for preconnected groupoid base `B`, pretransitivity on
  one specified fiber implies preconnectedness of the total category `E`.
  All four universes are independent; no nonempty fiber or surjectivity is needed.
- **Categories of elements** ([`Elements`](FundamentalGroupoids/CategoryTheory/Groupoid/Elements.lean)).
  For a type-valued functor on any category, strict object fibers recover its
  values. Given a covering proof, lift targets and monodromy agree with the
  functor action; for a groupoid base the projection is a quiver covering.
  The three universes are independent, with no nonemptiness or connectedness.
- **Components as type colimits** ([`ConnectedComponents`](FundamentalGroupoids/CategoryTheory/Elements/ConnectedComponents.lean)).
  For any `X : C ⥤ Type w`, `ConnectedComponents X.Elements ≃ X.ColimitType`,
  naturally and on representatives, with independent object, morphism and value
  universes and no smallness, nonemptiness or connectivity assumptions. An individual
  `HasColimit X` instance gives the comparison with `Limits.colimit X` instead.
- **Path connectedness** ([`Connected`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Connected.lean)).
  A space is path connected iff its fundamental groupoid is connected, including
  nonemptiness on both sides; no local path connectedness or separation is needed.
- **Sheaves of representation sections** ([`SectionsPresheaf`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/SectionsPresheaf.lean)).
  For any topological space `X`, a representation `FundamentalGroupoid X ⥤ Type w`
  determines a presheaf of transport-invariant families, functorially in the representation.
  At an open `U`, its values are canonically equivalent to sections of the representation
  pulled back along `FundamentalGroupoid U → FundamentalGroupoid X`; the comparison
  preserves open restriction and natural transformations. Only paths in the open subspace
  enter the transport condition. Space and fiber universes are independent, with no
  smallness, connectedness, local connectedness or inhabited-fiber assumption.
  This presheaf is a sheaf: compatible families on every open cover glue uniquely.
  No semilocal simple connectivity is needed, and no covering realization is asserted.
  The [limits API](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/SectionsPresheafLimits.lean)
  sends pointwise limit cones to limit cones. For coefficients in `Type v`,
  `[LocallySmall.{v} (FundamentalGroupoid X)]` suffices for the sections-presheaf
  functor to preserve every existing limit, with arbitrary indexing universes and
  no shape-completeness assumption on `Type v`. This asserts sufficiency only,
  not necessity or completeness. More generally, for any `C : Type u`
  with `Category.{a} C`, the sections functor `(C ⥤ Type v) ⥤ Type (max u v)` is
  corepresented by a constant singleton representation and preserves every existing
  limit, without smallness or coefficient-completeness assumptions. The category,
  coefficient and indexing universes remain independent.
- **Arbitrary coproducts and products** ([`Coproduct`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Coproduct.lean),
  [`Product`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Product.lean)).
  The inclusion-induced comparison `Σ i, FundamentalGroupoid (X i) →
  FundamentalGroupoid (Σ i, X i)` is an equivalence; the dependent-product
  comparison is an isomorphism in `Grpd`, with coordinate projection and assembly.
  Index and space universes are independent; no finiteness, connectedness, local
  path connectedness or nonemptiness is needed. The product comparison agrees
  with Mathlib's when its universes coincide.
- **Fundamental groups of dependent products** ([`piMulEquiv`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Product.lean)).
  For arbitrary spaces `X i` and basepoints `p i`, `π₁(∀ i, X i, p)` is
  multiplicatively equivalent to `∀ i, π₁(X i, p i)`, by evaluation and loop
  assembly, naturally in continuous maps and arbitrary reindexing. Index and
  space universes are independent; no finite/nonempty index or connectedness is needed.
- **Small-path generation** ([`OpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCover.lean)).
  For an indexed open cover, a composition-stable morphism property holding on
  every local inclusion image holds globally. No separate identity/inverse
  stability or connectedness is needed. Naturality on local images determines
  a unique natural transformation between global functors into any category.
- **Strict open-cover descent** ([`OpenCoverDescent`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCoverDescent.lean)).
  For any indexed open cover, local functors into any category agreeing by
  equality on every ordered pairwise intersection extend uniquely by equality.
  No connectivity is assumed. Inclusion cocones are colimits in `Grpd` and `Cat`.
- **Indexed based van Kampen** ([`isColimitOfIsOpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean)).
  For an arbitrarily indexed open cover by path-connected neighborhoods of a
  common basepoint with `InfClosed (Set.range U)`, compatible homomorphisms to
  any group extend uniquely from the local fundamental groups. Compatibility is
  along every inclusion, including repeated opens. Space, index and target-group
  universes are independent; the inclusion cocone is a colimit in `GrpCat.{u}`.
  Binary intersection closure does not require the whole space in the range.
- **Two-open based van Kampen** ([`OpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean)).
  For opens `U`, `V` with `U ∪ V = X`, all of `U`, `V`, `U ∩ V` path connected and a point
  in the intersection, compatible homomorphisms to any group extend uniquely,
  satisfying both restriction equations; target and space universes are independent.
  The inclusion square is a pushout in `GrpCat.{u}`. These specialize indexed
  van Kampen; neither formulation adds ambient or local path connectedness.
- **Semilocal simple connectivity** ([`Basic`](FundamentalGroupoids/SemilocallySimplyConnected/Basic.lean),
  [`Maps`](FundamentalGroupoids/SemilocallySimplyConnected/Maps.lean),
  [`LocallyPathConnected`](FundamentalGroupoids/SemilocallySimplyConnected/LocallyPathConnected.lean)).
  At `x`, an open neighborhood's loops **based at `x`** contract in the **ambient
  space**, not necessarily inside the neighborhood. The global class quantifies
  separately over all centers and is vacuous on empty spaces. Simply connected
  spaces satisfy it. Continuous maps with injective induced based fundamental-group
  maps reflect it; local homeomorphisms preserve it pointwise. For every covering,
  the pointwise properties are equivalent and the base property implies the total
  property without surjectivity; global descent needs surjectivity, also for local
  homeomorphisms. Only with local path connectedness do we obtain one open
  path-connected neighborhood controlling loops at all its basepoints in the ambient
  space, not an intrinsically simply connected neighborhood. Space universes are
  independent; no separation or extra connectedness/nonemptiness is assumed.
- **Based lifting and equivalence of covers** ([`Lifting`](FundamentalGroupoids/Topology/Covering/Lifting.lean),
  [`Equivalence`](FundamentalGroupoids/Topology/Covering/Equivalence.lean)).
  A continuous map from a path-connected, locally path-connected domain with
  a prescribed lift of its basepoint has a unique based lift iff its induced
  fundamental-group image lies in the covering image, compared by basepoint equality.
  Two covers with path-connected totals and equal based images at specified points
  over the same point are homeomorphic over the base, taking one point to the other;
  only the source total must be locally path connected. No base connectedness or
  global surjectivity is required.
- **Monodromy, cosets and path components** ([`Monodromy`](FundamentalGroupoids/Topology/Covering/Monodromy.lean),
  [`Components`](FundamentalGroupoids/Topology/Covering/Components.lean)).
  Fiber-point stabilizers are the based fundamental-group images, and orbits are
  joinedness classes, without connectivity or local path connectedness. Orbit
  classes identify with the fiber of the induced path-component map. Over a
  path-connected base they identify with all total-space components, allowing
  empty total spaces and independent total/base universes; total path connectedness
  is equivalent to nonemptiness and pretransitive monodromy. With path-connected total
  and a chosen fiber point, the fiber is equivariantly equivalent to left cosets of the
  induced based fundamental-group image, by `[g] ↦ monodromy g`; normality is not needed.
- **Pullbacks and double cosets** ([`Pullback`](FundamentalGroupoids/Topology/Covering/Pullback.lean),
  [`PullbackDoubleCoset`](FundamentalGroupoids/Topology/Covering/PullbackDoubleCoset.lean)).
  The pullback of two covers is a cover whose fiber is the product with diagonal
  monodromy. Over a path-connected base, diagonal orbits give its components,
  allowing empty/disconnected totals and independent universes. Alternatively,
  with both totals path connected and specified fiber points, components are
  `H \ G / K` for the based fundamental-group images; no base path connectedness is needed.
- **Fiber cardinalities and finiteness** ([`Cardinality`](FundamentalGroupoids/Topology/Covering/Cardinality.lean)).
  Point-fiber cardinality and the predicate of fiber finiteness are locally
  constant, with independent universes. The finite-fiber locus is clopen:
  empty fibers are included, infinite fibers excluded. No connectedness, local
  path connectedness, finiteness, surjectivity or nonempty total is needed.
- **Proper covering maps** ([`Proper`](FundamentalGroupoids/Topology/Covering/Proper.lean)).
  For a covering map between arbitrary topological spaces, Mathlib's
  `IsProperMap` holds iff every point fiber is finite. Total and base universes
  are independent; no separation, local compactness, connectedness, surjectivity
  or uniform degree is required. Over a preconnected base, finiteness of the
  fiber at any given point suffices, without an extra nonemptiness premise.
  For preconnected total and a supplied `e0`, properness instead means finiteness over
  `p e0`. With path-connected total, it means finite index of the canonical based
  fundamental-group image ([`FiniteIndex`](FundamentalGroupoids/Topology/Covering/FiniteIndex.lean));
  neither base connectedness nor surjectivity is required. Compact subsets have compact inverse images.
- **Maps of covers and deck centralizers** ([`DeckMonodromy`](FundamentalGroupoids/Topology/Covering/DeckMonodromy.lean)).
  Over-maps restrict to equivariant maps on a chosen fiber without connectivity
  assumptions. This is an equivalence of map spaces for path-connected base and
  locally path-connected source, allowing empty/disconnected source and arbitrary target cover.
  Alternatively a supplied source point and path-connected, locally path-connected
  source suffice without base connectedness. Deck restriction is a homomorphism
  into the monodromy centralizer in the fiber permutation group; it is injective
  for path-connected base and a multiplicative equivalence if the total is also
  locally path connected, even empty/disconnected. The supplied-point alternative
  needs only path-connected, locally path-connected total, not base connectedness.
- **Deck fixed-point rigidity** ([`DeckGroup`](FundamentalGroupoids/Topology/Covering/DeckGroup.lean)).
  Deck groups act on point fibers. For a separated, locally injective map with
  preconnected total, evaluation at a supplied point is injective: fixing a point
  forces identity. No codomain topology is needed; surjectivity is not asserted.

## Using the library

Add to `lakefile.toml`, pinning `rev` to a release commit if desired:

```toml
[[require]]
name = "fundamental-groupoids"
git = "https://github.com/FormalFrontier/fundamental-groupoids.git"
rev = "main"
```

```lean
import FundamentalGroupoids
```

Individual modules can be imported separately; use `FundamentalGroup.piMulEquiv p`
for pointed products or `FundamentalGroup.isColimitOfIsOpenCover` for indexed based
van Kampen. The deprecated `isColimit_of_isOpenCover` remains a compatibility alias.
See the [guide's API directions](docs/mathematical-guide.md#using-the-library)
and [verification examples](FundamentalGroupoidsTest.lean).

**Covering compatibility:** these modules retain the declaration names relocated
from [sphere-topology](https://github.com/FormalFrontier/sphere-topology).
Do not co-import a legacy version defining its own copies. Joint consumers need
its subsequent shim release and a compatible Fundamental Groupoids pin together;
existing pins do not update automatically. See the [migration warning](docs/mathematical-guide.md#covering-imports-and-compatibility-with-sphere-topology).

## Building

Lean is pinned to `leanprover/lean4:v4.34.0-rc2`; Mathlib is pinned to
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. The other direct package dependency is
[GroupTheory](https://github.com/FormalFrontier/group-theory), pinned to
`12ea07a60c5e6c219d8996eb56d7485139041e15`. The resolved dependencies are recorded
in `lake-manifest.json`.

```sh
lake exe cache get
lake build FundamentalGroupoids FundamentalGroupoidsTest
```

Both roots are default targets; `FundamentalGroupoidsTest` holds verification examples.

## Contents

| Module under `FundamentalGroupoids` | Contents |
| --- | --- |
| [`FundamentalGroup`](FundamentalGroupoids/FundamentalGroup.lean) | Induced maps, null-loop/trivial-image criteria, path transport and homotopy comparisons |
| [`CategoryTheory.Elements.ConnectedComponents`](FundamentalGroupoids/CategoryTheory/Elements/ConnectedComponents.lean) | Components/type-colimit equivalences, representative equations and naturality; induced colimit maps with identity/composition laws |
| [`CategoryTheory.Endomorphism.Conjugation`](FundamentalGroupoids/CategoryTheory/Endomorphism/Conjugation.lean) | Pointwise commutation criterion, centrality, commutative transport and group conjugation |
| [`CategoryTheory.SingleObj`](FundamentalGroupoids/CategoryTheory/SingleObj.lean) | Fullness, faithfulness and the chosen-vertex equivalence |
| [`CategoryTheory.Groupoid.Covering`](FundamentalGroupoids/CategoryTheory/Groupoid/Covering.lean) | Canonical fiber monodromy; pretransitivity for preconnected total groupoids and total preconnectedness from pretransitivity over a preconnected groupoid base |
| [`CategoryTheory.Groupoid.Elements`](FundamentalGroupoids/CategoryTheory/Groupoid/Elements.lean) | Fiber-value equivalence, compatibility with lifts and monodromy, and covering projections on groupoids |
| [`AlgebraicTopology.FundamentalGroupoid.Connected`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Connected.lean) | Path connectedness and connected groupoids |
| [`AlgebraicTopology.FundamentalGroupoid.SectionsPresheaf`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/SectionsPresheaf.lean) | Transport-invariant families, the representation-to-presheaf functor, canonical sections comparison with evaluation and naturality, and the sheaf condition |
| [`AlgebraicTopology.FundamentalGroupoid.Coproduct`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Coproduct.lean) | Canonical sigma comparison equivalence, restriction isomorphism and object bijectivity |
| [`AlgebraicTopology.FundamentalGroupoid.Product`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Product.lean) | Dependent-product comparison, projection, assembly and agreement with Mathlib |
| [`AlgebraicTopology.FundamentalGroupoid.OpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCover.lean) | Small-path generation and construction of natural transformations |
| [`AlgebraicTopology.FundamentalGroupoid.OpenCoverDescent`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCoverDescent.lean) | Pairwise diagrams, strict descent, characteristic equations and `Grpd`/`Cat` colimits |
| [`AlgebraicTopology.FundamentalGroup.Product`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Product.lean) | Fundamental-group product equivalence, coordinate and assembled-loop equations |
| [`AlgebraicTopology.FundamentalGroup.OpenNhds`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenNhds.lean) | Fundamental-group functor on open neighborhoods and its inclusion cocone |
| [`AlgebraicTopology.FundamentalGroup.OpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean) | Indexed based van Kampen for intersection-closed covers: unique compatible homomorphisms and `GrpCat` colimits; two-open pushouts |
| [`SemilocallySimplyConnected.Basic`](FundamentalGroupoids/SemilocallySimplyConnected/Basic.lean) | Chosen-center ambient-null-loop definition, inclusion-image criterion, simply connected spaces and reflection |
| [`SemilocallySimplyConnected.Maps`](FundamentalGroupoids/SemilocallySimplyConnected/Maps.lean) | Local-homeomorphism preservation, covering equivalence and surjective global descent |
| [`SemilocallySimplyConnected.LocallyPathConnected`](FundamentalGroupoids/SemilocallySimplyConnected/LocallyPathConnected.lean) | Open path-connected refinement with ambient nullhomotopies at all basepoints |
| [`Topology.Covering.Lifting`](FundamentalGroupoids/Topology/Covering/Lifting.lean) | Based unique lifting iff fundamental-group image containment |
| [`Topology.Covering.Equivalence`](FundamentalGroupoids/Topology/Covering/Equivalence.lean) | Surjectivity for nonempty source and path-connected target total space; based homeomorphisms from equal images with path-connected totals and locally path-connected source |
| [`Topology.Covering.Monodromy`](FundamentalGroupoids/Topology/Covering/Monodromy.lean) | Fiber-point stabilizers, joinedness, pretransitivity, equivariant fiber–coset equivalence and fiber restriction with identity/composition laws |
| [`Topology.Covering.Components`](FundamentalGroupoids/Topology/Covering/Components.lean) | Orbit equivalence with the path-component-map fiber; path-component image equality; equivalence to all total-space components over a path-connected base |
| [`Topology.Covering.Pullback`](FundamentalGroupoids/Topology/Covering/Pullback.lean) | Pullback covering projections, fiber/product monodromy comparison, and diagonal-orbit/path-component equivalence over a path-connected base |
| [`Topology.Covering.PullbackDoubleCoset`](FundamentalGroupoids/Topology/Covering/PullbackDoubleCoset.lean) | Path components as double cosets of based fundamental-group images for path-connected total spaces with specified fiber points, without base path connectedness |
| [`Topology.Covering.Cardinality`](FundamentalGroupoids/Topology/Covering/Cardinality.lean) | Local constancy of point-fiber cardinalities and finiteness; clopen finite-fiber locus |
| [`Topology.Covering.Proper`](FundamentalGroupoids/Topology/Covering/Proper.lean) | Properness iff point fibers are finite; given-point criteria on a preconnected base or total space |
| [`Topology.Covering.FiniteIndex`](FundamentalGroupoids/Topology/Covering/FiniteIndex.lean) | Properness iff the canonical based fundamental-group image has finite index, for path-connected total space |
| [`Topology.Covering.DeckGroup`](FundamentalGroupoids/Topology/Covering/DeckGroup.lean) | Fiber actions, evaluation embeddings and fixed-point rigidity for separated, locally injective maps with preconnected total space |
| [`Topology.Covering.DeckMonodromy`](FundamentalGroupoids/Topology/Covering/DeckMonodromy.lean) | Equivalences of over-map and equivariant fiber-map spaces; deck-centralizer restriction and multiplicative equivalences |

## Conventions and limitations

The APIs retain Mathlib's namespaces and original structures. Strict descent
uses equality, including `eqToHom` transports, not compatibility only up to
natural isomorphism. Its space, index, target-object and target-hom universes
are independent; bundled colimits have sizes `Grpd.{u, u}` and `Cat.{u, u}`.
The pairwise diagram includes empty intersections, not the empty-family intersection.
Based-group colimits require the stated common-basepoint, path-connected-member,
intersection-closure hypotheses, not an arbitrary open cover. No wedge calculation
or covering-space classification is asserted. A monodromy stabilizer is not
in general its permutation kernel; a centralizer is not a group structure on a fiber.
See [all conventions and boundaries](docs/mathematical-guide.md#conventions-and-limitations).

## References

- J. Peter May, *A Concise Course in Algebraic Topology*, revised author PDF,
  Chapter 1 §3, Chapter 2 §§5, 7 and Chapter 3 §§2–4, 7.
  [Author's revised text](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf).
- [Mathlib](https://github.com/leanprover-community/mathlib4) and
  [GroupTheory](https://github.com/FormalFrontier/group-theory).
  See the [guide's references](docs/mathematical-guide.md#references) for scope and dependencies.
- [VectorBundles](https://github.com/FormalFrontier/vector-bundles/blob/9d2d4b48577e873679271aeee0899239d9a835a1/VectorBundles/Topology/FiberBundle/Proper.lean):
  the local closedness and compact-fiber proof pattern for proper bundle projections.

## Credits and license

Authors: Formal Frontier Agents. AI agents contributed Lean formalization,
examples and documentation. May supplies mathematical motivation and arguments;
Mathlib supplies underlying constructions and APIs. Covering formalizations
originate in sphere-topology by Formal Frontier Agents, with retained Apache-2.0
and authorship notices. Pullback comparisons reuse GroupTheory's orbit–stabilizer
and double-coset constructions. The covering properness proof follows the
local closedness approach formalized in VectorBundles, using Mathlib's proper-map
and compact-projection APIs; no VectorBundles package dependency is required.
The semilocal API uses Mathlib's path quotients, chart homeomorphisms, covering
injectivity and locally path-connected neighborhood basis; it is supporting theory,
not a claimed correspondence with a named theorem in May.
Full prior-formalization and individual credits
are in [CONTRIBUTORS.md](CONTRIBUTORS.md), module documentation and the
[guide](docs/mathematical-guide.md#credits-and-license).
No open redistribution license is inferred for May's author-hosted book; no
book excerpts or PDF assets are included. Licensed under Apache-2.0; see [LICENSE](LICENSE).
