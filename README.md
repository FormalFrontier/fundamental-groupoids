# Fundamental Groupoids

Fundamental groupoids, based homotopy, relative affine homotopies, categorical
endomorphism transport, strict open-cover descent, based van Kampen, covering
spaces and semilocal simple connectivity in Lean. The library extends Mathlib's
categories, path-homotopy classes and covering maps rather than introducing
replacement structures. The [mathematical guide](docs/mathematical-guide.md)
gives detailed statements, API directions, examples, conventions and credits.

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
- **Cube boundaries** ([`Cube`](FundamentalGroupoids/Topology/Homotopy/Cube.lean)).
  For any index type `N` with at least two elements, the coordinate-face boundary of
  `N → I` is path connected, even for infinite `N`. The zero vertex lies in the
  boundary whenever `N` is nonempty.
- **Based generalized-loop lifts** ([`GenLoop`](FundamentalGroupoids/Topology/Covering/GenLoop.lean)).
  A covering map uniquely lifts a based generalized loop to a supplied point when
  the cube index has at least two elements. The spaces need no connectedness, local
  path connectedness or separation assumptions, and the covering need not be surjective.
- **Coverings on positive homotopy groups** ([`Covering.HomotopyGroup`](FundamentalGroupoids/Topology/Covering/HomotopyGroup.lean)).
  A covering induces an injection on the cubical homotopy quotient for every nonempty
  index type, and a bijection when the index has at least two elements. Neither needs
  decidable equality. With supplied decidable equality, the latter is a multiplicative
  equivalence for the stock group structures: its forward map is `HomotopyGroup.map`,
  and its inverse sends a class to the class of its chosen based lift. The cube, total
  and base universes are independent, without connectedness, local path connectedness,
  separation, finiteness or global surjectivity assumptions. For `Fin n` this gives
  the covering isomorphism in degrees `n ≥ 2`; arbitrary indices use the coordinate-face
  boundary, without a sphere-domain comparison.
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
- **Categorical based products** ([`Products`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Products.lean),
  [`Based.Products`](FundamentalGroupoids/Topology/Category/TopCat/Based/Products.lean)).
  The fundamental-group functor preserves every existing indexed product,
  including the empty product, with independent index and space universes.
  This is preservation, not a blanket large-product existence assertion.
  The stock comparison acts by the based projections; after the canonical based
  product identification, its coordinate homomorphism is exactly `piMulEquiv`.
  No connectedness, finiteness or index-smallness premise is needed.
- **Circle integer coordinates** ([`Circle`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Circle.lean)).
  For every nonzero real period `T`, `π₁(AddCircle T, 0) ≃* Multiplicative ℤ`,
  with the loop lifted from `0` to `T * n` assigned `n`, including negative periods.
  The induced period-one homeomorphism gives `π₁(Circle, 1) ≃* Multiplicative ℤ`,
  sending the counterclockwise full turn to `+1`. Signed-loop, inverse, endpoint,
  nonidentity and homeomorphism-compatibility laws are public; zero-period loops
  are constant. The coordinate core uses Mathlib alone.
- **Higher circle homotopy quotients** ([`HomotopyGroup.Circle`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Circle.lean)).
  At every basepoint `z` and for every index type `N` with at least two elements,
  `HomotopyGroup N Circle z` is a subsingleton, using the coordinate-face boundary
  even for infinite `N`. For finite indices this gives `πₙ(Circle, z) = 0` for
  `n ≥ 2`; no decidable equality or group instance is required for the quotient result.
- **Fundamental groups and based homotopy** ([`Based`](FundamentalGroupoids/Topology/Category/TopCat/Based.lean),
  [`Functor`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Functor.lean)).
  Based spaces form the under category of the one-point space. The fundamental
  group at the selected point and the induced homomorphism define a functor to
  `GrpCat`. It factors uniquely through the category of based-homotopy classes,
  with object, representative-map and loop-class characteristics. The quotient
  identifies exactly the based-homotopic maps and has Mathlib's categorical
  universal property and natural-transformation descent. Spaces and selected
  points are arbitrary, without connectedness, separation or well-pointedness.
- **Based maps on homotopy groups** ([`HomotopyGroup.Map`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Map.lean)).
  A continuous map preserving supplied points acts on generalized loops and on
  their homotopy quotient for every cube-index type, including an empty one.
  For nonempty indices with decidable equality, the same function is a group
  homomorphism. Representative, constant, identity, composition and based-homotopy
  laws are public; in dimension one the map agrees with `FundamentalGroup.mapOfEq`
  under Mathlib's multiplicative comparison. Cube and space universes are
  independent, with no separation, connectedness or finiteness assumptions.
  The module uses Mathlib alone.
- **Relative affine homotopies and vector-space quotients** ([`Affine`](FundamentalGroupoids/Topology/Homotopy/Affine.lean),
  [`HomotopyGroup.Affine`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Affine.lean)).
  Continuous maps from any space into a real vector space with continuous
  addition and scalar multiplication admit an affine homotopy fixed on any
  subset where they agree. Every generalized loop in such a vector space is
  homotopic to the constant loop relative to its cube boundary, so
  `HomotopyGroup N E x` is a subsingleton for every index type and every chosen
  point. Cube and target universes are independent; empty and infinite indices
  are allowed. No separation, norm, completeness or positive-degree group
  structure is required.
- **Homotopy-retraction splittings** ([`retractionOfHomotopy`](FundamentalGroupoids/FundamentalGroup.lean)).
  For `g : C(X, Y)`, `f : C(Y, X)` and a homotopy from `f.comp g` to `id X`,
  transport along its track at `x` gives an explicit left inverse of
  `π₁(X, x) → π₁(Y, g x)`, which is therefore injective. A nontrivial source
  vertex group and a subsingleton target vertex group obstruct such a homotopy.
  Space universes are independent; no connectedness or fixed-basepoint condition is needed.
- **Small-path generation** ([`OpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCover.lean)).
  For an indexed open cover, a composition-stable morphism property holding on
  every local inclusion image holds globally. No separate identity/inverse
  stability or connectedness is needed. Naturality on local images determines
  a unique natural transformation between global functors into any category.
- **Strict open-cover descent** ([`OpenCoverDescent`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCoverDescent.lean)).
  For any indexed open cover, local functors into any category agreeing by
  equality on every ordered pairwise intersection extend uniquely by equality.
  No connectivity is assumed. Inclusion cocones are colimits in `Grpd` and `Cat`.
- **Full-inclusion open-cover colimits** ([`OpenCoverInclusions`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCoverInclusions.lean)).
  For an indexed open cover with `InfClosed (Set.range U)`, the diagram retaining
  every index and every open inclusion has the ambient fundamental groupoid as
  its colimit in both `Grpd` and `Cat`. Chart functors into any category agreeing
  by equality along all inclusions extend uniquely by equality, with independent
  space, index, target-object and target-morphism universes. No path connectedness,
  common point, finiteness, injective indexing or member equal to the whole space
  is required. This generalizes May's groupoid theorem on printed p. 17 by dropping
  its path-connected-member hypothesis; the based theorem on p. 18 remains separate.
- **Indexed based van Kampen** ([`isColimitOfIsOpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean)).
  For an arbitrarily indexed open cover by path-connected neighborhoods of a
  common basepoint with `InfClosed (Set.range U)`, compatible homomorphisms to
  any group extend uniquely from the local fundamental groups. Compatibility is
  along every inclusion, including repeated opens. Space, index and target-group
  universes are independent; the inclusion cocone is a colimit in `GrpCat.{u}`.
  Binary intersection closure does not require the whole space in the range.
- **Directed open-cover colimits** ([`DirectedOpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/DirectedOpenCover.lean)).
  For any topological space with a supplied basepoint and an arbitrarily indexed,
  inclusion-directed open cover by its neighborhoods, compatible homomorphisms
  from the local fundamental groups to any monoid extend uniquely to a
  homomorphism from the ambient group. Compatibility is along every inclusion
  between presented neighborhoods; the diagram uses `inducedFunctor U`.
  The existing inclusion cocone is a colimit in `GrpCat.{u}`. All indices are
  retained, including repeated opens, and all maps are inclusion-induced.
  Space, index and target-monoid universes are independent; no path connectedness,
  intersection closure, separation, local connectivity, finiteness, dimension or
  separate index nonemptiness assumption is imposed.
- **Directed-preorder neighborhood-cover colimits** ([`DirectedOpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/DirectedOpenCover.lean)).
  Let `X : Type u` be any topological space, `p : X`, and `J : Type v` have
  `[Preorder J] [IsDirectedOrder J]`. For a monotone open-neighborhood cover
  `U : J → OpenNhds p`,
  `FundamentalGroup.existsUnique_hom_of_isOpenCover_of_monotone` extends local
  homomorphisms to any monoid `G : Type w` uniquely along the canonical inclusion
  legs. Compatibility is required only for `i ≤ j`, not for every inclusion
  `U i ≤ U j`. For `hU : Monotone U`, the noncomputable definition
  `FundamentalGroup.isColimitOfIsOpenCoverOfMonotone` supplies
  `IsColimit ((openNhdsCocone p).whisker hU.functor)` in `GrpCat.{u}`.
  Its diagram uses the ordinary preorder category on `J`. The universes `u`, `v`
  and `w` are independent; no path connectedness, intersection closure, separation,
  local connectivity, smallness, injectivity, order reflection or separate
  nonemptiness assumption on `J` is required.
- **Open-cover quotient presentations** ([`OpenCoverPresentation`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCoverPresentation.lean)).
  An intersection-closed open cover by path-connected neighborhoods of a common
  point presents the ambient fundamental group as the free product of the local
  groups modulo the normal closure of all inclusion-arrow relators. The quotient
  equivalence preserves the inclusion legs in both directions; the canonical
  free-product map is surjective with exactly this kernel. Arbitrary indices,
  repeated presentations and independent index/space universes are allowed.
- **Two-open based van Kampen** ([`OpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean)).
  For opens `U`, `V` with `U ∪ V = X`, all of `U`, `V`, `U ∩ V` path connected and a point
  in the intersection, compatible homomorphisms to any group extend uniquely,
  satisfying both restriction equations; target and space universes are independent.
  The inclusion square is a pushout in `GrpCat.{u}`. These specialize indexed
  van Kampen; neither formulation adds ambient or local path connectedness.
- **Simple-connectivity criteria** ([`FundamentalGroup`](FundamentalGroupoids/FundamentalGroup.lean),
  [`OpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean)).
  Simple connectivity is characterized by path connectedness and a
  subsingleton fundamental group at a given point. Two simply connected opens
  covering a space make it simply connected when their intersection
  is path connected, including nonemptiness. A nonempty directed union of open simply
  connected sets is simply connected. An arbitrarily indexed open cover also gives
  simple connectivity when its members are simply connected, share one point, and
  have path-connected pairwise intersections; connected triple intersections are not
  required. These criteria add no ambient or local path connectedness or separation
  assumption; overlaps need not be simply connected.
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
- **Cancellation of covering maps** ([`Composition`](FundamentalGroupoids/Topology/Covering/Composition.lean)).
  If `q ∘ g` and `q` are covering maps, `g` is continuous, and the target of `g` is
  locally connected, then `g` is a covering map. The three space universes are independent;
  no surjectivity, nonempty-fiber, path-connectedness or separation assumption is needed.
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
  Commuting squares of continuous maps intertwine monodromy across different bases;
  neither horizontal map need be a covering. Equivariant squares of quotient covers
  intertwine the canonical homomorphisms to opposite acting groups, without simple
  connectivity. All space and acting-group universes are independent.
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
- **Normalizer quotients and regularity** ([`NormalizerQuotient`](FundamentalGroupoids/Topology/Covering/NormalizerQuotient.lean)).
  For a covering map with path-connected, locally path-connected total space
  and a chosen point, the normalizer quotient of the based fundamental-group
  image is canonically the deck group. A representative acts by monodromy of its inverse at the
  chosen point. The existing deck action on that fiber is pretransitive iff
  the image subgroup is normal, without base connectedness or surjectivity.
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
For based spaces, use `BasedTopCat.of X x` and `BasedTopCat.ofHom f h`;
`FundamentalGroup.functor` gives the induced groups and homomorphisms, and
`FundamentalGroup.homotopyFunctor` acts on based-homotopy classes.
See the [guide's API directions](docs/mathematical-guide.md#using-the-library)
and [verification examples](FundamentalGroupoidsTest.lean).
Use `AddCircle.fundamentalGroupEquivInt hT` for signed nonzero periods, or
`Circle.fundamentalGroupEquivInt` at `1` on the complex unit circle. Their public
loop, inverse and endpoint laws are described in the
[circle coordinate guide](docs/circle-integer-normalization.md), together with the
all-integer power-map consumer, including zero and negative exponents.

For generalized loops and homotopy groups, import
`FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map` and use
`GenLoop.map f hf`, `HomotopyGroup.mapFun N f hf` or, for a nonempty index with
supplied decidable equality, `HomotopyGroup.map N f hf`. Here `hf : f x = y`
relates the supplied points. See the [homotopy-group map guide](docs/mathematical-guide.md#based-maps-on-homotopy-groups).
These declarations keep the names from
[Restricted Product Duality](https://github.com/FormalFrontier/restricted-product-duality).
Co-importing the libraries requires a Restricted Product Duality version whose
`HomotopyMaps` module publicly imports this module rather than defining its own copies.

For real vector spaces, import
`FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Affine` and use
`GenLoop.homotopic_const` or `HomotopyGroup.subsingleton N x`.
The relative construction `ContinuousMap.HomotopyRel.affine` is in
`FundamentalGroupoids.Topology.Homotopy.Affine`. See the
[relative affine guide](docs/mathematical-guide.md#relative-affine-homotopies-and-vector-space-quotients)
for the hypotheses, evaluation laws and empty-index interpretation.

For a covering proof `hf : IsCoveringMap f`, import
`FundamentalGroupoids.Topology.Covering.HomotopyGroup` and use
`hf.injective_homotopyGroup_mapFun N e`, `hf.bijective_homotopyGroup_mapFun N e`
or `hf.homotopyGroupMulEquiv N e` at the index hypotheses above. See the
[covering homotopy-group guide](docs/mathematical-guide.md#covering-maps-on-homotopy-groups)
for representative and chosen-lift inverse formulas.

**Covering and circle compatibility:** these modules retain declaration names
from [sphere-topology](https://github.com/FormalFrontier/sphere-topology).
Do not co-import a version defining its own copies. Joint consumers must select
a Sphere Topology version whose old modules publicly import the canonical
Fundamental Groupoids modules, with a compatible dependency pin. See the
[covering compatibility warning](docs/mathematical-guide.md#covering-imports-and-compatibility-with-sphere-topology)
and the [circle guide](docs/circle-integer-normalization.md#integer-power-map-consumers).

## Building

Lean is pinned to `leanprover/lean4:v4.34.0-rc2`; Mathlib is pinned to
`83abb3e776bdefcbc447a1e44d0debe4010039e5`. The other direct package dependency is
[GroupTheory](https://github.com/FormalFrontier/group-theory), pinned to
`da81dc691eabf38306f427465ea8a4af350f0aef`. The resolved dependencies are recorded
in `lake-manifest.json`.

```sh
lake exe cache get
lake build FundamentalGroupoids FundamentalGroupoidsTest
```

Both roots are default targets; `FundamentalGroupoidsTest` holds verification examples.

## Contents

| Module under `FundamentalGroupoids` | Contents |
| --- | --- |
| [`FundamentalGroup`](FundamentalGroupoids/FundamentalGroup.lean) | Induced-map and basepoint-equality laws, null-loop/trivial-image criteria, path transport, relative and moving-track homotopy comparisons, and retraction splittings |
| [`Topology.Homotopy.Affine`](FundamentalGroupoids/Topology/Homotopy/Affine.lean) | Affine homotopies fixed on an agreement subset, with evaluation and underlying-homotopy equations |
| [`Topology.Homotopy.HomotopyGroup.Affine`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Affine.lean) | Boundary-relative contraction of generalized loops in real topological vector spaces and subsingleton homotopy quotients for every index type |
| [`Topology.Homotopy.HomotopyGroup.Map`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Map.lean) | Based postcomposition on generalized loops and all homotopy quotients, positive homomorphisms, based-homotopy invariance and fundamental-group compatibility |
| [`Topology.Homotopy.Cube`](FundamentalGroupoids/Topology/Homotopy/Cube.lean) | Zero boundary vertex for nonempty indices and path-connected coordinate-face boundaries for nontrivial indices |
| [`Topology.Covering.GenLoop`](FundamentalGroupoids/Topology/Covering/GenLoop.lean) | Chosen unique based generalized-loop lifts through coverings for nontrivial cube indices, with projection and uniqueness laws |
| [`Topology.Covering.HomotopyGroup`](FundamentalGroupoids/Topology/Covering/HomotopyGroup.lean) | Canonical quotient-map injectivity for nonempty indices, bijectivity and stock multiplicative equivalences for nontrivial indices, with forward and inverse representative formulas |
| [`Topology.Homotopy.Relative`](FundamentalGroupoids/Topology/Homotopy/Relative.lean) | Relative-homotopy precomposition along maps carrying a specified set into the fixed set |
| [`Topology.Category.TopCat.Based`](FundamentalGroupoids/Topology/Category/TopCat/Based.lean) | Based spaces as an under category, based-homotopy congruence and categorical quotient |
| [`Topology.Category.TopCat.Based.Products`](FundamentalGroupoids/Topology/Category/TopCat/Based/Products.lean) | Canonical based product identification with the dependent product and its coordinate equations |
| [`AlgebraicTopology.FundamentalGroup.Circle`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Circle.lean) | Signed-period additive-circle and complex-circle integer coordinates, loop/inverse/endpoint laws, nonidentity generators and homeomorphism compatibility |
| [`AlgebraicTopology.FundamentalGroup.Functor`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Functor.lean) | Fundamental-group functor on based spaces and its unique factorization through based homotopy |
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
| [`AlgebraicTopology.FundamentalGroupoid.OpenCoverInclusions`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCoverInclusions.lean) | All-open inclusion cocone; full-inclusion `Grpd`/`Cat` colimits and strict arbitrary-category descent for indexed covers with binary-intersection-closed range, without connectivity, common-point or finiteness assumptions |
| [`AlgebraicTopology.FundamentalGroup.Product`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Product.lean) | Fundamental-group product equivalence, coordinate and assembled-loop equations |
| [`AlgebraicTopology.FundamentalGroup.Products`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Products.lean) | Preservation of every existing indexed product; canonical comparison, projected-loop and raw-product agreement laws |
| [`AlgebraicTopology.FundamentalGroup.DirectedOpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/DirectedOpenCover.lean) | Inclusion-directed covers and monotone covers on directed preorders: unique compatible homomorphisms to arbitrary monoids and canonical inclusion cocones as `GrpCat` colimits, without path connectedness or intersection closure |
| [`AlgebraicTopology.FundamentalGroup.OpenNhds`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenNhds.lean) | Fundamental-group functor on open neighborhoods and its inclusion cocone |
| [`AlgebraicTopology.FundamentalGroup.OpenCover`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean) | Indexed based van Kampen for intersection-closed covers: unique compatible homomorphisms and `GrpCat` colimits; two-open pushouts; directed-union and common-point simple-connectivity criteria |
| [`SemilocallySimplyConnected.Basic`](FundamentalGroupoids/SemilocallySimplyConnected/Basic.lean) | Chosen-center ambient-null-loop definition, inclusion-image criterion, simply connected spaces and reflection |
| [`SemilocallySimplyConnected.Maps`](FundamentalGroupoids/SemilocallySimplyConnected/Maps.lean) | Local-homeomorphism preservation, covering equivalence and surjective global descent |
| [`SemilocallySimplyConnected.LocallyPathConnected`](FundamentalGroupoids/SemilocallySimplyConnected/LocallyPathConnected.lean) | Open path-connected refinement with ambient nullhomotopies at all basepoints |
| [`Topology.Path`](FundamentalGroupoids/Topology/Path.lean) | Path corestriction, its inclusion and concatenation equations, and based homotopies in subspaces |
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

The APIs retain Mathlib's namespaces and original structures. Based homotopies
fix the selected point throughout time. An unbased homotopy instead compares
induced fundamental-group homomorphisms by transport along the point's track,
not equality at a fixed basepoint. Strict descent uses equality, including
`eqToHom` transports, not compatibility only up to
natural isomorphism. Its space, index, target-object and target-hom universes
are independent; bundled colimits have sizes `Grpd.{u, u}` and `Cat.{u, u}`.
The pairwise diagram includes empty intersections, not the empty-family intersection.
The intersection-closed based-group colimit theorem requires a common basepoint
and path-connected members. The directed-cover theorem instead requires
inclusion-directedness, without path connectedness or intersection closure.
Its monotone-cover form uses only inequalities in a directed index preorder,
not all inclusions of presented neighborhoods. These formulations do not assert
a based-group colimit for an arbitrary open cover.
No wedge calculation or covering-space classification is asserted. A monodromy
stabilizer is not in general its permutation kernel; a centralizer is not a group
structure on a fiber.
See [all conventions and boundaries](docs/mathematical-guide.md#conventions-and-limitations).

## References

- J. Peter May, *A Concise Course in Algebraic Topology*, revised author PDF,
  Chapter 1 §§3–5, 7, Chapter 2 §§5, 7–8, Chapter 3 §§2–4, 7 and
  Chapter 9 §§1, 4 (printed pp. 65–67).
  [Author's revised text](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf).
- [Mathlib](https://github.com/leanprover-community/mathlib4) and
  [GroupTheory](https://github.com/FormalFrontier/group-theory).
  See the [guide's references](docs/mathematical-guide.md#references) for scope and dependencies.
- [Restricted Product Duality](https://github.com/FormalFrontier/restricted-product-duality):
  the based-postcomposition definitions and proofs for generalized loops and
  homotopy groups, by Formal Frontier Agents.
- [VectorBundles](https://github.com/FormalFrontier/vector-bundles/blob/9d2d4b48577e873679271aeee0899239d9a835a1/VectorBundles/Topology/FiberBundle/Proper.lean):
  the local closedness and compact-fiber proof pattern for proper bundle projections.

## Credits and license

Authors: Formal Frontier Agents. AI agents contributed Lean formalization,
examples and documentation. May supplies mathematical motivation and arguments;
Mathlib supplies underlying constructions and APIs. Covering formalizations
originate in sphere-topology by Formal Frontier Agents, with retained Apache-2.0
and authorship notices. The signed-period and complex-circle coordinate core also
originates in its [circle formalization](https://github.com/FormalFrontier/sphere-topology/blob/4a2b822f12e7f2b4255dfea5363265277defa35e/SphereTopology/Homotopy/Circle.lean),
using Mathlib's quotient coverings and induced homeomorphism equivalence.
The generalized-loop and homotopy-group map API originates in Restricted Product
Duality by Formal Frontier Agents, retaining its definitions, proofs, names and
Apache-2.0 notice. It uses Roberto Alvarez's homotopy groups, Mark Lavrentyev's
fundamental groups and Shing Tak Lam's homotopies in Mathlib.
Pullback comparisons reuse GroupTheory's orbit–stabilizer
and double-coset constructions. Normalizer quotients compose GroupTheory's
normalizer–automorphism and centralizer APIs with covering monodromy.
The covering properness proof follows the
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
