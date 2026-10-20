# Mathematical guide

Detailed results, API directions, examples and conventions for Fundamental
Groupoids. See the [README](../README.md) for the overview,
[dependency and build instructions](../README.md#building) and
[module catalogue](../README.md#contents).

Fundamental groupoids, categorical endomorphism transport, strict descent along
indexed open covers, and based van Kampen for intersection-closed indexed covers in
Lean. The library extends Mathlib's categories, path-homotopy classes and open-cover
APIs; it introduces no replacement fundamental group, fundamental groupoid or
one-object category.
It also extends Mathlib's covering-space APIs with based lifting, monodromy,
maps of covers and deck-group comparisons.

## Headline results

- **Comparison of endomorphism transports**
  ([`CategoryTheory.Iso.conj_eq_iff_mem_center`](../FundamentalGroupoids/CategoryTheory/Endomorphism/Conjugation.lean)).
  In any category, two isomorphisms `α β : X ≅ Y` induce the same endomorphism
  transport exactly when the relative loop `α.hom ≫ β.inv` is central in `End X`.
  Commutativity of `End X` makes transport independent of the isomorphism.
  In a groupoid, independence of all transports to a fixed, explicitly isomorphic
  target conversely characterizes commutativity. Loop transport agrees with
  Mathlib's `MulAut.conj`.
- **Equivalence with a chosen vertex group**
  ([`CategoryTheory.SingleObj.isEquivalence_functor_id`](../FundamentalGroupoids/CategoryTheory/SingleObj.lean)).
  For a chosen object `x` in a preconnected groupoid, the existing functor
  `SingleObj.functor (MonoidHom.id (End x))` is an equivalence.
  It is full and faithful in every category; only essential surjectivity needs
  the preconnected-groupoid hypothesis.
- **Canonical monodromy of categorical coverings**
  ([`CategoryTheory.Functor.monodromyMulAction_isPretransitive`](../FundamentalGroupoids/CategoryTheory/Groupoid/Covering.lean)).
  For a functor `F : E ⥤ B` with `F.toPrefunctor.IsCovering`, arrow lifting
  defines the canonical left action
  [`F.monodromyMulAction`](../FundamentalGroupoids/CategoryTheory/Groupoid/Covering.lean)
  of `Aut b` on `F.Fiber b` for categories `E` and `B`. If `E` is a
  preconnected groupoid, the action is pretransitive; `B` need only be a category.
  All four object and morphism universes of `E` and `B` are independent.
  No nonempty-fiber, object-surjectivity or base-connectedness assumption is needed.
- **Preconnectedness from categorical monodromy**
  ([`CategoryTheory.Functor.isPreconnected_of_monodromyMulAction_isPretransitive`](../FundamentalGroupoids/CategoryTheory/Groupoid/Covering.lean)).
  For a functor `P : E ⥤ G` with `P.toPrefunctor.IsCovering` and preconnected
  groupoid base `G`, pretransitivity of the canonical `Aut g` action on one
  specified object fiber `P.Fiber g` implies `IsPreconnected E`. The total
  category needs only its original category structure. All four object and
  morphism universes are independent; no nonempty-total, nonempty-fiber or
  object-surjectivity assumption is required.
- **The category-of-elements projection is a quiver covering**
  ([`CategoryTheory.Functor.Elements.π_isCovering`](../FundamentalGroupoids/CategoryTheory/Groupoid/Elements.lean)).
  For any `F : G ⥤ Type w` with `[Category.{v} G]` and `[IsGroupoid G]`,
  Mathlib's projection `Functor.Elements.π F` is a covering of the underlying
  quivers. The object universe of `G`, its morphism universe and `w` are
  independent. No nonemptiness, connectedness or object-surjectivity hypothesis
  is required.
- **Fibers of a category-of-elements projection recover functor values**
  ([`CategoryTheory.Functor.Elements.fiberEquiv`](../FundamentalGroupoids/CategoryTheory/Groupoid/Elements.lean)).
  For a type-valued functor on any category, the strict object fiber over `g` is
  equivalent to `F.obj g`. Given a covering proof for the projection,
  `fiberEquiv_coveringLiftTarget` identifies canonical lift targets with `F.map f`,
  and `fiberEquiv_monodromyMulAction_smul` identifies its canonical left monodromy
  with `F.map a.hom`. The three universes are independent; no nonemptiness or
  connectedness assumption is required.
- **Components of categories of elements as type colimits**
  ([`CategoryTheory.Functor.elementsConnectedComponentsEquivColimitType`](../FundamentalGroupoids/CategoryTheory/Elements/ConnectedComponents.lean)).
  For any `X : C ⥤ Type w` on a category `[Category.{v} C]` with `C : Type u`,
  `ConnectedComponents X.Elements ≃ X.ColimitType`. The object, morphism and
  value universes are independent; no smallness, nonemptiness or connectedness
  assumption is needed. Both directions compute on representatives and the
  equivalence is natural in `X`. When `[Limits.HasColimit X]` is supplied,
  `elementsConnectedComponentsEquivColimit` instead identifies the components
  with `Limits.colimit X` in `Type w`, with the same representative equations
  and naturality for diagrams having individual colimits.
- **Path connectedness and categorical connectedness**
  ([`FundamentalGroupoid.pathConnectedSpace_iff_isConnected`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Connected.lean)).
  A topological space is path connected if and only if its fundamental groupoid
  is connected, with nonemptiness on both sides. No local path connectedness or
  separation condition is needed.
- **Fundamental groupoids of arbitrary topological coproducts**
  ([`FundamentalGroupoidFunctor.sigmaComparison_isEquivalence`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Coproduct.lean)).
  The inclusion-induced comparison from `Σ i, FundamentalGroupoid (X i)` to
  `FundamentalGroupoid (Σ i, X i)` is an equivalence of categories.
  The index and space universes are independent; no connectedness,
  local path connectedness or nonempty-summand assumptions are needed.
- **Fundamental groupoids of arbitrary dependent products**
  ([`FundamentalGroupoidFunctor.piProductIso`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Product.lean)).
  For `I : Type u` and `X : I → TopCat.{v}` with independent universes,
  there is an isomorphism in `Grpd` from
  `Grpd.of (∀ i, FundamentalGroupoid (X i))` to
  `Grpd.of (FundamentalGroupoid (∀ i, X i))`.
  Its forward functor `piAssembly` assembles coordinate points and path classes;
  its inverse is the family of coordinate projection functors `piProj`.
  For `X : I → TopCat.{u}`, projection, assembly and the isomorphism agree
  by equality with Mathlib's `proj`, `piToPiTop` and `piIso`, respectively.
- **Fundamental groups of arbitrary dependent products**
  ([`FundamentalGroup.piMulEquiv`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Product.lean)).
  For `I : Type u`, spaces `X i : Type v` and basepoints `p i`, with independent
  universes, the fundamental group of `∀ i, X i` is multiplicatively equivalent
  to `∀ i, FundamentalGroup (X i) (p i)`. Coordinate maps are induced by
  evaluation, and the inverse assembles loop classes. Characteristic equations
  describe both directions on loop representatives, with the original
  endomorphism and pointwise group operations. The equivalence commutes with
  families of continuous maps and arbitrary reindexing functions, using image
  basepoints. No finiteness, nonempty-index or connectedness hypothesis is required.
- **Generation by small paths**
  ([`FundamentalGroupoid.morphismProperty_of_isOpenCover`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCover.lean)).
  For an indexed open cover, a composition-stable morphism property holding on
  every local inclusion image holds on every global arrow. Separate identity
  and inverse stability, connectedness and faithful inclusion are unnecessary.
  The local images generate all arrows under multiplicative closure.
  Objectwise components natural on those images extend to a unique natural
  transformation between global functors into any category.
- **Constructed strict open-cover descent and colimits**
  ([`FundamentalGroupoid.descOfIsOpenCover`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/OpenCoverDescent.lean)).
  Local functors agreeing by equality on every ordered pairwise intersection
  extend to a uniquely determined global functor into any category.
  Restriction and uniqueness are equalities, not merely natural isomorphisms.
  The inclusion cocones are colimits in Mathlib's `Grpd` and `Cat`.
- **Based van Kampen for indexed covers: unique compatible homomorphism**
  ([`FundamentalGroup.existsUnique_hom_of_isOpenCover_of_infClosed`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean)).
  Let `U` be an arbitrarily indexed cover of `X` by open neighborhoods of a
  common point `x`, with `X : Type u` and index type `I : Type v`. Assume each
  member is path connected and `InfClosed (Set.range U)`. This means closure
  under binary, equivalently nonempty finite, intersections, without requiring
  `X` itself in the range. For any group `G : Type w`, with `u`, `v` and `w`
  independent, compatible `MonoidHom`s from the local fundamental groups extend
  uniquely to a `MonoidHom` from `π₁(X, x)`. Compatibility is along every
  inclusion between presented neighborhoods, including repeated opens.
- **Based van Kampen for indexed covers: colimit of groups**
  ([`FundamentalGroup.isColimitOfIsOpenCover`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean)).
  Under the same hypotheses, the inclusion cocone is a colimit in `GrpCat.{u}`.
  The family diagram is the precomposition of the canonical
  [`FundamentalGroup.openNhdsFunctor x`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenNhds.lean)
  with `CategoryTheory.inducedFunctor U`; its cocone is obtained by whiskering
  `FundamentalGroup.openNhdsCocone x` along that functor.
- **Based van Kampen for two opens: unique compatible homomorphism**
  ([`FundamentalGroup.existsUnique_hom_of_isOpenCover`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean)).
  Let `X : Type u` be a topological space, `U V : Opens X`, `U ⊔ V = ⊤`,
  and `p : ↑(U ⊓ V)`. Assume the sets `U`, `V` and `U ∩ V` are each
  `IsPathConnected`. Write `iU : U ∩ V → U`, `iV : U ∩ V → V`,
  `jU : U → X` and `jV : V → X` for the continuous inclusions, and `pU`, `pV`
  for the images of `p`. For any `G : Type v` with `[Group G]`, independently
  of `u`, homomorphisms `φU : π₁(U, pU) →* G` and `φV : π₁(V, pV) →* G`
  satisfying `φU.comp (iU_*) = φV.comp (iV_*)` admit a unique
  `φ : π₁(X, p.1) →* G` satisfying **both** equations
  `φ.comp (jU_*) = φU` and `φ.comp (jV_*) = φV`.
  Here `π₁` is Mathlib's `FundamentalGroup`, homomorphisms are `MonoidHom`s,
  and `f_*` is `FundamentalGroup.map f` at the displayed basepoint.
- **Based van Kampen for two opens: pushout of groups**
  ([`FundamentalGroup.isPushout_of_isOpenCover`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCover.lean)).
  Under the same cover, set path-connectedness and common-basepoint hypotheses,
  the same four induced inclusion homomorphisms, bundled by `GrpCat.ofHom`,
  form an `IsPushout` square in `GrpCat.{u}`:
  `π₁(U ∩ V, p) → π₁(U, pU)` and `π₁(V, pV) → π₁(X, p.1)`
  are its horizontal maps, with vertical maps induced by `iV` and `jU`.

The two-open results specialize the based-group colimit theorem. They reuse
strict groupoid descent by choosing paths compatibly on the intersection before
restricting to based loops. Neither the two-open nor the indexed results assume
ambient or local path connectedness; ambient path connectedness follows from the
cover hypotheses. For the indexed results, nonemptiness of the index type and
path connectedness of pairwise intersections are also consequences of the
hypotheses, and the index type need not be finite.

### Covering spaces

- **Based lifting and equivalence of covers**
  ([`Lifting`](../FundamentalGroupoids/Topology/Covering/Lifting.lean),
  [`Equivalence`](../FundamentalGroupoids/Topology/Covering/Equivalence.lean)).
  For a continuous map from a path-connected, locally path-connected domain and
  a prescribed lift of its basepoint, a unique based lift exists exactly when
  its induced fundamental-group image lies in the covering map's image, using
  the basepoint equality to compare them.
  For two covers of a fixed base with path-connected total spaces, equality of
  their fundamental-group images at points over the same basepoint constructs
  a homeomorphism over the base taking one point to the other. Only the source
  total space must be locally path connected. Neither result requires base
  connectedness or global surjectivity of the covers.
- **Monodromy stabilizers, joinedness and fiber maps**
  ([`Monodromy`](../FundamentalGroupoids/Topology/Covering/Monodromy.lean)).
  A loop fixes a fiber point exactly when it lies in the based total-space
  fundamental-group image; two fiber points share a monodromy orbit exactly
  when they are joined by a path. These statements need no connectedness or
  local path connectedness. Over a path-connected base, path connectedness of
  the total space is equivalent to nonemptiness and pretransitive monodromy.
  Continuous maps over the base restrict to equivariant fiber maps
  (`IsCoveringMap.fiberMap`), without connectivity assumptions, preserving
  identities and composition.
- **Monodromy orbit classes and path components**
  ([`Components`](../FundamentalGroupoids/Topology/Covering/Components.lean)).
  For any `cov : IsCoveringMap p` with `p : E → B` and `b : B`,
  `cov.monodromyOrbitEquivZerothHomotopyFiber b` identifies monodromy orbit
  classes in `p ⁻¹' {b}` with the fiber of
  `π₀(p) : ZerothHomotopy E → ZerothHomotopy B` over `ZerothHomotopy.mk b`.
  It sends the class of a fiber point to its component, retaining
  `cov.monodromyOrbitEmbeddingZerothHomotopyFiber b` as its forward embedding.
  Here `π₀(p)` is Mathlib's `Quotient.map` on the path setoids.
  No base or total-space path connectedness is needed. Moreover,
  `IsCoveringMap.image_pathComponent` gives
  `p '' pathComponent e = pathComponent (p e)` for every `e : E`.
  For a covering map `p : E → B` over a path-connected base and `b : B`,
  `IsCoveringMap.monodromyOrbitEquivZerothHomotopy` identifies the monodromy orbit
  quotient of `p ⁻¹' {b}` with `ZerothHomotopy E`, sending the class of a fiber
  point to its path component. The total and base universes are independent;
  the total space may be empty, with no local path connectedness or global
  surjectivity assumption on the covering map.
- **Pullback fibers, monodromy and path components**
  ([`Pullback`](../FundamentalGroupoids/Topology/Covering/Pullback.lean)).
  For coverings `f₁ : E₁ → B` and `f₂ : E₂ → B`, the map
  `z ↦ f₁ z.fst` from `Function.Pullback f₁ f₂` to `B` is a covering.
  `Function.Pullback.fiberEquiv` identifies its fiber over `b` with
  `(f₁ ⁻¹' {b}) × (f₂ ⁻¹' {b})`, intertwining canonical monodromy with
  the diagonal product action. The total and base universes are independent.
  When `B` is path connected, `IsCoveringMap.pullbackProdOrbitEquivZerothHomotopy`
  identifies diagonal fiber orbits with the pullback's path components;
  neither total space is required to be path connected or nonempty.
- **Double cosets of fundamental-group images**
  ([`PullbackDoubleCoset`](../FundamentalGroupoids/Topology/Covering/PullbackDoubleCoset.lean)).
  When both `E₁` and `E₂` are path connected and points `eᵢ : fᵢ ⁻¹' {b}`
  are specified, `IsCoveringMap.pullbackZerothHomotopyEquivDoubleCoset`
  identifies path components of the pullback with `H \ G / K`, where
  `G = FundamentalGroup B b` and `H`, `K` are the ranges of
  `FundamentalGroup.mapOfEq ⟨fᵢ, covᵢ.continuous⟩ eᵢ.2`.
  No path connectedness of `B` is needed. The component of
  `(γ • e₁, δ • e₂)` corresponds to `H (γ⁻¹ * δ) K`, and `H g K`
  maps back to the component of `(e₁, g • e₂)`.
- **Maps of covers from equivariant fiber maps**
  ([`DeckMonodromy`](../FundamentalGroupoids/Topology/Covering/DeckMonodromy.lean)).
  Restriction to a chosen fiber identifies continuous over-maps with Mathlib's
  `MulActionHom`s when the base is path connected and the source is locally
  path connected, allowing empty or disconnected source total spaces. Alternatively, a supplied
  source point and a path-connected, locally path-connected source suffice,
  without base connectedness. Neither version requires connectivity or local
  path connectedness of the target. These are equivalences of map spaces;
  individual fiber maps need not be bijections.
- **Deck actions and fixed-point rigidity**
  ([`DeckGroup`](../FundamentalGroupoids/Topology/Covering/DeckGroup.lean)).
  The deck group acts on every point fiber. For a separated, locally injective
  map with preconnected total space, evaluation at a supplied point embeds the
  deck group into its fiber, so a deck transformation fixing a point is the
  identity. No topology on the codomain is needed, and evaluation is not
  asserted to be surjective.
- **Deck groups as monodromy centralizers**
  ([`DeckMonodromy`](../FundamentalGroupoids/Topology/Covering/DeckMonodromy.lean)).
  Restriction to a chosen fiber gives a homomorphism to the centralizer of the
  monodromy image in its permutation group, without connectivity assumptions.
  It is injective over a path-connected base, without local path connectedness.
  If the total space is also locally path connected, it is a multiplicative
  equivalence, including empty or disconnected total spaces. The alternative
  with path-connected, locally path-connected total space uses the fiber over
  a supplied point's image and needs no base connectedness.

#### Cardinalities of fibers

The [`Cardinality`](../FundamentalGroupoids/Topology/Covering/Cardinality.lean) module
contains `IsCoveringMap.isLocallyConstant_cardinalMk_fiber`:
for a covering map `p : E → B`, the function
`fun b : B ↦ Cardinal.mk (p ⁻¹' {b})` is locally constant. The total and base
universes are independent. The statement uses the point fibers and
preserves infinite and empty cardinalities, without finiteness, path connectedness,
local path connectedness, surjectivity or nonempty-total assumptions.

For the constancy consequences on a preconnected subset or base, Mathlib already
provides `IsLocallyConstant.apply_eq_of_isPreconnected`,
`IsLocallyConstant.apply_eq_of_preconnectedSpace` and `IsLocallyConstant.eq_const`.
Local constancy does not assert equality of all fiber cardinalities over an
arbitrary disconnected base.

## Fundamental groupoids of topological coproducts

The [`Coproduct`](../FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Coproduct.lean)
module constructs `FundamentalGroupoidFunctor.sigmaComparison X` for arbitrary
`ι : Type v` and `X : ι → Type u` with supplied topologies and independent
universes. Its source is the stock categorical sigma
`Σ i, FundamentalGroupoid (X i)`; its target is the original fundamental
groupoid of the topological sigma `Σ i, X i`. The functor is exactly
`CategoryTheory.Sigma.desc` of
`FundamentalGroupoid.map (ContinuousMap.sigmaMk i)`.

The object and component-arrow equations are `sigmaComparison_obj` and
`sigmaComparison_map_mk`. The restriction natural isomorphism
`sigmaComparisonInclIso` reuses `CategoryTheory.Sigma.inclDesc`, and
`sigmaComparison_obj_bijective` proves bijectivity on the original object
carriers. Functor identity and composition laws come from the existing descent
and induced-map constructions. There is no connectedness, local path
connectedness, nonemptiness, finiteness, separation, compact-generation or
basepoint hypothesis; empty indices and empty summands are allowed.

The theorem `sigmaComparison_isEquivalence` establishes that this canonical
comparison is an equivalence. Mathlib's connected-source factorization into a
sigma type applies to the interval and its square: every path lies in one
summand, and a homotopy between paths in a summand stays in that summand.
Recovering the endpoints and relative boundary gives fullness and faithfulness
on the original path-homotopy quotients. Object surjectivity then completes the
proof. The theorem is not a registered instance; after installing it locally,
Mathlib's `Functor.asEquivalence` supplies equivalence data. No coproduct
naturality theorem is asserted. The comparison is derived support for May's
all-points groupoid and disjoint-union viewpoint (Chapter 2, §§5–6), not a named
theorem quoted from his book.

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

For induced fundamental-group maps, the
[`FundamentalGroup`](../FundamentalGroupoids/FundamentalGroup.lean) module supplies
`map_id` and `map_comp` (using the image basepoint in composition), together
with compatibility with path transport and homotopies. Use `map_fundamentalGroupMulEquivOfPath` for a loop and
`map_comp_fundamentalGroupMulEquivOfPath` for the homomorphism square. For a
homotopy `H`, `fundamentalGroupMulEquivOfPath_map_of_homotopy` compares the maps
by transport along `H.evalAt x`; its homomorphism form is
`fundamentalGroupMulEquivOfPath_comp_map_of_homotopy`. These comparisons impose
no basedness or connectedness condition.

For pointed products, import
`FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Product` and use
`FundamentalGroup.piMulEquiv p`. The lemmas `piMulEquiv_apply` and
`piMulEquiv_symm_apply` compute coordinate evaluation and loop assembly;
`piMulEquiv_fromPath` and `piMulEquiv_symm_fromPath` give their equations on
loop representatives. Use `piMulEquiv_naturality` for families of continuous
maps and `piMulEquiv_reindex` for arbitrary reindexing functions, with image
basepoints as displayed in their statements.

For a type-valued diagram on any category, import
`FundamentalGroupoids.CategoryTheory.Elements.ConnectedComponents` and use
`X.elementsConnectedComponentsEquivColimitType`. Its `_apply` and `_symm_apply`
lemmas compute the two representative maps. `NatTrans.mapColimitType` has
`_ι`, `_id` and `_comp` lemmas, and
`Functor.elementsConnectedComponentsEquivColimitType_natural` compares it with
Mathlib's `NatTrans.mapElements` followed by `Functor.mapConnectedComponents`.
With an individual colimit instance, use `X.elementsConnectedComponentsEquivColimit`
and its representative and naturality lemmas. These are equivalences of types,
not equivalences of the elements category with a discrete category.

For a path-connected space and chosen point `x`, apply `Functor.asEquivalence` to
`SingleObj.functor (MonoidHom.id (End (FundamentalGroupoid.mk x)))`.
The [interval client](../FundamentalGroupoidsTest/AlgebraicTopology/FundamentalGroupoid/Connected.lean)
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

For based van Kampen, import
`FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover`.
For an intersection-closed indexed cover, use
`FundamentalGroup.existsUnique_hom_of_isOpenCover_of_infClosed` for `MonoidHom`s,
or `FundamentalGroup.isColimitOfIsOpenCover` for the whiskered inclusion cocone
and its `IsColimit.desc`, `fac` and `uniq` interface.
For the two-open formulation, supply the cover equation, the three set
path-connectedness proofs and `p` to
`FundamentalGroup.existsUnique_hom_of_isOpenCover`, followed by `G`, `φU`, `φV`
and their compatibility equation. Its unique homomorphism satisfies the two
restriction equations above. For categorical use, apply
`FundamentalGroup.isPushout_of_isOpenCover` to the same geometric data, then use
its `IsPushout` interface. The [circle-cylinder example](../FundamentalGroupoidsTest/AlgebraicTopology/FundamentalGroup/OpenCover.lean)
illustrates both formulations.

The canonical indexed-cover colimit name is `FundamentalGroup.isColimitOfIsOpenCover`.
The deprecated spelling `FundamentalGroup.isColimit_of_isOpenCover` remains a
compatibility alias; use the canonical name in new code.

### Covering imports and compatibility with sphere-topology

Import the covering modules individually as
`FundamentalGroupoids.Topology.Covering.Lifting`, `Equivalence`, `Monodromy`,
`Components`, `Pullback`, `PullbackDoubleCoset`, `Cardinality`, `DeckGroup` or
`DeckMonodromy`, with the same prefix for each. They extend
Mathlib's covering maps, monodromy actions and deck groups rather than defining
replacement structures.

Without base path connectedness, use
`cov.monodromyOrbitEquivZerothHomotopyFiber b` to identify orbit classes with the
fiber of the induced path-component map over `ZerothHomotopy.mk b`. Its `_apply`
and `_symm_apply` lemmas compute both directions on fiber-point representatives;
`_val_apply` gives the underlying component. The `_toEmbedding` lemma identifies
its forward embedding with `cov.monodromyOrbitEmbeddingZerothHomotopyFiber b`.
Use `cov.image_pathComponent e` for
`p '' pathComponent e = pathComponent (p e)`.

For a path-connected base, use `cov.monodromyOrbitEquivZerothHomotopy b` to
compare orbit classes and path components. Its `_apply` and `_symm_apply` lemmas
compute both directions on fiber-point representatives.

The generic covering API was relocated from
[sphere-topology](https://github.com/FormalFrontier/sphere-topology), with
**the same declaration names**. A Fundamental Groupoids release containing these
modules **cannot be co-imported with a legacy sphere-topology release that still
defines its own copies**. Joint consumers must use the subsequent sphere-topology
shim release, whose old covering modules publicly import the new modules, and a
compatible `fundamental-groupoids` pin **together**. Release order does not make
arbitrary version pairs compatible; existing dependency pins are not upgraded
automatically.

## Examples and boundaries

The clients under [`FundamentalGroupoidsTest`](../FundamentalGroupoidsTest.lean)
exercise the advertised interfaces:

- For the constant `Bool` functor on `Discrete PUnit`, the two values determine
  distinct components of its category of elements despite having the same
  underlying base object. A `Bool`-valued cocone and the components/type-colimit
  equivalence distinguish them. Diagrams on `Discrete PEmpty` have empty
  components and empty quotient-type colimits; no nonemptiness is required.
- On `AddCircle (1 : ℝ)`, translation by half a period moves the basepoint
  through a homotopy. A nonidentity loop chosen through Mathlib's covering-group
  coordinate remains nonidentity under the transport and map comparisons. This
  concerns the loop classes, not a nonidentity transport automorphism; the circle's
  fundamental group is abelian.
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
- The [circle cylinder](../FundamentalGroupoidsTest/AlgebraicTopology/FundamentalGroup/OpenCover.lean)
  `AddCircle (1 : ℝ) × ℝ` has proper open strips `U = {t < 1}` and
  `V = {-1 < t}`, with common basepoint `(0, 0)` and path-connected intersection
  `{-1 < t < 1}`. Projection to the circle retracts the zero-height section on
  the intersection, each strip and the cylinder. A specified nonidentity circle
  class from the quotient covering `ℝ → AddCircle 1` gives a nonidentity
  fundamental-group class in each of these four spaces. The inclusions take the
  intersection class to both strip classes and both strip classes to the same
  nonidentity cylinder class; the retractions recover the circle class.
  These geometric and group-theoretic facts are established independently of the
  open-cover universal properties, which are then applied in both forms.

## Conventions and limitations

Production declarations retain Mathlib's mathematical namespaces
`CategoryTheory.Iso`, `CategoryTheory.SingleObj`, `FundamentalGroupoid` and
`FundamentalGroup`.
The covering modules use `IsCoveringMap`, `IsQuotientCoveringMap` and `deck`.
For an arrow in one chart, the descent map is the local map conjugated by
`eqToHom` of its object-value equalities. Chart compatibility is strict;
compatibility given only by natural isomorphisms is not an input to this API.

The space, cover index, target-object and target-hom universes are independent
in the arbitrary-category descent theorem. The bundled colimits lie in
`Grpd.{u, u}` and `Cat.{u, u}`. The pairwise diagram has chart objects and
ordered pairwise-intersection objects, including empty intersections, but no
object for an intersection of the empty family. No connectedness,
inhabited-intersection, nonempty-target or faithful-inclusion condition is assumed.

Arbitrary-cover descent concerns all-point groupoids without connectedness
conditions. The indexed based-group results require a common basepoint,
path-connected members and an intersection-closed range; they do not assert a
based-group colimit for arbitrary open covers. No wedge calculation or
covering-space classification is asserted.
The small-path module on its own proves generation and naturality, not functor
descent. The translation example does not assert nonidentity chart-object casts.
A monodromy point stabilizer is not generally the kernel of its permutation
representation. The deck centralizer is a subgroup of the permutation group of
a fiber, not a group structure on that fiber.

## References

- J. Peter May, *A Concise Course in Algebraic Topology*, revised author PDF,
  Chapter 1, §3 and Chapter 2, §§5, 7 (the groupoid and based-group colimit
  discussions are on printed pp. 17–19). [Author's revised text](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf).
  Published by the University of Chicago Press. The categorical transport
  results and the arbitrary-cover, arbitrary-category descent statements
  generalize the corresponding topological results. The indexed based van Kampen
  statements give the common-basepoint, intersection-closed formulation, with the
  two-open pushout as a specialization.
  Chapter 3, §§2–4, 7 supplies the covering-space lifting and monodromy arguments.
  The categorical preconnectedness criterion is a derived consequence of the
  fiber-translation argument in §4, rather than a theorem stated there.
- [Mathlib](https://github.com/leanprover-community/mathlib4), especially its
  fundamental groupoid, conjugation, one-object category, open-cover,
  interval-subdivision, subpath, morphism-property and colimit APIs, as well as
  covering maps, lifting, monodromy, deck groups and equivariant maps.
- [GroupTheory](https://github.com/FormalFrontier/group-theory), by Formal
  Frontier Agents: orbit–stabilizer equivariance and the equivalence between
  diagonal orbits of products of coset spaces and double cosets.

## Credits and license

Authors: Formal Frontier Agents. AI agents contributed Lean formalization,
examples and mathematical documentation. May supplies mathematical motivation
and arguments; Mathlib supplies the underlying constructions and APIs.
Individual Mathlib contributions used in the proofs are credited in the module
documentation and [CONTRIBUTORS.md](../CONTRIBUTORS.md).
The pullback component comparisons reuse GroupTheory's independent-universe
orbit–stabilizer equivariance and product-coset orbit/double-coset constructions,
formalized by Formal Frontier Agents.
The covering-space formalizations originate in
[sphere-topology](https://github.com/FormalFrontier/sphere-topology) by Formal
Frontier Agents, retaining their Apache-2.0 and authorship notices. They build on
Junyan Xu's covering-space lifting and monodromy and Kim Morrison's deck-group
formalizations in Mathlib, with further credits in the module documentation.
The coproduct proof uses Johannes Hölzl, Mario Carneiro and Yury Kudryashov's
connected-source sigma factorization in Mathlib. The comparison reuses Bhavik
Mehta's categorical sigma descent,
Shing Tak Lam's fundamental groupoid and induced maps, Nicolò Cavalleri's
continuous-map API, and the topology constructions of Johannes Hölzl, Mario
Carneiro and Patrick Massot in Mathlib. Its object bijectivity uses existing
underlying-type equivalences, not a new categorical equivalence construction.
The components-of-elements equivalences, naturality proofs and verification
examples are by Formal Frontier Agents. They build on Kim Morrison and Joël Riou's
category of elements, Bhavik Mehta's connected components, and Joël Riou, Kim
Morrison and Reid Barton's type-colimit formalizations in Mathlib.
No open redistribution license is inferred for May's author-hosted book; no
book excerpts or PDF assets are included.
Licensed under Apache-2.0; see [LICENSE](../LICENSE).
