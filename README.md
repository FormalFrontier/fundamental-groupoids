# Fundamental Groupoids

Fundamental groupoids, based homotopy, compact-open generalized-loop spaces,
ordinary compact-open endpoint paths and homotopy fibers, relative affine
homotopies, categorical endomorphism transport, strict open-cover
descent, based van Kampen, covering spaces and semilocal simple connectivity in
Lean. The library extends Mathlib's categories, path-homotopy classes and covering
maps rather than introducing replacement structures. The
[mathematical guide](docs/mathematical-guide.md) gives detailed statements, API
directions, examples, conventions and credits.

## Headline results

- **Homotopy invariance of ordinary homotopy fibers.** For topological spaces `E` and
  `B`, continuous maps `f g : C(E, B)`, a specified homotopy
  `H : ContinuousMap.Homotopy f g`, and any `b : B`,
  `ContinuousMap.HomotopyFiber.homotopyEquiv H b` constructs an unbased
  homotopy equivalence `HomotopyFiber f b ≃ₕ HomotopyFiber g b`. The forward map
  retains the `E`-point and appends the path traced by `H` after the whole supplied
  path; the inverse appends its reverse. The named inverse homotopies retain the
  `E`-point at every time. No separation or local-compactness assumptions on `E` or
  `B` are required. See [homotopy invariance](FundamentalGroupoids/Topology/Homotopy/Fiber/Homotopy.lean).

- **Point-wide-pushout coproducts up to based homotopy** ([`Based.Coproducts`](FundamentalGroupoids/Topology/Category/TopCat/Based/Coproducts.lean)).
  A family `D : J → BasedTopCat.{max u w}`, indexed by `J : Type w`, has a
  point-wide-pushout cofan with explicit descent and uniqueness, both in based
  spaces and after quotienting based maps by homotopies fixing the point at
  every time. Two based maps from this wedge represent the same class exactly
  when all factor restrictions do. The colimit data retain the mapped composite
  diagram; the binary specialization uses its explicit comparison isomorphism.
  Empty families give initial objects. No separation, local compactness of the
  spaces, finiteness of the index, or condition on the basepoints is required.
- **Strict ordered finite-wedge comparisons** ([`Based.FiniteWedge`](FundamentalGroupoids/Topology/Category/TopCat/Based/FiniteWedge.lean)).
  For `D : Fin 2 → BasedTopCat.{u}`, the finite wedge is isomorphic in based
  spaces to the binary wedge, sending `0` to the left and `1` to the right.
  For `D : Fin 3 → BasedTopCat.{u}`, both nested binary wedges flatten
  isomorphically to the three-factor wedge, preserving leaf order `0`, `1`, `2`.
  Forward and inverse leg equations and common-point preservation characterize
  the comparisons. The factors may differ in an arbitrary common universe,
  without separation, connectedness, local compactness or basepoint conditions.
  The existing `homotopyQuotient.mapIso` gives their based-homotopy images.
- **Chosen finite products in the opposite based-homotopy category** ([`Based.Cartesian`](FundamentalGroupoids/Topology/Category/TopCat/Based/Cartesian.lean)).
  The ordinary opposite of `BasedTopCat.HomotopyCategory` has explicit terminal
  and binary limit cones, given by the opposite empty and ordered two-factor
  based wedges. The named cartesian monoidal structure uses these choices;
  its unit, tensor, two projections and map to the unit have characteristic
  equations. The projections preserve the left/right order of the wedge
  inclusions. For `D : Fin 3 → BasedTopCat.{u}`, the unop of the associator
  followed by the quotient image of left-nested flattening equals the quotient
  image of right-nested flattening, preserving the ordered leaves `0`, `1`, `2`.
  No global cartesian or monoidal instance is installed.
- **Point-family maps and universe lifting** ([`WidePushout.PointMap`](FundamentalGroupoids/Topology/Category/TopCat/Limits/WidePushout/PointMap.lean),
  [`WidePushout.ULift`](FundamentalGroupoids/Topology/Category/TopCat/Limits/WidePushout/ULift.lean),
  [`Based.ULift`](FundamentalGroupoids/Topology/Category/TopCat/Based/ULift.lean)).
  Point-preserving maps between independently sized families on the same index
  type descend through their point-wide-pushouts, preserving identities and
  composition. For `J : Type w` and `X : J → TopCat.{max u w}` with chosen points,
  the universe lift of its point-wide-pushout is homeomorphic to the
  point-wide-pushout of its lifted factors, with head, factor and inverse
  evaluation laws. Based at the
  lifted head, this gives an isomorphism with the based wedge of the lifted
  pointed factors. Empty families retain the head. No separation or local
  compactness is needed; the point-family and homeomorphism modules are
  independent of based-homotopy constructions.
- **Wide-pushout continuity and homotopy descent** ([`Limits.Products`](FundamentalGroupoids/Topology/Category/TopCat/Limits/Products.lean),
  [`Limits.WidePushout`](FundamentalGroupoids/Topology/Category/TopCat/Limits/WidePushout.lean),
  [`Homotopy.WidePushout`](FundamentalGroupoids/Topology/Homotopy/WidePushout.lean)).
  A supplied topological colimit has its characteristic continuity criterion after
  product with `P` for maps to `Y` under `LocallyCompactPair P Y`, with independent
  indexing-object, indexing-morphism, diagram, parameter and target universes.
  Wide pushouts of arbitrary continuous attaching maps have a quotient comparison
  and continuous descent to independently universed targets, with head, factor and
  uniqueness equations. Compatible jointly continuous families and `HomotopyLike`
  data descend with their prescribed restrictions at every time. For a point head,
  chosen-point-relative factor homotopies and explicit equality of endpoint maps
  at the head give a unique head-relative homotopy. Empty index families are
  included; no separation or local compactness of the factors or target is required.
- **Unpointed disk attachments** ([`DiskAttachment`](FundamentalGroupoids/Topology/Category/TopCat/DiskAttachment.lean)).
  Arbitrary families of circle maps attach closed complex unit disks, with no
  connectedness or separation assumptions. The continuous-map universal property
  allows independent universes. Continuity on an open or closed subset is tested
  on its preimages in the original space and each disk, without continuity elsewhere.
  Compatible functions have a unique descent to any target type, without a
  continuity requirement; continuous descent has the same underlying function.
  Empty attachments recover the original space; attaching along the identity of the
  boundary recovers the disk. The original inclusion is a closed embedding, and the
  open-disk characteristic maps are open embeddings with mutually disjoint images
  avoiding the original space. Every attaching
  boundary circle induces a trivial fundamental-group homomorphism at every basepoint.
- **Punctured disk attachments** ([`Punctured`](FundamentalGroupoids/Topology/Category/TopCat/DiskAttachment/Punctured.lean),
  [`PuncturedRetraction`](FundamentalGroupoids/Topology/Category/TopCat/DiskAttachment/PuncturedRetraction.lean)).
  For any topological space and arbitrary unbased attaching maps, the disk centres
  form a closed set. Their complement strongly deformation retracts onto the
  original-space image, fixing that image throughout. On each punctured disk,
  the retraction follows its unit direction and the deformation is radial.
  Space and disk-index universes are independent; no connectivity, separation
  or finiteness assumptions are needed.
  The [punctured part of an attachment path component](FundamentalGroupoids/Topology/Category/TopCat/DiskAttachment/PuncturedComponent.lean)
  retracts to the corresponding original-space component through a relative
  deformation. Its [fundamental group](FundamentalGroupoids/FundamentalGroup/DiskAttachment/PuncturedComponent/Basic.lean)
  is isomorphic to that of the original space, with forward map induced by
  retraction followed by component inclusion. The inverse lifts to the
  original-space component and then includes it into the punctured component.
  Neither component is assumed open.
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
- **Maps on path components** ([`PathConnected`](FundamentalGroupoids/Topology/Connected/PathConnected.lean)).
  Every continuous map induces `ZerothHomotopy.map`, preserving representatives,
  identity and composition; homotopic maps induce equal functions. Space universes
  are independent, with no separation or connectedness assumptions.
- **Cube boundaries** ([`Cube`](FundamentalGroupoids/Topology/Homotopy/Cube.lean)).
  For any index type `N` with at least two elements, the coordinate-face boundary of
  `N → I` is path connected, even for infinite `N`. The zero vertex lies in the
  boundary whenever `N` is nonempty. For finite `N`, the boundary is closed,
  including the empty-index cube.
- **Real coordinates on cube-boundary complements** ([`Cube.Coordinates`](FundamentalGroupoids/Topology/Homotopy/Cube/Coordinates.lean)).
  For every index type `N` in any universe, `Cube.boundaryComplHomeomorphPi N`
  identifies the boundary complement, with its subtype topology, with the product
  `N → ℝ`. Each coordinate is increasing, using `t ↦ 2 * t - 1` followed by the
  inverse of Mathlib's `orderIsoIooNegOneOne ℝ`; forward and inverse evaluation
  laws are public. A theorem supplies local compactness for finite `N`.
  Empty and infinite indices are allowed; for infinite cubes this is not an
  ambient-interior description.
- **Open-subspace collapse** ([`OnePoint.Collapse`](FundamentalGroupoids/Topology/Compactification/OnePoint/Collapse.lean)).
  For a Hausdorff space `K` and any open subspace `s`, `OnePoint.collapse s`
  continuously retains the points of `s` and sends its complement to infinity
  in `OnePoint s`, without local compactness of `K`. The extension
  `OnePoint.collapseWithPoint s` from `K ⊕ PUnit` is surjective even when `s` is
  the whole space; for compact `K` it is a quotient map, giving continuous descent
  through Mathlib's quotient-map API to arbitrary topological targets. Neither
  nonemptiness nor properness of `s` is required.
- **Based compact-open collapse comparison** ([`OnePoint.ContinuousMap`](FundamentalGroupoids/Topology/Compactification/OnePoint/ContinuousMap.lean)).
  For a compact Hausdorff space `K`, any open `s` and any topological space `X`
  with a chosen `x : X`, `OnePoint.collapsePullbackHomeomorph s x` identifies
  `{F : C(OnePoint s, X) // F ∞ = x}` homeomorphically with continuous maps
  `K → X` equal to `x` outside `s`. The forward map precomposes with
  `OnePoint.collapse s`; the inverse is `OnePoint.rec x` applied to restriction
  to `s`. Both spaces carry the ordinary compact-open/subtype topology.
  Ambient and target universes are independent; `s` may be empty or all of `K`,
  and `X` needs neither separation nor local compactness. The construction uses
  GroupTheory's compact-covering precomposition embedding API.
- **Ordinary compact-open paths and homotopy fibers** ([`RelativePathSpace`](FundamentalGroupoids/Topology/Homotopy/RelativePathSpace.lean),
  [`Fiber`](FundamentalGroupoids/Topology/Homotopy/Fiber.lean),
  [`Fiber.Const`](FundamentalGroupoids/Topology/Homotopy/Fiber/Const.lean),
  [`Fiber.Contractible`](FundamentalGroupoids/Topology/Homotopy/Fiber/Contractible.lean),
  [`Fiber.Homeomorph`](FundamentalGroupoids/Topology/Homotopy/Fiber/Homeomorph.lean),
  [`Fiber.PathComponent`](FundamentalGroupoids/Topology/Homotopy/Fiber/PathComponent.lean),
  [`Fiber.Prod`](FundamentalGroupoids/Topology/Homotopy/Fiber/Prod.lean),
  [`RelativePathSpace.Contractible`](FundamentalGroupoids/Topology/Homotopy/RelativePathSpace/Contractible.lean)).
  `ContinuousMap.RelativePathSpace b A` consists of paths from an arbitrary `b`
  to any point of `A`; the paths need not stay in `A`, and `b` need not lie in `A`.
  `ContinuousMap.HomotopyFiber f b` retains both a source point `e` and a path
  from `b` to `f e`, with the ordinary product/subtype compact-open topology.
  It is homeomorphic to the pullback of `f` along terminal evaluation. For an
  embedding, forgetting `e` identifies it with paths ending in `Set.range f`;
  for the original subspace inclusion, the endpoint lies in `A` itself.
  Maps act on both point and path, with identity, composition, constant and
  naturality laws. A commuting square of source and target homeomorphisms
  induces `HomotopyFiber.homeomorph eX eY w hy` at specified points satisfying
  `hy : eY y = y'`. Its inverse uses the inverse coordinate homeomorphisms;
  its forward map sends the retained point through `eX` and postcomposes the
  whole path by `eY`, with identity, composition and projection laws.
  All four space universes are independent, without embedding, separation or
  nonemptiness assumptions.
  `HomotopyFiber.prodHomeomorph f g y z` splits the fiber of a product map
  over `(y, z)` into the product of the two fibers, retaining both source points
  and entire paths. Its inverse pairs paths at the same original time. The
  comparison commutes with both projections and is natural for two arbitrary
  continuous squares, with eight independent universes and no separation or
  ambient local-compactness assumptions.
  `HomotopyFiber.compFstHomeomorph (Z := Z) f b` identifies the fiber of
  `f.comp (ContinuousMap.fst : C(X × Z, X))` over `b` with
  `HomotopyFiber f b × Z`. It preserves both source coordinates and the full
  original path, with forward and inverse same-time evaluation and constructor
  laws. Whole continuous-map diagrams describe the first-fiber, free-coordinate,
  point and path projections. Naturality permits any continuous commuting square
  and any continuous map of the free factor, with six independent universes;
  the comparison itself uses three independent universes and arbitrary topologies.
  Empty spaces are allowed. For `f = id`, the full identity-fiber factor remains;
  this is not a homeomorphism from the projection's fiber to `Z` alone.
  A constant fiber point needs a specified `e` with `f e = b`;
  being outside the image does not force the homotopy fiber to be empty.
  For arbitrary `f`, nonemptiness is equivalent to `∃ e, Joined b (f e)`, or
  to membership of `ZerothHomotopy.mk b` in the range of `ZerothHomotopy.map f`.
  The induced path-component map is therefore surjective exactly when every
  homotopy fiber is nonempty. Source and target universes are independent,
  without connectivity assumptions. The retained-point projection has path-component
  image equal to the preimage of `{ZerothHomotopy.mk b}` under
  `ZerothHomotopy.map f`; no injectivity of the component projection is asserted.
  For a constant map with value `c`, `HomotopyFiber.constHomeomorph E b c`
  identifies its fiber with `E × Path b c`, retaining the point and every path
  value, naturally in continuous source maps. The fiber is nonempty exactly when
  both factors are nonempty; an empty source and the full loop factor for `b = c`
  are included, with independent source and target universes.
  For every topological space `X` and chosen `b : X`,
  `RelativePathSpace.contraction b` sends `γ` to `t ↦ γ ((1 - s) * t)` at time
  `s`, fixes the constant path throughout, and gives a `ContractibleSpace`
  instance on `RelativePathSpace b Set.univ`. Its endpoint is free to move.
  `HomotopyFiber.idContraction b` transports this to the identity map's homotopy
  fiber, giving a `ContractibleSpace` instance and fixing its constant-path point.
  At time `s`, the retained source point is `γ (1 - s)` and the whole path is
  `t ↦ γ ((1 - s) * t)`, with its original direction and starting point.
  No target separation or local compactness is required. These are ordinary,
  non-kified spaces, not an identification with May's category `U`; this contracts
  neither loop spaces nor `X`.
- **Homotopy-fiber exactness** ([`Fiber.Exact`](FundamentalGroupoids/Topology/Homotopy/Fiber/Exact.lean)).
  For `f : C(E, B)`, `e₀ : E`, `b : B` and `h : f e₀ = b`, base
  `HF = ContinuousMap.HomotopyFiber f b` at its constant-path point, and let
  `p` retain the source point. For every cube index `N`,
  `HomotopyGroup.range_mapFun_homotopyFiber_point` gives
  `range (π_N p) = (π_N f) ⁻¹' {constant class}`, where `π_N` denotes
  `HomotopyGroup.mapFun` with these point equations. No index instances are
  needed. With `[DecidableEq N] [Nonempty N]`,
  `HomotopyGroup.range_map_homotopyFiber_point` gives the range–kernel form
  for the existing groups and homomorphisms. These instances supply operation
  data, not geometric assumptions. Index and space universes are independent,
  and all topologies are arbitrary.
  For the adjacent position, let `J : C(Path b b, HF)` be the continuous
  composite through `HomotopyFiber.constHomeomorph Unit b b` and
  `HomotopyFiber.map`, retaining `e₀` and the whole forward loop `γ`.
  It sends `Path.refl b` to `HomotopyFiber.const e₀ h`; only the pointwise
  equation `h` is required, not constancy of `f`.
  `HomotopyGroup.range_mapFun_homotopyFiber_loop` gives
  `range (π_N J) = (π_N p) ⁻¹' {constant class}` for every `N`, again without
  index instances. This is exactness at
  `HomotopyGroup N HF (HomotopyFiber.const e₀ h)`.
  With `[DecidableEq N] [Nonempty N]`,
  `HomotopyGroup.range_map_homotopyFiber_loop` gives the subgroup range–kernel
  form for the same maps. The empty-index consequence
  `ZerothHomotopy.range_map_homotopyFiber_loop` is
  `range (π₀ J) = (π₀ p) ⁻¹' {ZerothHomotopy.mk e₀}` on all path components
  of the ordinary topological loop space `Path b b`, not just the component
  of `Path.refl b`. The unpointed zeroth projection formula also allows
  empty `E`, without choosing `e₀` or `h`.
  For continuous `g : C(E', B)` and `u : C(E', E)` with `f (u x) = g x`,
  the induced fiber map `K` over `id B` satisfies
  `range (π₀ K) = (π₀ p) ⁻¹' range (π₀ u)`; `E'` may be empty.
  The loop-class map `δ : π₁B → π₀HF` retains the whole forward loop at `e₀`,
  with image `(π₀ p) ⁻¹' {ZerothHomotopy.mk e₀}` and
  `δ ⁻¹' {δ 1} = Set.range (FundamentalGroup.mapOfEq f h)`.
  These are the positions at `π₀HF` and `π₁B`, distinct from projection
  exactness at `HomotopyGroup N E e₀`. No group structure on `π₀HF` or full
  long exact sequence is supplied. The finite-degree projection and loop-inclusion
  formulas adapt May, Chapter 8 §6, printed pp. 61–62; the all-index statements
  are ordinary-topology cubical extensions, without a sphere-domain or degree-shift
  comparison or an identification with his category `U`. See the
  [exactness guide](docs/mathematical-guide.md#path-component-exactness-for-homotopy-fibers).
- **Finite generalized loops as based compact-open maps** ([`GenLoop.OnePoint`](FundamentalGroupoids/Topology/Homotopy/GenLoop/OnePoint.lean)).
  For every finite index type `N` (`[Finite N]`) and every topological space `X`
  with chosen `x`, `GenLoop.onePointHomeomorph N x` identifies `GenLoop N X x`
  with continuous maps from `OnePoint ((Cube.boundary N)ᶜ)` taking infinity to
  `x`, with the ordinary compact-open/subtype topologies. It keeps the loop's
  values on the coordinate-face boundary complement and assigns `x` at infinity;
  its inverse precomposes with the boundary collapse. Underlying-map and
  evaluation laws characterize both directions of this and the open-subspace
  comparison. Index and target universes are independent; no `Fintype`, decidable
  equality, index nonemptiness, target separation or target local compactness is
  required. For empty `N`, the cube is a singleton with empty boundary, but the
  added infinity is distinct from its cube point, so the based-map space need
  not be a singleton.
- **Coverings on compact-open generalized-loop spaces** ([`GenLoop`](FundamentalGroupoids/Topology/Covering/GenLoop.lean)).
  For a covering `p : E → X`, a chosen `e : E` and any index type `N` with at least
  two elements, `hp.genLoopHomeomorph N e` identifies `GenLoop N E e` with
  `GenLoop N X (p e)` in their ordinary compact-open/subtype topologies. Its forward
  map is `GenLoop.map` and its inverse is the unique chosen based lift `hp.liftGenLoop e`.
  The lift is natural in commuting squares with arbitrary continuous horizontal maps;
  the forward map agrees with `HomotopyGroup.mapFun` on representative classes.
  Cube, total and base universes are independent, without finiteness, decidable equality,
  connectedness, local path connectedness, local compactness, separation or global
  surjectivity assumptions.
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
- **Reindexing cube coordinates** ([`HomotopyGroup.Congr`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Congr.lean)).
  An equivalence `e : N ≃ M` induces `HomotopyGroup.congr x e` on the existing
  boundary-relative quotients, sending `[p]` to `[t ↦ p (t ∘ e)]`.
  The inverse uses `e.symm`; representative, constant, identity, composition
  and based-postcomposition laws are public. Index and space universes are
  independent, and the indices may be empty or infinite. For nonempty indices
  with supplied decidable equality, `HomotopyGroup.congrMulEquiv x e` uses the
  same function with Mathlib's existing group structures. It commutes with
  concatenation along corresponding coordinates, without requiring the two
  group structures to select corresponding axes. This is a cubical transport,
  not a comparison with sphere-domain homotopy classes.
- **Coherent loop iteration** ([`HomotopyGroup.Iteration`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Iteration.lean)).
  The computed comparison `HomotopyGroup.genLoopEquiv N M x` flattens an
  `N`-cube of `M`-loops to an `(N ⊕ M)`-loop using Mathlib's sum-flattening
  homeomorphism on representatives. Its inverse, constant and based-map laws
  are public. For nonempty `N`, with supplied decidable equality on `N` and
  `N ⊕ M`, `genLoopMulEquiv` preserves the existing group operations; `M` may
  be empty. Associativity uses the ordered sum associator, and the two empty
  units retain all inner-loop components or evaluate the empty inner loop.
  `genLoopFinEquiv n m x` orders the outer coordinates before the inner ones,
  with associativity and zero-unit casts in every degree and a multiplicative
  refinement when `n` is positive. Index and space universes are independent.
  These are comparisons of the existing cubical homotopy quotients, not
  sphere-domain or kified mapping-space identifications.
- **Generalized loops and homotopy quotients of dependent products** ([`HomotopyGroup.Product`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Product.lean),
  [`FundamentalGroup.Product`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Product.lean)).
  For arbitrary spaces `X i`, points `p i` and cube index `N`,
  `GenLoop.piHomeomorph N p` is a homeomorphism from generalized loops in the
  ordinary dependent product to the Pi product of coordinate generalized-loop
  spaces, using their inherited compact-open topologies. Its inverse is the
  existing assembler `GenLoop.pi`.
  `HomotopyGroup.piEquiv N p` identifies `HomotopyGroup N (∀ i, X i) p` with
  `∀ i, HomotopyGroup N (X i) (p i)`. Its coordinates are induced by evaluation;
  its inverse assembles loop representatives with `GenLoop.pi`, naturally in
  based coordinate maps. Cube, family and space universes are independent;
  either index may be empty or infinite, without finiteness or decidable-equality
  assumptions. No connectedness, separation or local-compactness hypotheses on
  the spaces are needed; the cube's local compactness is internal to the construction.
  With `[DecidableEq N] [Nonempty N]`,
  `HomotopyGroup.piMulEquiv N p` is multiplicative for Mathlib's existing group
  structures. Under `pi1MulEquivFundamentalGroup`, the degree-one equivalence
  agrees with the existing `FundamentalGroup.piMulEquiv p`, identifying
  `π₁(∀ i, X i, p)` multiplicatively with `∀ i, π₁(X i, p i)`.
  That FundamentalGroup API is natural in continuous coordinate maps and arbitrary
  reindexing. This generalizes May's binary finite-degree product statement
  (Chapter 9 §4, printed p. 67), without a sphere-domain or U-topology comparison.
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
- **Locally compact products** ([`CompactlyGeneratedSpace`](FundamentalGroupoids/Topology/Compactness/CompactlyGeneratedSpace.lean)).
  The ordinary product of two `UCompactlyGeneratedSpace.{u}` spaces is again
  `u`-compactly generated when the first factor is locally compact. For such
  a first factor `P` and an arbitrary topological `A`,
  `Homeomorph.compactlyGeneratedProd` identifies `k_u (P × A)` with `P × k_u A`
  by the identity function in both directions, compatibly with the counits.
  The probe and both space universes are independent, without separation or
  smallness assumptions. This is not an arbitrary-product formula.
- **Closed subspaces under refinement** ([`CompactlyGeneratedSpace`](FundamentalGroupoids/Topology/Compactness/CompactlyGeneratedSpace.lean)).
  Let `κ_u Y` mean `Y` with Mathlib's `compactlyGenerated.{u} Y` topology,
  with continuous identity `ε_u : κ_u Y → Y`. Closed subsets of a
  `UCompactlyGeneratedSpace.{u}` space are `u`-compactly generated in their original
  subtype topology. For any ambient space and closed `s`,
  `Homeomorph.compactlyGeneratedSubtype` identifies `κ_u s` with the subtype `s`
  of `κ_u Y` by unchanged functions in both directions. This homeomorphism and
  preservation of closed embeddings require no ambient compact generation or
  separation. The forward comparison and restricted counit exist for every subset;
  no such inheritance or homeomorphism is asserted for arbitrary subspaces,
  nor preservation of arbitrary embeddings.
- **Fixed-evaluation fibers under refinement** ([`Homotopy.CompactlyGenerated`](FundamentalGroupoids/Topology/Homotopy/CompactlyGenerated.lean)).
  For arbitrary spaces `A`, `X` and points `a : A`, `x : X`, assume only
  `IsClosed ({x} : Set X)`. Give `M = C(A, X)` its original compact-open topology,
  `P = {F : M // F a = x}` its original subtype topology, and
  `Q = {F : κ_u M // (ε_u F) a = x}` the subtype topology inside `κ_u M`.
  `Homeomorph.compactlyGeneratedEvalFiber` gives `κ_u P ≃ₜ Q`, with unchanged
  evaluations in both directions and counit laws. It is separately natural under
  `f : C(A', A)` with `f a' = a` and `g : C(X, Y)` with `g x = y`.
  The second homeomorphism for postcomposition needs `{y}` closed; these maps do not.
  Probe and all space universes are independent. No compact generation, local
  compactness, separation, countability or smallness of the spaces is required.
  This refines the function space, not the codomain as in `C(A, κ_u X)`;
  it asserts no `P ≃ₜ Q`, exponential law, joint composition continuity or
  arbitrary-product closure.
- **Path components under refinement** ([`Homotopy.CompactlyGenerated`](FundamentalGroupoids/Topology/Homotopy/CompactlyGenerated.lean)).
  `ZerothHomotopy.bijective_map_compactlyGeneratedCounit` gives a bijection on
  path components for every topological space. Its subtype and fixed-evaluation-fiber
  versions hold for every subset and every pole, even a nonclosed one, without
  compact-generation or separation assumptions. Interval paths lift with unchanged
  functions; this does not assert homeomorphisms or compact generation of arbitrary
  subspaces.
- **Relative homotopies under refinement** ([`Homotopy.CompactlyGenerated`](FundamentalGroupoids/Topology/Homotopy/CompactlyGenerated.lean)).
  From any `UCompactlyGeneratedSpace.{u}` source, a supplied relative homotopy
  lifts to the CompHaus-test refinement of its target with its entire joint
  cylinder function unchanged. Endpoints and any fixed subset are preserved;
  counit postcomposition is inverse to lifting, which is natural in target maps.
  Source, target and probe universes are independent. The target needs no
  separation or compact-generation assumption, and the source needs no local
  compactness or first-countability assumption.
- **CompHaus-test topology comparisons** ([`HomotopyGroup.CompactlyGenerated`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/CompactlyGenerated.lean)).
  Refining the target topology to Mathlib's `compactlyGenerated.{u} X` leaves
  every boundary-relative cubical homotopy quotient canonically equivalent to
  the original-topology quotient. The forward function is the existing
  `HomotopyGroup.mapFun`; for nonempty indices with decidable equality the
  comparison is multiplicative for the existing group structures, naturally
  in based maps. Probe, cube-index and target universes are independent, with
  no target separation or compact-generation hypothesis. Empty indices retain
  all path components; for infinite indices both quotients are subsingletons.
  This compares two topologies in the same cubical model, not sphere-domain
  classes or May's weak-Hausdorff category. The
  [continuous-map API](FundamentalGroupoids/Topology/Compactness/CompactlyGeneratedSpace.lean)
  lifts unchanged functions from any `UCompactlyGeneratedSpace.{u}` source,
  with evaluation, inverse-composition and refinement-naturality laws.
- **Basepoint transport of generalized homotopy classes** ([`HomotopyGroup.BasepointEquiv`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/BasepointEquiv.lean)).
  A path `γ : Path x y` induces `HomotopyGroup.equivOfPath γ` for arbitrary
  index types and topological targets, with independent universes. The
  characteristic theorem `HomotopyGroup.pathMap_mk_eq_iff` identifies transport
  of representatives with a homotopy having boundary trace exactly `γ`.
  With the supplied `[DecidableEq N] [Nonempty N]`, `mulEquivOfPath γ` preserves
  the existing multiplication; transport is natural and agrees with the
  fundamental-group construction in degree one. Empty indices preserve the
  represented component of the target; infinite-index quotients are
  subsingletons. No separation or local compactness of the target is required,
  and no sphere or kification model comparison is asserted.
- **Generalized-loop spaces and components** ([`HomotopyGroup.LoopSpace`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/LoopSpace.lean)).
  For a singleton index type `J`, `genLoopHomeoOfUnique J x` is a homeomorphism
  from `GenLoop J X x` to the compact-open based path space `Path x x`, with
  underlying equivalence `genLoopEquivOfUnique J`. It evaluates a generalized
  loop on constant coordinates and its inverse evaluates a path at the unique
  coordinate. Constant loops correspond to reflexive paths, and the comparison
  commutes with based postcomposition, including endpoint casts. Index and target
  universes are independent; no separation or local compactness of `X` is needed.
  `HomotopyGroup.equivZerothHomotopy N x` identifies the raw quotient
  `HomotopyGroup N X x` with `ZerothHomotopy (GenLoop N X x)` by the identity
  on representatives in both directions, preserving the chosen constant class.
  The compact-open/subtype topology is unchanged. Index and space universes are
  independent; only a topology and chosen `x` are required, with no finiteness,
  index nonemptiness, decidable equality or separation assumptions.
  Naturality relates `HomotopyGroup.mapFun` to `ZerothHomotopy.map` of the same
  continuous `GenLoop.map`. For empty indices, the square with
  `genLoopHomeoOfIsEmpty` and `homotopyGroupEquivZerothHomotopyOfIsEmpty`
  commutes, including arbitrary `y : X`, not just `x`. No group structure on
  components is introduced. This is a raw cubical analogue of May, Chapter 8 §1's
  based mapping-space observation; his sphere classes and kified weak-Hausdorff
  category `U` use a different model. No sphere-domain, interval-quotient,
  kification, `U`-category or finite iterated-loop comparison is asserted.
  Boundaries mean coordinate faces; for infinite indices these are not interpreted
  as ambient frontiers or infinite-dimensional spheres.
- **Fundamental-group actions on generalized homotopy quotients** ([`HomotopyGroup.Action`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Action.lean)).
  The existing fundamental group acts on every generalized homotopy quotient by
  path-induced change of basepoint. Its reversed traversal product makes this a
  left action. Representatives are related exactly by homotopies whose whole
  cube boundary follows the chosen loop. Based maps are equivariant for their
  induced fundamental-group maps. With the given nonempty index and decidable
  equality, the same action preserves the existing group multiplication. Empty
  indices fix every free path component; in degree one Mathlib's comparison
  gives conjugation `g * a * g⁻¹`. Target and index universes are independent,
  and no separation or local-connectivity hypothesis is required.
- **Point-local loop rigidity and totally disconnected targets** ([`HomotopyGroup.Discrete`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Discrete.lean)).
  At any chosen point with a subsingleton path component, every generalized loop
  indexed by a nonempty type equals the constant loop, so its boundary-relative
  homotopy quotient is a subsingleton. In particular this holds at every basepoint
  of a totally disconnected space, including discrete spaces. Cube and target
  universes are independent, and indices may be infinite. The nonempty-index
  hypothesis is essential in general: the empty-index quotient records all
  path components.
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
- **Positive integer index in punctured complex balls** ([`FundamentalGroup.ComplexPuncturedBall`](FundamentalGroupoids/FundamentalGroup/ComplexPuncturedBall.lean)).
  For `0 < a < r`, positive scaling embeds `Circle` as the radius-`a` circle
  inside the punctured radius-`r` ball, and normalization is `z / ‖z‖`.
  The radial deformation fixes this circle pointwise. At the image of
  `1 : Circle`, normalization induces a multiplicative equivalence of the
  fundamental group with `Multiplicative ℤ`; its inverse scales circle classes.
  Every scaled `Circle.loop n` has index `n`, so the positive loop is nontrivial
  and has index one, including on the half-radius circle in the unit ball.
- **Radial deformation of punctured closed balls** ([`Homotopy.Radial`](FundamentalGroupoids/Topology/Homotopy/Radial.lean)).
  For every real normed space and positive radius, radial projection retracts
  the closed ball with its centre removed onto its metric sphere. The scalar
  interpolation from the identity to inclusion after projection is a
  `ContinuousMap.HomotopyRel` fixing every boundary point. The projection and
  inclusion give a `ContinuousMap.HomotopyEquiv`, with evaluation, endpoint,
  boundary-fixing and retraction laws. No nontriviality, completeness or dimension
  assumption is required; empty punctured balls and spheres are allowed.
  For an open ball of radius `r` and `0 < a < r`, the same construction
  retracts onto the radius-`a` inner sphere, with the deformation fixing the
  range of its inclusion. Projection onto a positive-radius sphere requires
  only `0 < a`, even when that sphere is not contained in the source ball.
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
- **Common-overlap stars** ([`CommonOverlap`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/CommonOverlap.lean)).
  Let a based open core `C` lie in every chart `U i`, with `C` and the charts
  path connected, `U i ∩ U j = C` for distinct indices, and the core together
  with the charts covering the space. The core-to-chart inclusion star has the
  ambient fundamental group as its colimit. Its raw group colimit is canonically
  multiplicatively equivalent to that group, preserving every core and chart
  leg in both directions. Space and index universes are independent; empty
  chart families and a nontrivial core fundamental group are allowed.
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
- **Infinite cyclic intersections** ([`OpenCoverCyclicIntersection`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/OpenCoverCyclicIntersection.lean)).
  For a path-connected two-open cover with path-connected intersection, suppose
  the second open has trivial fundamental group and the intersection group is
  classified by `Multiplicative ℤ`. A homomorphism on the first open extends
  uniquely exactly when it kills the inclusion image of the class corresponding
  to `Multiplicative.ofAdd (1 : ℤ)`. Restriction gives an equivalence with these
  homomorphisms, with forward and inverse restriction laws. Restriction to the
  first open also determines ambient homomorphisms without any cyclicity
  assumption. Space and target-group universes are independent; no geometric
  orientation is implicit in the supplied classification.
- **Path-component inclusion** ([`pathComponentInclusionMulEquiv`](FundamentalGroupoids/FundamentalGroup.lean)).
  Inclusion of a path component induces an isomorphism on fundamental groups at
  any point of the component. The inverse is represented by corestricting loops;
  neither openness of the component nor connectedness of the ambient space is required.

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

For path components, import `FundamentalGroupoids.Topology.Connected.PathConnected`
and use `ZerothHomotopy.map f`. Its representative law is `map_mk`; `map_id` and
`map_comp` are pointwise laws, and `map_eq_of_homotopy f g H` gives equality of
functions for a homotopy `H : ContinuousMap.Homotopy f g`.

For generalized loops and homotopy groups, import
`FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map` and use
`GenLoop.map f hf`, `HomotopyGroup.mapFun N f hf` or, for a nonempty index with
supplied decidable equality, `HomotopyGroup.map N f hf`. Here `hf : f x = y`
relates the supplied points. See the [homotopy-group map guide](docs/mathematical-guide.md#based-maps-on-homotopy-groups).
These declarations keep the names from
[Restricted Product Duality](https://github.com/FormalFrontier/restricted-product-duality).
Co-importing the libraries requires a Restricted Product Duality version whose
`HomotopyMaps` module publicly imports this module rather than defining its own copies.

For the fundamental-group action, import
`FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Action`. The explicit value
`HomotopyGroup.fundamentalGroupMulAction N x` supplies scalar notation locally
for any index type. Under the given `[DecidableEq N] [Nonempty N]`, use
`HomotopyGroup.fundamentalGroupMulDistribMulAction N x` for the same action with
its multiplication-preservation laws. No global action instances are added.

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

For product-parameter colimit continuity, import
`FundamentalGroupoids.Topology.Category.TopCat.Limits.Products` and use
`TopCat.continuous_prod_iff_of_isColimit c hc`. For wide-pushout families or
homotopies, import `FundamentalGroupoids.Topology.Homotopy.WidePushout` and use
`TopCat.widePushoutProdDesc`, `TopCat.widePushoutHomotopy` or
`TopCat.widePushoutPointHomotopyRel`. Their head and factor equations and uniqueness
lemmas characterize the constructed data; the last constructor requires explicit
head equality even when there are no factors.

For ordered finite wedges, import
`FundamentalGroupoids.Topology.Category.TopCat.Based.FiniteWedge` and use
`BasedTopCat.basedWedgeFinTwoIso D`, `BasedTopCat.basedWedgeFinThreeLeftIso D`
or `BasedTopCat.basedWedgeFinThreeRightIso D`. The `_ι_*_hom` and `_ι_*_inv`
equations specify every factor restriction; `_hom_point` and `_inv_point`
record common-point preservation. Apply `BasedTopCat.homotopyQuotient.mapIso`
to any of these isomorphisms to pass to the based-homotopy category.

For finite products in the opposite based-homotopy category, import
`FundamentalGroupoids.Topology.Category.TopCat.Based.Cartesian` and use
`BasedTopCat.homotopyOppositeTerminalLimitCone`,
`BasedTopCat.homotopyOppositeBinaryLimitCone` and
`BasedTopCat.homotopyOppositeCartesianMonoidalCategory`. Use the last as a local
instance for monoidal notation; the `homotopyOpposite_*` equations identify the
unit, tensor, projections and terminal map with the corresponding wedge data.
`BasedTopCat.homotopyOpposite_associator_unop_comp_finThreeLeft D` compares the
unop of this associator with the ordered flattenings of a three-factor wedge.

For point-family maps, import
`FundamentalGroupoids.Topology.Category.TopCat.Limits.WidePushout.PointMap`.
`TopCat.widePushoutDesc_point_condition` supplies compatibility for
`TopCat.widePushoutDesc`; the head, factor, uniqueness, identity and composition
laws describe this descent without unfolding it. Import the neighboring
`WidePushout.ULift` module for `TopCat.widePushoutPointULiftUp`,
`TopCat.widePushoutPointULiftDown` and `TopCat.widePushoutPointULiftHomeomorph`.
For the based isomorphism `BasedTopCat.basedWedgeULiftIso`, import
`FundamentalGroupoids.Topology.Category.TopCat.Based.ULift`.

**Covering, circle and wide-pushout compatibility:** these modules retain declaration names
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
| [`FundamentalGroup`](FundamentalGroupoids/FundamentalGroup.lean) | Induced-map and basepoint-equality laws, null-loop/trivial-image criteria, path-component inclusion isomorphisms, path transport, relative and moving-track homotopy comparisons, and retraction splittings |
| [`FundamentalGroup.DiskAttachment`](FundamentalGroupoids/FundamentalGroup/DiskAttachment.lean) | Triviality of every attaching boundary-circle fundamental-group map, at arbitrary and chosen basepoints |
| [`Topology.Connected.PathConnected`](FundamentalGroupoids/Topology/Connected/PathConnected.lean) | Continuous maps on path components, with representative, identity, composition and homotopy-invariance laws |
| [`Topology.Compactification.OnePoint.Collapse`](FundamentalGroupoids/Topology/Compactification/OnePoint/Collapse.lean) | Continuous open-subspace collapse for Hausdorff spaces, membership and infinity laws, and a surjective disjoint-point extension that is a quotient map for compact sources |
| [`Topology.Compactification.OnePoint.ContinuousMap`](FundamentalGroupoids/Topology/Compactification/OnePoint/ContinuousMap.lean) | Compact-open/subtype homeomorphism between maps based at infinity and ambient maps constant outside any open in a compact Hausdorff space; collapse-precomposition, recursor and evaluation laws |
| [`Topology.Homeomorph.Subtype`](FundamentalGroupoids/Topology/Homeomorph/Subtype.lean) | Flattening nested subspaces using Mathlib's carrier equivalence, with forward/inverse coercion laws |
| [`Topology.Homotopy.RelativePathSpace`](FundamentalGroupoids/Topology/Homotopy/RelativePathSpace.lean) | Ordinary compact-open paths from an arbitrary point to a subspace, with constructor, extensionality, evaluation, endpoint and functorial postcomposition APIs |
| [`Topology.Homotopy.Fiber`](FundamentalGroupoids/Topology/Homotopy/Fiber.lean) | Retained-point ordinary homotopy fibers, maps of continuous squares, pullback and embedding/subspace homeomorphisms, with projection, evaluation, constant and naturality laws |
| [`Topology.Homotopy.Fiber.Const`](FundamentalGroupoids/Topology/Homotopy/Fiber/Const.lean) | Constant-map fibers as source times fixed-endpoint Path, with coordinate laws, source naturality and a nonemptiness criterion |
| [`Topology.Homotopy.Fiber.Contractible`](FundamentalGroupoids/Topology/Homotopy/Fiber/Contractible.lean) | Identity-map fiber contraction relative to its constant-path point, with moving-point, whole-path, evaluation, endpoint and fixed-point laws, and a contractibility instance for arbitrary targets |
| [`Topology.Homotopy.Fiber.Exact`](FundamentalGroupoids/Topology/Homotopy/Fiber/Exact.lean) | Component images for fiber maps over the identity base; all-index loop-inclusion and point-projection exactness, positive range–kernel forms, all-loop-component image and fundamental-group exactness, with arbitrary topologies and independent universes |
| [`Topology.Homotopy.Fiber.Homeomorph`](FundamentalGroupoids/Topology/Homotopy/Fiber/Homeomorph.lean) | Homeomorphisms induced by invertible coordinate squares, with forward/inverse point and full-path laws, identity, composition and projection compatibility |
| [`Topology.Homotopy.Fiber.PathComponent`](FundamentalGroupoids/Topology/Homotopy/Fiber/PathComponent.lean) | Homotopy-fiber nonemptiness, surjectivity on path components iff all fibers are nonempty, and the point projection's component image as the preimage of the basepoint component, for independent universes and arbitrary topologies |
| [`Topology.Homotopy.Fiber.Prod`](FundamentalGroupoids/Topology/Homotopy/Fiber/Prod.lean) | Product fibers as products of fibers, preserving retained points and full same-time paths, with projection diagrams and naturality for arbitrary continuous squares; free source factors split off with whole point/path diagrams, constructor laws and six-universe naturality |
| [`Topology.Homotopy.RelativePathSpace.Contractible`](FundamentalGroupoids/Topology/Homotopy/RelativePathSpace/Contractible.lean) | Explicit time-shortening homotopy relative to the constant path, characteristic evaluation and moving-endpoint laws, and contractibility of fixed-start/free-endpoint paths |
| [`Topology.Homotopy.Affine`](FundamentalGroupoids/Topology/Homotopy/Affine.lean) | Affine homotopies fixed on an agreement subset, with evaluation and underlying-homotopy equations |
| [`Topology.Homotopy.HomotopyGroup.Affine`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Affine.lean) | Boundary-relative contraction of generalized loops in real topological vector spaces and subsingleton homotopy quotients for every index type |
| [`Topology.Homotopy.HomotopyGroup.Map`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Map.lean) | Based postcomposition on generalized loops and all homotopy quotients, positive homomorphisms, based-homotopy invariance and fundamental-group compatibility |
| [`Topology.Homotopy.HomotopyGroup.Action`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Action.lean) | Fundamental-group actions on all homotopy quotients, preservation of the given positive group structure, strict boundary characterization, based-map equivariance, empty free components and degree-one conjugation |
| [`Topology.Compactness.CompactlyGeneratedSpace`](FundamentalGroupoids/Topology/Compactness/CompactlyGeneratedSpace.lean) | Source-test continuity, unchanged-function lifts, locally compact product closure and the identity product-refinement homeomorphism; closed-subtype compact generation and refinement homeomorphisms, and preservation of closed embeddings |
| [`Topology.Homotopy.CompactlyGenerated`](FundamentalGroupoids/Topology/Homotopy/CompactlyGenerated.lean) | Joint relative-homotopy lifts with arbitrary fixed subsets, counit inverse laws, target naturality and homotopy-existence comparison; fixed-evaluation-fiber refinement homeomorphisms and based naturality; counit bijectivity on path components for arbitrary spaces, subtypes and fixed-evaluation fibers |
| [`Topology.Homotopy.HomotopyGroup.CompactlyGenerated`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/CompactlyGenerated.lean) | Natural equivalences for CompHaus-test topology comparisons on all cubical homotopy quotients, with existing-map and positive multiplicative characteristics |
| [`Topology.Homotopy.HomotopyGroup.LoopSpace`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/LoopSpace.lean) | Singleton-indexed generalized-loop/based-path homeomorphism retaining the underlying equivalence, full evaluation and based-map laws; boundary-relative homotopy iff joinedness; raw quotient/component equivalence with constant, naturality and empty-index laws |
| [`Topology.Homotopy.HomotopyGroup.Product`](FundamentalGroupoids/Topology/Homotopy/HomotopyGroup/Product.lean) | Canonical evaluation/assembly equivalences for arbitrary dependent products and cube indices; stock multiplicative equivalences for nonempty cube indices with decidable equality |
| [`Topology.Homotopy.Cube`](FundamentalGroupoids/Topology/Homotopy/Cube.lean) | Closed coordinate-face boundaries for finite indices, zero boundary vertex for nonempty indices and path-connected boundaries for nontrivial indices |
| [`Topology.Homotopy.Cube.Coordinates`](FundamentalGroupoids/Topology/Homotopy/Cube/Coordinates.lean) | Increasing real-product coordinates on the boundary complement for every index type, with membership and forward/inverse evaluation laws; local compactness theorem for finite indices |
| [`Topology.Homotopy.GenLoop.OnePoint`](FundamentalGroupoids/Topology/Homotopy/GenLoop/OnePoint.lean) | Finite generalized loops as based maps from the one-point compactification of the cube-boundary complement, with restriction/extension, collapse-precomposition and evaluation laws, including empty indices |
| [`Topology.Covering.GenLoop`](FundamentalGroupoids/Topology/Covering/GenLoop.lean) | Compact-open homeomorphisms of based generalized-loop spaces through coverings for nontrivial cube indices, with chosen-lift inverse, continuous-square naturality and quotient representative compatibility |
| [`Topology.Covering.HomotopyGroup`](FundamentalGroupoids/Topology/Covering/HomotopyGroup.lean) | Canonical quotient-map injectivity for nonempty indices, bijectivity and stock multiplicative equivalences for nontrivial indices, with forward and inverse representative formulas |
| [`Topology.Homotopy.Relative`](FundamentalGroupoids/Topology/Homotopy/Relative.lean) | Relative-homotopy precomposition; `HomotopyWith.joined` without local compactness and `nonempty_iff_joined` for locally compact sources, for arbitrary predicates and independent source/target universes |
| [`Topology.Category.TopCat.Based`](FundamentalGroupoids/Topology/Category/TopCat/Based.lean) | Based spaces as an under category, based-homotopy congruence and categorical quotient |
| [`Topology.Category.TopCat.Based.Cartesian`](FundamentalGroupoids/Topology/Category/TopCat/Based/Cartesian.lean) | Chosen terminal and binary limit cones in the ordinary opposite based-homotopy category, their named cartesian monoidal structure, and compatibility of its associator with ordered three-factor flattening |
| [`Topology.Category.TopCat.Based.Coproducts`](FundamentalGroupoids/Topology/Category/TopCat/Based/Coproducts.lean) | Point-wide-pushout coproduct data in based spaces and their homotopy category, factorwise based-homotopy criterion, and empty and binary specializations |
| [`Topology.Category.TopCat.Based.FiniteWedge`](FundamentalGroupoids/Topology/Category/TopCat/Based/FiniteWedge.lean) | Strict isomorphisms between ordered two-factor and binary wedges, and from both nested binary three-factor wedges to the finite wedge, with forward/inverse leg and point equations |
| [`Topology.Category.TopCat.Based.Products`](FundamentalGroupoids/Topology/Category/TopCat/Based/Products.lean) | Canonical based product identification with the dependent product and its coordinate equations |
| [`Topology.Category.TopCat.Based.ULift`](FundamentalGroupoids/Topology/Category/TopCat/Based/ULift.lean) | Isomorphism from a point-wide-pushout lifted and based at its head to the based wedge of the lifted pointed factors, with underlying-map, head, factor and inverse equations |
| [`Topology.Category.TopCat.DiskAttachment`](FundamentalGroupoids/Topology/Category/TopCat/DiskAttachment.lean) | Unpointed disk attachments, universal property, original-space closed embedding, disjoint open-disk embeddings and empty/identity attachment homeomorphisms |
| [`Topology.Category.TopCat.DiskAttachment.Punctured`](FundamentalGroupoids/Topology/Category/TopCat/DiskAttachment/Punctured.lean) | Closed centre set, punctured subspace, characteristic maps and descent of functions and continuous maps |
| [`Topology.Category.TopCat.DiskAttachment.PuncturedRetraction`](FundamentalGroupoids/Topology/Category/TopCat/DiskAttachment/PuncturedRetraction.lean) | Retraction onto the original space and radial strong deformation fixing its image |
| [`Topology.Category.TopCat.Limits.Products`](FundamentalGroupoids/Topology/Category/TopCat/Limits/Products.lean) | Product-parameter continuity for supplied topological colimits under a locally compact pair hypothesis, and its one-point specialization |
| [`Topology.Category.TopCat.Limits.WidePushout`](FundamentalGroupoids/Topology/Category/TopCat/Limits/WidePushout.lean) | Head-plus-factors quotient comparison, arbitrary-target continuous descent and uniqueness, and empty/singleton diagram homeomorphisms |
| [`Topology.Category.TopCat.Limits.WidePushout.PointMap`](FundamentalGroupoids/Topology/Category/TopCat/Limits/WidePushout/PointMap.lean) | Point-preserving family descent with independently sized families, head and factor characteristics, uniqueness, and identity and composition laws |
| [`Topology.Category.TopCat.Limits.WidePushout.ULift`](FundamentalGroupoids/Topology/Category/TopCat/Limits/WidePushout/ULift.lean) | Universe-raising and universe-lowering descent, strict inverse equations, and the universe-lift homeomorphism with head, factor and inverse evaluation laws |
| [`Topology.Homotopy.WidePushout`](FundamentalGroupoids/Topology/Homotopy/WidePushout.lean) | Jointly continuous family and homotopy descent, all-time restrictions, uniqueness and reparameterization; point-relative factor homotopies as a unique head-relative homotopy |
| [`AlgebraicTopology.FundamentalGroup.Circle`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Circle.lean) | Signed-period additive-circle and complex-circle integer coordinates, loop/inverse/endpoint laws, nonidentity generators and homeomorphism compatibility |
| [`AlgebraicTopology.FundamentalGroup.Functor`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/Functor.lean) | Fundamental-group functor on based spaces and its unique factorization through based homotopy |
| [`CategoryTheory.Elements.ConnectedComponents`](FundamentalGroupoids/CategoryTheory/Elements/ConnectedComponents.lean) | Components/type-colimit equivalences, representative equations and naturality; induced colimit maps with identity/composition laws |
| [`CategoryTheory.Endomorphism.Conjugation`](FundamentalGroupoids/CategoryTheory/Endomorphism/Conjugation.lean) | Pointwise commutation criterion, centrality, commutative transport and group conjugation |
| [`CategoryTheory.SingleObj`](FundamentalGroupoids/CategoryTheory/SingleObj.lean) | Fullness, faithfulness and the chosen-vertex equivalence |
| [`CategoryTheory.Groupoid.ConnectedComponents`](FundamentalGroupoids/CategoryTheory/Groupoid/ConnectedComponents.lean) | Equality of component classes in any groupoid iff a morphism exists, with independent object and morphism universes |
| [`CategoryTheory.Groupoid.Covering`](FundamentalGroupoids/CategoryTheory/Groupoid/Covering.lean) | Canonical fiber monodromy; pretransitivity for preconnected total groupoids and total preconnectedness from pretransitivity over a preconnected groupoid base |
| [`CategoryTheory.Groupoid.Elements`](FundamentalGroupoids/CategoryTheory/Groupoid/Elements.lean) | Fiber-value equivalence, compatibility with lifts and monodromy, and covering projections on groupoids |
| [`AlgebraicTopology.FundamentalGroupoid.Connected`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroupoid/Connected.lean) | Equality of categorical component classes iff points are joined by a path; path connectedness and connected groupoids |
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
| [`AlgebraicTopology.FundamentalGroup.CommonOverlap`](FundamentalGroupoids/AlgebraicTopology/FundamentalGroup/CommonOverlap.lean) | Common-core inclusion-star colimit and raw-quotient equivalence, preserving every leg in independent universes |
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
| [`Topology.Homotopy.Radial`](FundamentalGroupoids/Topology/Homotopy/Radial.lean) | Radial projection and strong deformation of punctured closed balls and open balls onto spheres in arbitrary real normed spaces |
| [`Topology.Homotopy.ComplexPuncturedBall`](FundamentalGroupoids/Topology/Homotopy/ComplexPuncturedBall.lean) | Positive scaling from Circle to complex spheres, normalization and circle-fixing radial deformation |
| [`FundamentalGroup.ComplexPuncturedBall`](FundamentalGroupoids/FundamentalGroup/ComplexPuncturedBall.lean) | Integer classification of punctured complex balls, scaled circle-loop formulas and a nontrivial positive generator |

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
  Chapter 1 §§3–5, 7, Chapter 2 §§5, 7–8, Chapter 3 §§2–4, 7,
  Chapter 7 §3 (printed p. 50, time-shortening deformation),
  Chapter 8 §6 (printed pp. 61–62, path direction, pullback fibers and
  loop-image exactness), and
  Chapter 9 §§1, 4 (printed pp. 65–67, including subspace endpoint paths).
  [Author's revised text](https://www.math.uchicago.edu/~may/CONCISE/ConciseRevised.pdf).
- [Mathlib](https://github.com/leanprover-community/mathlib4) and
  [GroupTheory](https://github.com/FormalFrontier/group-theory).
  See the [guide's references](docs/mathematical-guide.md#references) for scope and dependencies.
- [Restricted Product Duality](https://github.com/FormalFrontier/restricted-product-duality):
  the based-postcomposition definitions and proofs for generalized loops and
  homotopy groups, and the path-component map API, by Formal Frontier Agents.
- [VectorBundles](https://github.com/FormalFrontier/vector-bundles/blob/9d2d4b48577e873679271aeee0899239d9a835a1/VectorBundles/Topology/FiberBundle/Proper.lean):
  the local closedness and compact-fiber proof pattern for proper bundle projections.

## Credits and license

Authors: Formal Frontier Agents. AI agents contributed Lean formalization,
examples and documentation. May supplies mathematical motivation and arguments;
Mathlib supplies underlying constructions and APIs. Its compactly generated topology
and source-test continuity API are due to Dagur Asgeirsson and Etienne Marion.
Covering formalizations originate in sphere-topology by Formal Frontier Agents,
with retained Apache-2.0 and authorship notices. The signed-period and complex-circle
coordinate core also
originates in its [circle formalization](https://github.com/FormalFrontier/sphere-topology/blob/4a2b822f12e7f2b4255dfea5363265277defa35e/SphereTopology/Homotopy/Circle.lean),
using Mathlib's quotient coverings and induced homeomorphism equivalence.
The product-parameter colimit criterion, wide-pushout quotient/descent API and
point-relative homotopy constructor also originate in Sphere Topology by Formal
Frontier Agents. They reuse Mathlib's topological colimits, Joël Riou's
`Types.Pushout`, Reid Barton's compact-open currying and evaluation, and Shing Tak
Lam's relative homotopies. May, Chapter 2 §8, p. 19 supplies the point-wedge setting,
not the pair-hypothesis or universe-general descent results.
Formal Frontier Agents supplied the point-family map laws, the universe-lift
homeomorphism and based isomorphism, the strict ordered finite-wedge comparisons,
and the chosen cartesian structure on the opposite based-homotopy category.
These use Mathlib's homeomorphisms, under categories, coproduct universal
properties, opposite binary (co)fans and cartesian monoidal construction.
Tiller and Loupe supplied point-family image/preimage and empty-head observations.
The generalized-loop and homotopy-group map API originates in Restricted Product
Duality by Formal Frontier Agents, retaining its definitions, proofs, names and
Apache-2.0 notice. It uses Roberto Alvarez's homotopy groups, Mark Lavrentyev's
fundamental groups and Shing Tak Lam's homotopies in Mathlib. The based compact-open
collapse comparisons use Yourong Zang and Yury Kudryashov's one-point
compactification and Mathlib's compact-open topology, together with GroupTheory's
compact-covering precomposition embedding API.
The relative-path spaces, retained-point homotopy fibers, fixed-start contraction
and identity-fiber contraction are by Formal Frontier Agents. May's time-shortening
deformation (Chapter 7 §3, printed p. 50) supplies the contraction idea;
Chapters 8 §6 and 9 §1 motivate the
fiber and endpoint-path models, without identifying their ordinary topologies
with his kified category. The identity-fiber contraction transports the fixed-start
deformation through the embedding comparison using relative-homotopy precomposition,
postcomposition and endpoint casts. The fiber comparisons reuse Mathlib's whole
`TopCat.pullbackHomeoPreimage`, including its inverse continuity, by Patrick Massot,
Kim Morrison, Mario Carneiro and Andrew Yang. The constant-map product splitting
uses Patrick Massot's `Path` topology and Mathlib's product and induced-topology
continuity APIs. The coordinate-square homeomorphism is elementary invariance
of the same fiber, using its map functoriality and Mathlib's coordinate
homeomorphism cancellation. The free-source-factor comparison composes the
existing canonical `pullbackHomeomorph` provider and its inverse with Mathlib's
restricted product associator and set-product homeomorphisms; it is structural
support for the retained-point model, not a named theorem quoted from May.
Subspace flattening uses
`Equiv.subtypeSubtypeEquivSubtypeInter` from the equivalence API by Leonardo de Moura
and Mario Carneiro, with Mathlib's subtype continuity. Evaluation and currying
use Reid Barton's compact-open API; relative homotopies use Shing Tak Lam's API,
and the contractibility criterion uses Praneeth Kolichala's formalization.
The path-component map and its four characteristic laws also originate in
Restricted Product Duality, with names under `ZerothHomotopy`, retained proofs and
notices, and Mathlib's path components by Patrick Massot and contributors.
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
