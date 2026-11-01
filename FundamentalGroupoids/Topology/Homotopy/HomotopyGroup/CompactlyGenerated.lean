/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Compactness.CompactlyGeneratedSpace
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map
public import FundamentalGroupoids.Topology.Homotopy.InfiniteCube

/-!
# Compactly generated topology and cubical homotopy quotients

The continuous identity from `TopologicalSpace.compactlyGenerated.{u} X` to the
original topology induces a bijection on Mathlib's boundary-relative cubical
homotopy quotient for every cube-index type. The forward function is the
existing `HomotopyGroup.mapFun`, not a new quotient map. For nonempty indices
with decidable equality, `HomotopyGroup.compactlyGeneratedMulEquiv` packages the
existing `HomotopyGroup.map` with Mathlib's group structures and multiplication
convention. Both comparisons commute with based continuous maps, using the
same-function map between the compactly generated topologies.

The probe universe, cube-index universe and target universe are independent.
For finite indices, the raw source cube and its full homotopy cylinder are first
countable, hence sequential and `u`-compactly generated for every `u`; continuity
therefore lifts without changing the underlying functions. For infinite indices,
`HomotopyGroup.subsingleton_of_infinite` makes both quotients subsingletons,
without separation assumptions. No product formula for compactly generated
topologies is used. There is no compact-generation, separation or well-pointedness
assumption on `X`.

For `N = Fin n` this is the finite-degree cubical model. For an empty index, the
coordinate-face boundary is empty, so a representative may take any value, not
just the supplied point; the quotient records path components and no group
structure is asserted. Infinite indices concern generalized-loop quotients that
collapse by the subsingleton theorem, not conventional infinite-dimensional
homotopy groups. The boundary is Mathlib's union of coordinate faces, not an
ambient frontier or an infinite-dimensional sphere.

This compares the two topologies in the same cubical model. It does not identify
that model with sphere-domain homotopy classes or supply May's category of weak
Hausdorff compactly generated spaces. No equality of the two target topologies
or homeomorphism between them is asserted.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 5 §§1–2,
  pp. 39–41, for compact-Hausdorff tests and kification, and Chapter 9 §1,
  p. 65, for finite-degree based homotopy groups. The arbitrary-index
  statement here is a cubical extension, without a sphere-model comparison.
* Mathlib's compactly generated topology and source-test continuity API,
  due to Dagur Asgeirsson and Etienne Marion; its generalized loops and homotopy
  groups, due to Roberto Alvarez; and its relative homotopies, due to Shing Tak
  Lam and contributors.
* Based postcomposition on generalized loops and their homotopy quotient is
  provided by `FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map`.
  The infinite-index subsingleton theorem is provided by
  `FundamentalGroupoids.Topology.Homotopy.InfiniteCube`.
-/

@[expose] public section

universe u v w s

open TopologicalSpace

namespace HomotopyGroup

variable {X : Type v} [tX : TopologicalSpace X]

/-- The continuous identity from the CompHaus-test compactly generated topology
induces a bijection on the existing boundary-relative homotopy quotient for every
cube-index type, including an empty one. The finite-index case is the cubical
topology comparison motivated by May, *A Concise Course in Algebraic Topology*,
Chapter 5 §§1–2. For infinite indices both quotients are subsingletons by
`HomotopyGroup.subsingleton_of_infinite`. No separation hypothesis or sphere-domain
comparison is imposed. -/
theorem bijective_mapFun_compactlyGeneratedCounit (N : Type s) (x : X) :
    Function.Bijective
      (@HomotopyGroup.mapFun X X (compactlyGenerated.{u} X) tX x x N
          (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl :
        @HomotopyGroup N X (compactlyGenerated.{u} X) x → HomotopyGroup N X x) := by
  let f : @HomotopyGroup N X (compactlyGenerated.{u} X) x → HomotopyGroup N X x :=
    @HomotopyGroup.mapFun X X (compactlyGenerated.{u} X) tX x x N
      (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl
  change Function.Bijective f
  rcases finite_or_infinite N with hN | hN
  · let : Finite N := hN
    let : Countable N := inferInstance
    -- These are the raw cube and joint cylinder, with their stock product topologies.
    let : FirstCountableTopology (N → unitInterval) := inferInstance
    let : FirstCountableTopology (unitInterval × (N → unitInterval)) := inferInstance
    -- First-countable spaces are sequential, hence compactly generated for every `u`.
    let : UCompactlyGeneratedSpace.{u} (N → unitInterval) := inferInstance
    let : UCompactlyGeneratedSpace.{u} (unitInterval × (N → unitInterval)) := inferInstance
    constructor
    · intro a b
      refine Quotient.inductionOn₂
        (motive := fun a b : @HomotopyGroup N X (compactlyGenerated.{u} X) x ↦
          f a = f b → a = b) a b ?_
      intro p q hpq
      have h : @GenLoop.Homotopic N X tX x
          (@GenLoop.map N X X (compactlyGenerated.{u} X) tX x x
            (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl p)
          (@GenLoop.map N X X (compactlyGenerated.{u} X) tX x x
            (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl q) :=
        Quotient.exact hpq
      rcases h with ⟨H⟩
      apply Quotient.sound
      change Nonempty
        (@ContinuousMap.HomotopyRel (N → unitInterval) X inferInstance
          (compactlyGenerated.{u} X) p.1 q.1 (Cube.boundary N))
      -- Lift the entire jointly continuous homotopy, not just its time slices.
      exact ⟨@ContinuousMap.HomotopyWith.mk (N → unitInterval) X inferInstance
        (compactlyGenerated.{u} X) p.1 q.1
        (fun f ↦ ∀ a ∈ Cube.boundary N, f a = p.1 a)
        (@ContinuousMap.Homotopy.mk (N → unitInterval) X inferInstance
          (compactlyGenerated.{u} X) p.1 q.1
          (@ContinuousMap.toCompactlyGenerated.{u} (unitInterval × (N → unitInterval)) X
            inferInstance tX inferInstance H.toContinuousMap)
          (fun a ↦ H.apply_zero a) (fun a ↦ H.apply_one a))
        (fun t a ha ↦ H.eq_fst t ha)⟩
    · apply Quotient.map_surjective
      intro p
      refine ⟨
        (⟨@ContinuousMap.toCompactlyGenerated.{u} (N → unitInterval) X
          inferInstance tX inferInstance p.1, p.2⟩ :
          @GenLoop N X (compactlyGenerated.{u} X) x), ?_⟩
      apply GenLoop.ext
      intro a
      rfl
  · let : Infinite N := hN
    let : Subsingleton (@HomotopyGroup N X (compactlyGenerated.{u} X) x) :=
      @HomotopyGroup.subsingleton_of_infinite N inferInstance X (compactlyGenerated.{u} X) x
    let : Subsingleton (HomotopyGroup N X x) :=
      HomotopyGroup.subsingleton_of_infinite N X x
    -- The stock constant representatives inhabit the quotients on both sides.
    exact Function.bijective_of_subsingleton' f

/-- The equivalence induced by the continuous identity from the CompHaus-test
compactly generated topology, using the existing homotopy quotient on each side.
It includes the empty-index path-component case. -/
noncomputable def compactlyGeneratedEquiv (N : Type s) (x : X) :
    @HomotopyGroup N X (compactlyGenerated.{u} X) x ≃ HomotopyGroup N X x :=
  Equiv.ofBijective
    (@HomotopyGroup.mapFun X X (compactlyGenerated.{u} X) tX x x N
      (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl)
    (bijective_mapFun_compactlyGeneratedCounit.{u} N x)

/-- The forward equivalence is the existing map on the homotopy quotient. -/
@[simp]
theorem compactlyGeneratedEquiv_apply (N : Type s) (x : X)
    (a : @HomotopyGroup N X (compactlyGenerated.{u} X) x) :
    compactlyGeneratedEquiv.{u} N x a =
      @HomotopyGroup.mapFun X X (compactlyGenerated.{u} X) tX x x N
        (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl a :=
  rfl

/-- On representatives the equivalence is postcomposition by the continuous
identity, so the underlying cube map does not change. -/
theorem compactlyGeneratedEquiv_apply_class (N : Type s) (x : X)
    (p : @GenLoop N X (compactlyGenerated.{u} X) x) :
    compactlyGeneratedEquiv.{u} N x
        (⟦p⟧ : @HomotopyGroup N X (compactlyGenerated.{u} X) x) =
      (⟦@GenLoop.map N X X (compactlyGenerated.{u} X) tX x x
        (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl p⟧ :
        HomotopyGroup N X x) :=
  rfl

/-- The continuous identity gives a multiplicative equivalence for the existing
positive homotopy-group structures. Its forward homomorphism is `map`; no group
structure is transported or replaced. -/
noncomputable def compactlyGeneratedMulEquiv (N : Type s)
    [DecidableEq N] [Nonempty N] (x : X) :
    @HomotopyGroup N X (compactlyGenerated.{u} X) x ≃* HomotopyGroup N X x :=
  MulEquiv.ofBijective
    (@HomotopyGroup.map X X (compactlyGenerated.{u} X) tX x x N
      inferInstance inferInstance (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl) (by
      rw [@coe_map_eq_mapFun X X (compactlyGenerated.{u} X) tX x x N
        inferInstance inferInstance (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl]
      exact bijective_mapFun_compactlyGeneratedCounit.{u} N x)

/-- The forward homomorphism is exactly the existing based-postcomposition map
for Mathlib's group structures. -/
theorem compactlyGeneratedMulEquiv_toMonoidHom (N : Type s)
    [DecidableEq N] [Nonempty N] (x : X) :
    (compactlyGeneratedMulEquiv.{u} N x).toMonoidHom =
      @HomotopyGroup.map X X (compactlyGenerated.{u} X) tX x x N
        inferInstance inferInstance (ContinuousMap.compactlyGeneratedCounit.{u} X) rfl :=
  rfl

/-- Forgetting multiplication gives the equivalence on the same homotopy quotient. -/
theorem compactlyGeneratedMulEquiv_toEquiv (N : Type s)
    [DecidableEq N] [Nonempty N] (x : X) :
    (compactlyGeneratedMulEquiv.{u} N x).toEquiv = compactlyGeneratedEquiv.{u} N x :=
  rfl

variable {Y : Type w} [tY : TopologicalSpace Y]

/-- The topology-comparison equivalences commute with based postcomposition,
using the same-function continuous map between the two refined topologies. -/
theorem compactlyGeneratedEquiv_mapFun (N : Type s)
    {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y)
    (a : @HomotopyGroup N X (compactlyGenerated.{u} X) x) :
    compactlyGeneratedEquiv.{u} N y
        (@HomotopyGroup.mapFun X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y) x y N
          (ContinuousMap.compactlyGeneratedMap.{u} f) hf a) =
      @HomotopyGroup.mapFun X Y tX tY x y N f hf
        (compactlyGeneratedEquiv.{u} N x a) := by
  refine Quotient.inductionOn a ?_
  intro p
  rfl

/-- The multiplicative topology comparisons commute with the existing based
homomorphisms, for the same stock group structures on both sides. -/
theorem compactlyGeneratedMulEquiv_map (N : Type s)
    [DecidableEq N] [Nonempty N] {x : X} {y : Y}
    (f : C(X, Y)) (hf : f x = y)
    (a : @HomotopyGroup N X (compactlyGenerated.{u} X) x) :
    compactlyGeneratedMulEquiv.{u} N y
        (@HomotopyGroup.map X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y) x y N inferInstance inferInstance
          (ContinuousMap.compactlyGeneratedMap.{u} f) hf a) =
      @HomotopyGroup.map X Y tX tY x y N inferInstance inferInstance f hf
        (compactlyGeneratedMulEquiv.{u} N x a) :=
  compactlyGeneratedEquiv_mapFun.{u} N f hf a

end HomotopyGroup
