/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Maps and products for the compactly generated topology

Mathlib's `TopologicalSpace.compactlyGenerated.{u} X` is a topology on the same
carrier `X`, tested by continuous maps from `CompHaus.{u}`. The continuous
identity `ContinuousMap.compactlyGeneratedCounit` points from this topology
to the original one.

For a `UCompactlyGeneratedSpace.{u}` source, continuity of a function into the
compactly generated topology is equivalent to continuity into the original
topology. `ContinuousMap.toCompactlyGenerated` bundles this unchanged function;
its two composition identities characterize the lift. The probe, source and
target universes are independent. `ContinuousMap.compactlyGeneratedMap` refines
both topologies of a continuous map without changing its function, compatibly
with identity, composition and the outward comparisons.

For a locally compact `UCompactlyGeneratedSpace.{u}` factor `P`,
`Homeomorph.compactlyGeneratedProd` compares the compactly generated topology on
`P × A` with the product of `P` and the compactly generated topology on arbitrary
`A`. Both directions are the identity function. This does not assert closure
under arbitrary ordinary products of compactly generated spaces.

No separation hypothesis is imposed. In particular, this is the CompHaus-test
construction, not a claim that an arbitrary target is weak Hausdorff. May's
term "compactly generated" includes weak Hausdorffness. No new type, topology,
category or adjunction is introduced here.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 5 §§1–2,
  pp. 39–40, for compact-Hausdorff tests and the continuous identity to the
  original topology, with the weak-Hausdorff convention described above.
* Mathlib's compactly generated topology and source-test continuity API,
  due to Dagur Asgeirsson and Etienne Marion.
* Mathlib's compact-open formalization (Reid Barton), especially the
  quotient-product continuity theorem
  `Topology.IsQuotientMap.continuous_lift_prod_right` in
  `Mathlib.Topology.CompactOpen`, which supplies the locally compact descent
  used in the product proof.
-/

@[expose] public section

universe u v w z

open TopologicalSpace

namespace ContinuousMap

variable (X : Type v) [tX : TopologicalSpace X]

/-- The continuous identity from the CompHaus-test compactly generated topology
to the original topology on the same carrier. This is a continuous map, not a
packaged categorical adjunction. -/
def compactlyGeneratedCounit :
    @ContinuousMap X X (compactlyGenerated.{u} X) tX :=
  @ContinuousMap.mk X X (compactlyGenerated.{u} X) tX (_root_.id : X → X)
    (@continuous_from_compactlyGenerated.{u} X X tX tX (_root_.id : X → X)
      fun _ g ↦ g.continuous)

/-- The outward comparison does not change points. -/
@[simp]
theorem compactlyGeneratedCounit_apply (x : X) :
    compactlyGeneratedCounit.{u} X x = x :=
  rfl

end ContinuousMap

/-- For a `u`-compactly generated source, a function is continuous into the
CompHaus-test compactly generated topology exactly when it is continuous into
the original topology. The target has no compact-generation or separation
hypothesis, and the three universes are independent. -/
theorem continuous_to_compactlyGenerated_iff {Z : Type w} {X : Type v}
    [tZ : TopologicalSpace Z] [tX : TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} Z] (f : Z → X) :
    @Continuous Z X tZ (compactlyGenerated.{u} X) f ↔ @Continuous Z X tZ tX f := by
  constructor
  · intro h
    exact @Continuous.comp Z X X tZ (compactlyGenerated.{u} X) tX f _root_.id
      (@ContinuousMap.continuous_toFun X X (compactlyGenerated.{u} X) tX
        (@ContinuousMap.compactlyGeneratedCounit.{u} X tX)) h
  · intro h
    refine @continuous_from_uCompactlyGeneratedSpace.{u} Z X tZ
      (compactlyGenerated.{u} X) inferInstance f ?_
    intro S g
    let p : C(S, X) :=
      @ContinuousMap.mk S X inferInstance tX (f ∘ g) (h.comp g.continuous)
    let e : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) → X :=
      fun ⟨⟨_, i⟩, s⟩ ↦ i s
    suffices ∀ (i : (T : CompHaus.{u}) × C(T, X)),
        @Continuous i.fst X inferInstance (compactlyGenerated.{u} X)
          (fun (a : i.fst) ↦ e ⟨i, a⟩) from this ⟨S, p⟩
    rw [← @continuous_sigma_iff]
    apply continuous_coinduced_rng

namespace ContinuousMap

variable {Z : Type w} {X : Type v}
variable [tZ : TopologicalSpace Z] [tX : TopologicalSpace X]
variable [UCompactlyGeneratedSpace.{u} Z]

/-- Lift a continuous map from a `u`-compactly generated source to the
CompHaus-test compactly generated topology, without changing its function. -/
def toCompactlyGenerated (f : C(Z, X)) :
    @ContinuousMap Z X tZ (compactlyGenerated.{u} X) :=
  @ContinuousMap.mk Z X tZ (compactlyGenerated.{u} X) (f : Z → X)
    ((@continuous_to_compactlyGenerated_iff.{u} Z X tZ tX inferInstance
      (f : Z → X)).2 f.continuous)

/-- The lift has the same pointwise values as the original map. -/
@[simp]
theorem toCompactlyGenerated_apply (f : C(Z, X)) (z : Z) :
    toCompactlyGenerated.{u} f z = f z :=
  rfl

/-- Composing a lift with the outward comparison recovers the original map. -/
@[simp]
theorem compactlyGeneratedCounit_comp_toCompactlyGenerated (f : C(Z, X)) :
    @ContinuousMap.comp Z X X tZ (compactlyGenerated.{u} X) tX
      (compactlyGeneratedCounit.{u} X) (toCompactlyGenerated.{u} f) = f :=
  rfl

/-- Lifting the outward composite recovers a map into the compactly generated
topology. Together with the other composition identity, this characterizes the
lift uniquely. -/
@[simp]
theorem toCompactlyGenerated_comp_compactlyGeneratedCounit
    (g : @ContinuousMap Z X tZ (compactlyGenerated.{u} X)) :
    toCompactlyGenerated.{u}
      (@ContinuousMap.comp Z X X tZ (compactlyGenerated.{u} X) tX
        (compactlyGeneratedCounit.{u} X) g) = g :=
  rfl

end ContinuousMap

namespace ContinuousMap

variable {X : Type v} {Y : Type w} {Z : Type z}
variable [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]

/-- A continuous map remains continuous when both its source and target have
the CompHaus-test compactly generated topologies. Its function is unchanged. -/
def compactlyGeneratedMap (f : C(X, Y)) :
    @ContinuousMap X Y (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y) :=
  @ContinuousMap.mk X Y (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y)
    (f : X → Y)
    (@continuous_from_compactlyGenerated.{u} X Y tX (compactlyGenerated.{u} Y) f
      fun S g ↦
        (@continuous_to_compactlyGenerated_iff.{u} S Y inferInstance tY inferInstance
          (f ∘ g)).2 (f.continuous.comp g.continuous))

/-- Refining the topologies does not change the values of a continuous map. -/
@[simp]
theorem compactlyGeneratedMap_apply (f : C(X, Y)) (x : X) :
    compactlyGeneratedMap.{u} f x = f x :=
  rfl

/-- Refinement preserves the identity continuous map. -/
@[simp]
theorem compactlyGeneratedMap_id :
    compactlyGeneratedMap.{u} (ContinuousMap.id X) =
      @ContinuousMap.id X (compactlyGenerated.{u} X) :=
  rfl

/-- Refinement preserves composition of continuous maps. -/
theorem compactlyGeneratedMap_comp (g : C(Y, Z)) (f : C(X, Y)) :
    compactlyGeneratedMap.{u} (@ContinuousMap.comp X Y Z tX tY tZ g f) =
      @ContinuousMap.comp X Y Z (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y) (compactlyGenerated.{u} Z)
        (compactlyGeneratedMap.{u} g) (compactlyGeneratedMap.{u} f) :=
  rfl

/-- The outward comparisons commute with every continuous map. -/
theorem compactlyGeneratedCounit_naturality (f : C(X, Y)) :
    @ContinuousMap.comp X Y Y (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y) tY
      (compactlyGeneratedCounit.{u} Y) (compactlyGeneratedMap.{u} f) =
      @ContinuousMap.comp X X Y (compactlyGenerated.{u} X) tX tY
        f (compactlyGeneratedCounit.{u} X) :=
  rfl

end ContinuousMap

/-- The CompHaus-test compactly generated topology is `u`-compactly generated,
with no size or separation hypothesis on the original space. -/
instance instUCompactlyGeneratedSpaceCompactlyGenerated
    (A : Type v) [tA : TopologicalSpace A] :
    @UCompactlyGeneratedSpace.{u} A (compactlyGenerated.{u} A) := by
  let E := Σ (i : (S : CompHaus.{u}) × C(S, A)), i.fst
  let q : E → A := fun ⟨⟨_, f⟩, s⟩ ↦ f s
  have hE : UCompactlyGeneratedSpace.{u} E := inferInstance
  exact @uCompactlyGeneratedSpace_of_coinduced E A inferInstance
    (compactlyGenerated.{u} A) hE q continuous_coinduced_rng rfl

private theorem isQuotientMap_compHausEval (B : Type v) [TopologicalSpace B]
    [UCompactlyGeneratedSpace.{u} B] :
    Topology.IsQuotientMap
      (fun p : Σ (i : (S : CompHaus.{u}) × C(S, B)), i.fst ↦ p.1.2 p.2) := by
  refine ⟨⟨eq_compactlyGenerated (X := B)⟩, ?_⟩
  intro b
  exact ⟨⟨⟨CompHaus.of PUnit.{u + 1}, ContinuousMap.const _ b⟩, PUnit.unit⟩, rfl⟩

-- The evaluation domain need not be small. Distribute its sigma type over the
-- product, then descend along evaluation using local compactness of `P`.
private theorem continuous_prod_of_compHaus_restrictions
    {P : Type v} {B : Type w} {Y : Type z}
    [TopologicalSpace P] [TopologicalSpace B] [TopologicalSpace Y]
    [LocallyCompactSpace P] [UCompactlyGeneratedSpace.{u} B]
    (f : P × B → Y)
    (h : ∀ (S : CompHaus.{u}) (g : C(S, B)),
      Continuous (fun p : P × S ↦ f (p.1, g p.2))) : Continuous f := by
  let E := Σ (i : (S : CompHaus.{u}) × C(S, B)), i.fst
  let q : E → B := fun p ↦ p.1.2 p.2
  have hq : Topology.IsQuotientMap q := isQuotientMap_compHausEval.{u} B
  apply hq.continuous_lift_prod_right
  let e : E × P ≃ₜ Σ (i : (S : CompHaus.{u}) × C(S, B)), i.fst × P :=
    Homeomorph.sigmaProdDistrib
  have hSigma : Continuous
      (fun p : Σ (i : (S : CompHaus.{u}) × C(S, B)), i.fst × P ↦
        f (p.2.2, p.1.2 p.2.1)) := by
    apply continuous_sigma
    intro i
    exact (h i.1 i.2).comp continuous_swap
  exact (hSigma.comp e.continuous).comp continuous_swap

private theorem uCompactlyGeneratedSpace_compHaus_prod
    (S : CompHaus.{u}) (B : Type v) [TopologicalSpace B]
    [UCompactlyGeneratedSpace.{u} B] : UCompactlyGeneratedSpace.{u} (S × B) := by
  refine uCompactlyGeneratedSpace_of_continuous_maps.{u} ?_
  intro Y tY f h
  apply continuous_prod_of_compHaus_restrictions.{u} f
  intro T g
  -- Both factors belong to the probe universe, so this is a small probe.
  exact h (CompHaus.of (S × T))
    ⟨fun p ↦ (p.1, g p.2),
      continuous_fst.prodMk (g.continuous.comp continuous_snd)⟩

/-- The ordinary product of a locally compact `u`-compactly generated space
with a `u`-compactly generated space is `u`-compactly generated. -/
instance instUCompactlyGeneratedSpaceProdOfLocallyCompactSpace
    (P : Type v) (A : Type w) [TopologicalSpace P] [TopologicalSpace A]
    [UCompactlyGeneratedSpace.{u} P] [LocallyCompactSpace P]
    [UCompactlyGeneratedSpace.{u} A] : UCompactlyGeneratedSpace.{u} (P × A) := by
  refine uCompactlyGeneratedSpace_of_continuous_maps.{u} ?_
  intro Y tY f h
  apply continuous_prod_of_compHaus_restrictions.{u} f
  intro S g
  let : UCompactlyGeneratedSpace.{u} (S × P) :=
    uCompactlyGeneratedSpace_compHaus_prod.{u} S P
  let : UCompactlyGeneratedSpace.{u} (P × S) :=
    uCompactlyGeneratedSpace_of_coinduced.{u}
      (Homeomorph.prodComm S P).continuous
      (Homeomorph.prodComm S P).isQuotientMap.eq_coinduced
  -- `P × S` can be large: use its source-test criterion, not a small-probe claim.
  apply continuous_from_uCompactlyGeneratedSpace.{u}
    (fun p : P × S ↦ f (p.1, g p.2))
  intro T k
  exact h T
    ⟨fun t ↦ ((k t).1, g (k t).2),
      (continuous_fst.comp k.continuous).prodMk
        (g.continuous.comp (continuous_snd.comp k.continuous))⟩

namespace Homeomorph

variable (P : Type v) (A : Type w)
variable [tP : TopologicalSpace P] [tA : TopologicalSpace A]
variable [UCompactlyGeneratedSpace.{u} P] [LocallyCompactSpace P]

/-- For a locally compact `u`-compactly generated space `P`, the identity
homeomorphism between the compactly generated topology on `P × A` and the
product of `P` with the compactly generated topology on `A`. No
compact-generation or separation hypothesis is imposed on `A`. -/
def compactlyGeneratedProd :
    @Homeomorph (P × A) (P × A) (compactlyGenerated.{u} (P × A))
      (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A)) := by
  let forward :
      @ContinuousMap (P × A) (P × A) (compactlyGenerated.{u} (P × A))
        (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A)) :=
    @ContinuousMap.prodMk (P × A) (compactlyGenerated.{u} (P × A))
      P A tP (compactlyGenerated.{u} A)
      (@ContinuousMap.comp (P × A) (P × A) P (compactlyGenerated.{u} (P × A))
        (@instTopologicalSpaceProd P A tP tA) tP
        (@ContinuousMap.fst P A tP tA)
        (ContinuousMap.compactlyGeneratedCounit.{u} (P × A)))
      (@ContinuousMap.compactlyGeneratedMap.{u} (P × A) A
        (@instTopologicalSpaceProd P A tP tA) tA
        (@ContinuousMap.snd P A tP tA))
  let backward :
      @ContinuousMap (P × A) (P × A)
        (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
        (compactlyGenerated.{u} (P × A)) :=
    @ContinuousMap.toCompactlyGenerated.{u} (P × A) (P × A)
      (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
      (@instTopologicalSpaceProd P A tP tA)
      (@instUCompactlyGeneratedSpaceProdOfLocallyCompactSpace.{u} P A tP
        (compactlyGenerated.{u} A) inferInstance inferInstance
        (@instUCompactlyGeneratedSpaceCompactlyGenerated.{u} A tA))
      (@ContinuousMap.prodMap P P A A tP tP (compactlyGenerated.{u} A) tA
        (@ContinuousMap.id P tP)
        (ContinuousMap.compactlyGeneratedCounit.{u} A))
  exact @Homeomorph.mk (P × A) (P × A) (compactlyGenerated.{u} (P × A))
    (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
    { toFun := _root_.id
      invFun := _root_.id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
    (@ContinuousMap.continuous_toFun (P × A) (P × A)
      (compactlyGenerated.{u} (P × A))
      (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A)) forward)
    (@ContinuousMap.continuous_toFun (P × A) (P × A)
      (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
      (compactlyGenerated.{u} (P × A)) backward)

/-- The product comparison does not change points. -/
@[simp]
theorem compactlyGeneratedProd_apply (p : P × A) :
    compactlyGeneratedProd.{u} P A p = p :=
  rfl

/-- The inverse product comparison does not change points. -/
@[simp]
theorem compactlyGeneratedProd_symm_apply (p : P × A) :
    (@Homeomorph.symm (P × A) (P × A) (compactlyGenerated.{u} (P × A))
      (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
      (compactlyGeneratedProd.{u} P A)) p = p :=
  rfl

/-- The product comparison commutes with the outward comparisons
as an equality of continuous maps. -/
@[simp]
theorem compactlyGeneratedProd_counit :
    @ContinuousMap.comp (P × A) (P × A) (P × A)
      (compactlyGenerated.{u} (P × A))
      (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
      (@instTopologicalSpaceProd P A tP tA)
      (@ContinuousMap.prodMap P P A A tP tP (compactlyGenerated.{u} A) tA
        (@ContinuousMap.id P tP)
        (ContinuousMap.compactlyGeneratedCounit.{u} A))
      (@_root_.toContinuousMap
        (@Homeomorph (P × A) (P × A) (compactlyGenerated.{u} (P × A))
          (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A)))
        (P × A) (P × A) (compactlyGenerated.{u} (P × A))
        (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
        inferInstance inferInstance (compactlyGeneratedProd.{u} P A)) =
        ContinuousMap.compactlyGeneratedCounit.{u} (P × A) := by
  refine @ContinuousMap.ext (P × A) (P × A) (compactlyGenerated.{u} (P × A))
    (@instTopologicalSpaceProd P A tP tA) _ _ ?_
  intro p
  rfl

end Homeomorph
