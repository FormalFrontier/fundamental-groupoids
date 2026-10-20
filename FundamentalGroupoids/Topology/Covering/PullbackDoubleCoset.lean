/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Pullback
public import GroupTheory.GroupAction.DoubleCoset
public import Mathlib.Logic.Equiv.Basic

/-!
# Path components of pullback coverings and double cosets

For two coverings with path-connected total spaces and points over `b`, the path
components of their pullback correspond to double cosets of the two induced
fundamental-group images in `FundamentalGroup B b`. The base need not be path-connected:
every pullback point maps into the component of `b`, because either total space is
path-connected and has a specified point over `b`.

The construction composes the existing arbitrary-base monodromy/component-map-fiber
equivalence, the pullback-fiber comparison, the stock orbit–stabilizer/coset
identifications, and the product-coset-orbit/double-coset equivalence. The action
on the pullback fiber is its canonical covering monodromy.

With the stock multiplication `γ * δ = δ.trans γ`, the component with coordinates
`(γ • e₁, δ • e₂)` maps to `H (γ⁻¹ * δ) K`. The inverse sends `H g K` to the component
of `(e₁, g • e₂)`. The subgroups need not be normal.

## References

* `FundamentalGroupoids.Topology.Covering.Components`, for the component-map-fiber equivalence.
* `Mathlib.GroupTheory.GroupAction.Quotient`, for the existing orbit–stabilizer equivalence.
* `GroupTheory.GroupAction.Quotient`, for its equivariance with independent universes.
* `GroupTheory.GroupAction.DoubleCoset`, for diagonal product-coset orbits and double cosets.
-/

@[expose] public section

universe u₁ u₂ v

namespace IsCoveringMap

private theorem transitiveCosetEquiv_apply_mk
    {A : Type v} [Group A] {X : Type u₁} [MulAction A X]
    [MulAction.IsPretransitive A X] (x : X) {L : Subgroup A}
    (h : MulAction.stabilizer A x = L) (a : A) :
    ((Subgroup.quotientEquivOfEq h.symm).trans
      (((MulAction.orbitEquivQuotientStabilizer A x).symm.trans
        (Set.equivOfEq (MulAction.orbit_eq_univ A x))).trans
          (Equiv.Set.univ X))) (QuotientGroup.mk a) = a • x := by
  rw [Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk]
  rfl

private theorem transitiveCosetEquiv_symm_apply_smul
    {A : Type v} [Group A] {X : Type u₁} [MulAction A X]
    [MulAction.IsPretransitive A X] (x : X) {L : Subgroup A}
    (h : MulAction.stabilizer A x = L) (a : A) :
    ((Subgroup.quotientEquivOfEq h.symm).trans
      (((MulAction.orbitEquivQuotientStabilizer A x).symm.trans
        (Set.equivOfEq (MulAction.orbit_eq_univ A x))).trans
          (Equiv.Set.univ X))).symm (a • x) = QuotientGroup.mk a := by
  rw [Equiv.symm_apply_eq]
  exact (transitiveCosetEquiv_apply_mk x h a).symm

private theorem transitiveCosetEquiv_smul
    {A : Type v} [Group A] {X : Type u₁} [MulAction A X]
    [MulAction.IsPretransitive A X] (x : X) {L : Subgroup A}
    (h : MulAction.stabilizer A x = L) (a : A) (q : A ⧸ L) :
    ((Subgroup.quotientEquivOfEq h.symm).trans
      (((MulAction.orbitEquivQuotientStabilizer A x).symm.trans
        (Set.equivOfEq (MulAction.orbit_eq_univ A x))).trans
          (Equiv.Set.univ X))) (a • q) =
      a • ((Subgroup.quotientEquivOfEq h.symm).trans
        (((MulAction.orbitEquivQuotientStabilizer A x).symm.trans
          (Set.equivOfEq (MulAction.orbit_eq_univ A x))).trans
            (Equiv.Set.univ X))) q := by
  have hq : Subgroup.quotientEquivOfEq h.symm (a • q) =
      a • Subgroup.quotientEquivOfEq h.symm q := by
    refine Quotient.inductionOn' q ?_
    intro g
    simp only [MulAction.Quotient.smul_mk, Subgroup.quotientEquivOfEq_mk]
  change ((MulAction.orbitEquivQuotientStabilizer A x).symm
      (Subgroup.quotientEquivOfEq h.symm (a • q))).val =
    a • ((MulAction.orbitEquivQuotientStabilizer A x).symm
      (Subgroup.quotientEquivOfEq h.symm q)).val
  rw [hq]
  exact congrArg Subtype.val
    (MulAction.orbitEquivQuotientStabilizer_symm_smul x a _)

variable {E₁ : Type u₁} {E₂ : Type u₂} {B : Type v}
  [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace B]
  {f₁ : E₁ → B} {f₂ : E₂ → B}
  (cov₁ : IsCoveringMap f₁) (cov₂ : IsCoveringMap f₂)
  (b : B) (e₁ : f₁ ⁻¹' {b}) (e₂ : f₂ ⁻¹' {b})

local notation "G" => FundamentalGroup B b
local notation "F₁" => Set.preimage f₁ (Singleton.singleton b : Set B)
local notation "F₂" => Set.preimage f₂ (Singleton.singleton b : Set B)
local notation "H" =>
  MonoidHom.range (FundamentalGroup.mapOfEq
    (ContinuousMap.mk f₁ (IsCoveringMap.continuous cov₁)) (Subtype.property e₁))
local notation "K" =>
  MonoidHom.range (FundamentalGroup.mapOfEq
    (ContinuousMap.mk f₂ (IsCoveringMap.continuous cov₂)) (Subtype.property e₂))

local notation "A₁" => cov₁.fundamentalGroupMulAction b
local notation "A₂" => cov₂.fundamentalGroupMulAction b
local notation "A₁₂" => @Prod.mulAction G F₁ F₂ _ A₁ A₂

/-- Path components of the pullback correspond to double cosets of the canonical
images of the two based fundamental groups. Only the total spaces are assumed
path-connected; no path-connectedness of the base is required. -/
noncomputable def pullbackZerothHomotopyEquivDoubleCoset
    [PathConnectedSpace E₁] [PathConnectedSpace E₂] :
    ZerothHomotopy (f₁.Pullback f₂) ≃
      DoubleCoset.Quotient (H : Set G) (K : Set G) := by
  letI := A₁
  letI := A₂
  haveI : @MulAction.IsPretransitive G F₁ (A₁).toSemigroupAction.toSMul :=
    cov₁.monodromy_isPretransitive b
  haveI : @MulAction.IsPretransitive G F₂ (A₂).toSemigroupAction.toSMul :=
    cov₂.monodromy_isPretransitive b
  let covP := cov₁.pullback_base cov₂
  let hconst : ∀ c : ZerothHomotopy (f₁.Pullback f₂),
      @Quotient.map (f₁.Pullback f₂) B (pathSetoid (f₁.Pullback f₂)) (pathSetoid B)
        (fun z ↦ f₁ z.fst) (fun _ _ h ↦ h.map covP.continuous) c =
          ZerothHomotopy.mk b := by
    intro c
    obtain ⟨z, rfl⟩ := ZerothHomotopy.mk_surjective c
    change ZerothHomotopy.mk (f₁ z.fst) = ZerothHomotopy.mk b
    apply Quotient.sound
    change Joined (f₁ z.fst) b
    have he₁ : f₁ e₁.val = b := e₁.property
    simpa only [he₁] using
      (PathConnectedSpace.joined z.fst e₁.val).map cov₁.continuous
  let h₁ : MulAction.stabilizer G e₁ = H := by
    ext γ
    exact cov₁.monodromy_eq_self_iff_mem_range e₁ γ
  let h₂ : MulAction.stabilizer G e₂ = K := by
    ext γ
    exact cov₂.monodromy_eq_self_iff_mem_range e₂ γ
  let c₁ : (G ⧸ H) ≃ F₁ :=
    (Subgroup.quotientEquivOfEq h₁.symm).trans
      (((MulAction.orbitEquivQuotientStabilizer G e₁).symm.trans
        (Set.equivOfEq (MulAction.orbit_eq_univ G e₁))).trans
          (Equiv.Set.univ F₁))
  let c₂ : (G ⧸ K) ≃ F₂ :=
    (Subgroup.quotientEquivOfEq h₂.symm).trans
      (((MulAction.orbitEquivQuotientStabilizer G e₂).symm.trans
        (Set.equivOfEq (MulAction.orbit_eq_univ G e₂))).trans
          (Equiv.Set.univ F₂))
  -- Equivariance of the orbit–stabilizer equivalence gives the quotient congruence.
  let orbitDC : @MulAction.orbitRel.Quotient G (F₁ × F₂) _ A₁₂ ≃
      DoubleCoset.Quotient (H : Set G) (K : Set G) :=
    (Quotient.congr
      (ra := @MulAction.orbitRel G (F₁ × F₂) _ A₁₂)
      (rb := MulAction.orbitRel G ((G ⧸ H) × (G ⧸ K)))
      (Equiv.prodCongr c₁ c₂).symm (by
        have hc (a : G) (q : (G ⧸ H) × (G ⧸ K)) :
            (Equiv.prodCongr c₁ c₂) (a • q) =
              a • (Equiv.prodCongr c₁ c₂) q := by
          apply Prod.ext
          · exact transitiveCosetEquiv_smul e₁ h₁ a q.1
          · exact transitiveCosetEquiv_smul e₂ h₂ a q.2
        intro x y
        change (∃ a : G, a • y = x) ↔
          ∃ a : G, a • (Equiv.prodCongr c₁ c₂).symm y =
            (Equiv.prodCongr c₁ c₂).symm x
        constructor
        · rintro ⟨a, ha⟩
          refine ⟨a, ?_⟩
          apply (Equiv.prodCongr c₁ c₂).injective
          rw [hc, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
          exact ha
        · rintro ⟨a, ha⟩
          refine ⟨a, ?_⟩
          have heq := congrArg (Equiv.prodCongr c₁ c₂) ha
          simpa only [hc, Equiv.apply_symm_apply] using heq)).trans
        (MulAction.orbitQuotientProdQuotientEquivDoubleCoset H K)
  exact ((((covP.monodromyOrbitEquivZerothHomotopyFiber b).trans
    (Equiv.subtypeUnivEquiv hconst)).symm.trans
      (cov₁.pullbackFiberOrbitEquivProd cov₂ b)).trans orbitDC)

variable [PathConnectedSpace E₁] [PathConnectedSpace E₂]

/-- The relative product is `γ⁻¹ * δ`, with Mathlib's stock fundamental-group multiplication. -/
@[simp] theorem pullbackZerothHomotopyEquivDoubleCoset_apply (γ δ : G) :
    cov₁.pullbackZerothHomotopyEquivDoubleCoset cov₂ b e₁ e₂
      (ZerothHomotopy.mk
        ((Function.Pullback.fiberEquiv f₁ f₂ b).symm
          (cov₁.monodromy γ e₁, cov₂.monodromy δ e₂)).val) =
      DoubleCoset.mk H K (γ⁻¹ * δ) := by
  let := A₁
  let := A₂
  have : @MulAction.IsPretransitive G F₁ (A₁).toSemigroupAction.toSMul :=
    cov₁.monodromy_isPretransitive b
  have : @MulAction.IsPretransitive G F₂ (A₂).toSemigroupAction.toSMul :=
    cov₂.monodromy_isPretransitive b
  unfold pullbackZerothHomotopyEquivDoubleCoset
  simp only [Equiv.trans_apply, Equiv.symm_trans_apply,
    Equiv.subtypeUnivEquiv_symm_apply]
  rw [monodromyOrbitEquivZerothHomotopyFiber_symm_apply
    (cov₁.pullback_base cov₂) b
    ((Function.Pullback.fiberEquiv f₁ f₂ b).symm
      (cov₁.monodromy γ e₁, cov₂.monodromy δ e₂))]
  rw [pullbackFiberOrbitEquivProd_apply_mk, Equiv.apply_symm_apply,
    Quotient.congr_mk]
  change MulAction.orbitQuotientProdQuotientEquivDoubleCoset H K
    (Quotient.mk (MulAction.orbitRel G ((G ⧸ H) × (G ⧸ K)))
      (_, _)) = _
  have h₁ : MulAction.stabilizer G e₁ = H := by
    ext a
    exact cov₁.monodromy_eq_self_iff_mem_range e₁ a
  have h₂ : MulAction.stabilizer G e₂ = K := by
    ext a
    exact cov₂.monodromy_eq_self_iff_mem_range e₂ a
  have hc₁ :
      ((Subgroup.quotientEquivOfEq h₁.symm).trans
        (((MulAction.orbitEquivQuotientStabilizer G e₁).symm.trans
          (Set.equivOfEq (MulAction.orbit_eq_univ G e₁))).trans
            (Equiv.Set.univ F₁))).symm (cov₁.monodromy γ e₁) =
        (QuotientGroup.mk γ : G ⧸ H) :=
    transitiveCosetEquiv_symm_apply_smul e₁ h₁ γ
  have hc₂ :
      ((Subgroup.quotientEquivOfEq h₂.symm).trans
        (((MulAction.orbitEquivQuotientStabilizer G e₂).symm.trans
          (Set.equivOfEq (MulAction.orbit_eq_univ G e₂))).trans
            (Equiv.Set.univ F₂))).symm (cov₂.monodromy δ e₂) =
        (QuotientGroup.mk δ : G ⧸ K) :=
    transitiveCosetEquiv_symm_apply_smul e₂ h₂ δ
  rw [hc₁, hc₂]
  exact MulAction.orbitQuotientProdQuotientEquivDoubleCoset_apply_mk H K γ δ

/-- The inverse double-coset formula uses `g`, not `g⁻¹`, in the second coordinate. -/
@[simp] theorem pullbackZerothHomotopyEquivDoubleCoset_symm_apply (g : G) :
    (cov₁.pullbackZerothHomotopyEquivDoubleCoset cov₂ b e₁ e₂).symm
        (DoubleCoset.mk H K g) =
      ZerothHomotopy.mk
        ((Function.Pullback.fiberEquiv f₁ f₂ b).symm
          (e₁, cov₂.monodromy g e₂)).val := by
  let := A₁
  apply (cov₁.pullbackZerothHomotopyEquivDoubleCoset cov₂ b e₁ e₂).injective
  rw [Equiv.apply_symm_apply]
  symm
  simpa only [show cov₁.monodromy (1 : G) e₁ = e₁ from one_smul G e₁,
    inv_one, one_mul] using
    cov₁.pullbackZerothHomotopyEquivDoubleCoset_apply cov₂ b e₁ e₂ 1 g

/-- Equality of these path components is exactly equality of their relative double cosets. -/
theorem pullback_components_eq_iff (γ δ γ' δ' : G) :
    ZerothHomotopy.mk
        ((Function.Pullback.fiberEquiv f₁ f₂ b).symm
          (cov₁.monodromy γ e₁, cov₂.monodromy δ e₂)).val =
      ZerothHomotopy.mk
        ((Function.Pullback.fiberEquiv f₁ f₂ b).symm
          (cov₁.monodromy γ' e₁, cov₂.monodromy δ' e₂)).val ↔
      DoubleCoset.mk H K (γ⁻¹ * δ) = DoubleCoset.mk H K (γ'⁻¹ * δ') := by
  rw [← pullbackZerothHomotopyEquivDoubleCoset_apply cov₁ cov₂ b e₁ e₂ γ δ,
    ← pullbackZerothHomotopyEquivDoubleCoset_apply cov₁ cov₂ b e₁ e₂ γ' δ']
  exact (cov₁.pullbackZerothHomotopyEquivDoubleCoset cov₂ b e₁ e₂).injective.eq_iff.symm

end IsCoveringMap
