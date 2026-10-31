/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.DeckMonodromy
public import GroupTheory.GroupAction.Centralizer

/-!
# Normalizer quotients and deck transformations

For a covering with path-connected, locally path-connected total space, the
normalizer quotient of the based fundamental-group image is canonically the
deck group. The representative `n` acts by inverse right translation on the
monodromy orbit. The resulting evaluation law supplies the normal-direction
witness in the regularity criterion for the existing deck action on a fiber.

The construction composes the group-action normalizer classification with
covering monodromy and deck restriction.

## References

* May, *A Concise Course in Algebraic Topology*, Chapter 3, §§4 and 7, for
  the covering-space interpretation.
* `MulAction.normalizerQuotientEquivAut` and `Action.autEquivPermCentralizer`,
  for the group-action normalizer and centralizer equivalences.
* `IsCoveringMap.deckMonodromyEquivOfPathConnected`, for restriction to the
  occupied fiber and extension of its monodromy centralizer.
* `MulAction.isPretransitive_centralizer_iff_stabilizer_normal`, for the
  group-action regularity criterion.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

section EqualityTransport

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]
  [MulAction.IsPretransitive G X]

/-- Equality transport of the existing normalizer classification. -/
private def normalizerQuotientEquivAutOfEq (x : X) (H : Subgroup G)
    (h : H = MulAction.stabilizer G x) :
    (Subgroup.normalizer (H : Set G) ⧸
      H.subgroupOf (Subgroup.normalizer (H : Set G))) ≃*
        Aut (Action.ofMulAction G X) := by
  subst H
  exact MulAction.normalizerQuotientEquivAut x

private theorem normalizerQuotientEquivAutOfEq_mk_apply (x : X) (H : Subgroup G)
    (h : H = MulAction.stabilizer G x)
    (n : Subgroup.normalizer (H : Set G)) (g : G) :
    (normalizerQuotientEquivAutOfEq x H h (QuotientGroup.mk n)).hom.hom (g • x) =
      (g * (n : G)⁻¹) • x := by
  subst H
  exact MulAction.normalizerQuotientEquivAut_mk_apply x n g

end EqualityTransport

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B} (hp : IsCoveringMap p)

variable [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)

local notation "Γ" => FundamentalGroup B (p e₀)
local notation "F" => p ⁻¹' {p e₀}
local notation "x₀" =>
  (Subtype.mk e₀ (Set.mem_preimage.mpr (Set.mem_singleton (p e₀))) : F)
local notation "H" =>
  MonoidHom.range (FundamentalGroup.mapOfEq
    (ContinuousMap.mk p (IsCoveringMap.continuous hp)) rfl :
      FundamentalGroup E e₀ →* Γ)
local notation "N" =>
  Subgroup.normalizer (Set.range (FundamentalGroup.mapOfEq
    (ContinuousMap.mk p (IsCoveringMap.continuous hp)) rfl :
      FundamentalGroup E e₀ →* Γ))

omit [PathConnectedSpace E] [LocallyPathConnectedSpace E] in
private theorem monodromy_stabilizer_eq_range :
    @MulAction.stabilizer Γ F inferInstance (hp.fundamentalGroupMulAction (p e₀)) x₀ =
      H := by
  ext g
  exact hp.monodromy_eq_self_iff_mem_range x₀ g

/-- The normalizer quotient of the based fundamental-group image is canonically
isomorphic to the deck group. Its representatives act by inverse right
translation on monodromy orbits, with ordinary composition of deck maps.

See May, *A Concise Course in Algebraic Topology*, Chapter 3, §§4 and 7, and
`MulAction.normalizerQuotientEquivAut`. -/
def normalizerQuotientEquivDeck :
    (N ⧸ Subgroup.subgroupOf H N) ≃* deck p := private_decl% (by
  letI := hp.fundamentalGroupMulAction (p e₀)
  letI := hp.monodromy_isPretransitive (p e₀)
  exact (normalizerQuotientEquivAutOfEq x₀ H
    (hp.monodromy_stabilizer_eq_range e₀).symm).trans
      ((Action.autEquivPermCentralizer Γ F).trans
        (hp.deckMonodromyEquivOfPathConnected e₀).symm))

/-- The class of `n` sends the orbit point `g • x₀` to `(g * n⁻¹) • x₀`. -/
@[simp] theorem normalizerQuotientEquivDeck_mk_smul
    (n : N) (g : Γ) :
    hp.normalizerQuotientEquivDeck e₀
      (QuotientGroup.mk (α := N) (s := Subgroup.subgroupOf H N) n) • hp.monodromy g x₀ =
      hp.monodromy (g * (n : Γ)⁻¹ : Γ) x₀ := by
  let := hp.fundamentalGroupMulAction (p e₀)
  let := hp.monodromy_isPretransitive (p e₀)
  let a := normalizerQuotientEquivAutOfEq x₀ H
    (hp.monodromy_stabilizer_eq_range e₀).symm (QuotientGroup.mk n)
  apply Subtype.ext
  change (hp.deckMonodromyEquivOfPathConnected e₀).symm
    (Action.autEquivPermCentralizer Γ F a) • (hp.monodromy g x₀ : E) =
      (hp.monodromy (g * (n : Γ)⁻¹ : Γ) x₀ : E)
  calc
    _ = ((Action.autEquivPermCentralizer Γ F a).val (hp.monodromy g x₀)).val :=
      hp.deckMonodromyEquivOfPathConnected_symm_smul e₀
        (Action.autEquivPermCentralizer Γ F a) (hp.monodromy g x₀)
    _ = (a.hom.hom (hp.monodromy g x₀)).val :=
      congrArg (fun z : F => (z : E))
        (Action.autEquivPermCentralizer_apply (G := Γ) (X := F) a (hp.monodromy g x₀))
    _ = _ := congrArg (fun z : F => (z : E))
      (normalizerQuotientEquivAutOfEq_mk_apply x₀ H
        (hp.monodromy_stabilizer_eq_range e₀).symm n g)

/-- Evaluation at the chosen point fixes the inverse-translation convention. -/
@[simp] theorem normalizerQuotientEquivDeck_mk_smul_self
    (n : N) :
    hp.normalizerQuotientEquivDeck e₀
      (QuotientGroup.mk (α := N) (s := Subgroup.subgroupOf H N) n) • e₀ =
      (hp.monodromy ((n : Γ)⁻¹ : Γ) x₀ : E) := by
  let := hp.fundamentalGroupMulAction (p e₀)
  let := hp.monodromy_isPretransitive (p e₀)
  have h := hp.normalizerQuotientEquivDeck_mk_smul e₀ n (1 : Γ)
  change hp.normalizerQuotientEquivDeck e₀ (QuotientGroup.mk n) • ((1 : Γ) • x₀) =
    ((1 : Γ) * (n : Γ)⁻¹) • x₀ at h
  simp only [one_smul, one_mul] at h
  change hp.normalizerQuotientEquivDeck e₀ (QuotientGroup.mk n) • x₀ =
    hp.monodromy ((n : Γ)⁻¹ : Γ) x₀ at h
  simpa only [deck.coe_fiber_smul] using congrArg (fun z : F => (z : E)) h

/-- Recognize a normalizer representative by the value of its deck map at the
chosen point, without unfolding a quotient lift or deck extension. -/
theorem normalizerQuotientEquivDeck_symm_apply_eq_mk_iff
    (d : deck p) (n : N) :
    (hp.normalizerQuotientEquivDeck e₀).symm d = QuotientGroup.mk n ↔
      d • e₀ = (hp.monodromy ((n : Γ)⁻¹ : Γ) x₀ : E) := by
  rw [MulEquiv.symm_apply_eq]
  constructor
  · intro h
    rw [h, hp.normalizerQuotientEquivDeck_mk_smul_self]
  · intro h
    apply (deck.evalEmbedding hp.isSeparatedMap
      hp.isLocalHomeomorph.isLocallyInjective e₀).injective
    apply Subtype.ext
    change d • e₀ = hp.normalizerQuotientEquivDeck e₀ (QuotientGroup.mk n) • e₀
    rw [hp.normalizerQuotientEquivDeck_mk_smul_self]
    exact h

/-- The deck action on the occupied fiber is pretransitive exactly when the
based fundamental-group image is normal. No connectedness of the base or
surjectivity of the covering is required.

See May, *A Concise Course in Algebraic Topology*, Chapter 3, §§4 and 7, and
`MulAction.isPretransitive_centralizer_iff_stabilizer_normal`. -/
theorem isPretransitive_deck_iff_range_normal :
    @MulAction.IsPretransitive (deck p) F
      (deck.instMulActionFiber p (p e₀)).toSemigroupAction.toSMul ↔ Subgroup.Normal H := by
  let := hp.fundamentalGroupMulAction (p e₀)
  let := hp.monodromy_isPretransitive (p e₀)
  constructor
  · intro h
    let : MulAction.IsPretransitive (deck p) F := h
    have hC : MulAction.IsPretransitive
        (Subgroup.centralizer (Set.range (MulAction.toPermHom Γ F))) F := by
      constructor
      intro x y
      obtain ⟨d, hd⟩ := MulAction.exists_smul_eq (deck p) x y
      refine ⟨hp.deckMonodromyEquivOfPathConnected e₀ d, ?_⟩
      apply Subtype.ext
      change ((hp.deckMonodromyEquivOfPathConnected e₀ d).val x).val = y.val
      simpa only [hp.deckMonodromyEquivOfPathConnected_apply_coe,
        deck.coe_fiber_smul] using congrArg Subtype.val hd
    have hS := (MulAction.isPretransitive_centralizer_iff_stabilizer_normal
      (G := Γ) x₀).mp hC
    rwa [hp.monodromy_stabilizer_eq_range e₀] at hS
  · intro h
    let : Subgroup.Normal H := h
    apply MulAction.IsPretransitive.of_orbit (G := deck p) («x₀» := x₀)
    intro y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ x₀ y
    change hp.monodromy g x₀ = y at hg
    let n : N :=
      ⟨g⁻¹, by
        simpa only [MonoidHom.coe_range] using
          (show (g⁻¹ : Γ) ∈ Subgroup.normalizer (H : Set Γ) from by
            rw [Subgroup.normalizer_eq_top]
            exact Subgroup.mem_top _)⟩
    refine ⟨hp.normalizerQuotientEquivDeck e₀ (QuotientGroup.mk n), ?_⟩
    apply Subtype.ext
    rw [deck.coe_fiber_smul]
    change hp.normalizerQuotientEquivDeck e₀ (QuotientGroup.mk n) • e₀ = y.val
    rw [hp.normalizerQuotientEquivDeck_mk_smul_self]
    change (hp.monodromy ((g⁻¹)⁻¹ : Γ) x₀ : E) = y.val
    simpa only [inv_inv] using congrArg (fun z : F => (z : E)) hg

end IsCoveringMap

end
