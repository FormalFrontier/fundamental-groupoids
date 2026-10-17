/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Covering.DeckMonodromy
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Concrete maps of covering spaces

The standard projection `ℝ → AddCircle (1 : ℝ)` is a continuous map over the
identity circle cover. Its equivariant fiber map is not injective: zero and one
have the same image. The public restriction and both public equivalences between
map spaces recover an independently constructed constant fiber map. An equivalence
between these map spaces does not require its individual fiber maps to be bijective.

The full equivalence also applies when both total spaces are empty over `Unit`.
No point of either empty total space is supplied.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §7, for maps
  of covering spaces and equivariant maps of fibers.
* Mathlib's covering maps (Thomas Browning), lifting and monodromy (Junyan Xu),
  additive circle (Oliver Nash), and equivariant maps (Kenny Lau and Antoine Chambert-Loir).
* The covering-map and monodromy constructions of `SphereTopology`.
-/

noncomputable section

private abbrev S := AddCircle (1 : ℝ)

private abbrev circleProjection : ℝ → S := (↑)

private theorem circleCover : IsCoveringMap circleProjection :=
  AddCircle.isCoveringMap_coe (1 : ℝ)

private theorem circleIdentityCover : IsCoveringMap (id : S → S) :=
  (isLocalHomeomorph_iff_isCoveringMap).mp
    (Homeomorph.refl S).isLocalHomeomorph

private def circleOverMap : {f : C(ℝ, S) // (id : S → S) ∘ f = circleProjection} :=
  ⟨⟨circleProjection, circleCover.continuous⟩, rfl⟩

private def circleFiberZero : circleProjection ⁻¹' {0} :=
  ⟨0, AddCircle.coe_zero _⟩

private def circleFiberOne : circleProjection ⁻¹' {0} :=
  ⟨1, AddCircle.coe_period _⟩

private theorem circleFiberZero_ne_one : circleFiberZero ≠ circleFiberOne := by
  intro h
  exact zero_ne_one (congrArg Subtype.val h)

private theorem circleIdFiberSubsingleton : Subsingleton ((id : S → S) ⁻¹' {0}) :=
  ⟨fun e e' ↦ Subtype.ext (e.property.trans e'.property.symm)⟩

-- This map is constructed independently of restriction. The canonical action
-- dictionaries belong to the specified covers; no replacement instances are chosen.
private def circleFiberHom :
    @MulActionHom (FundamentalGroup S 0) (FundamentalGroup S 0)
      (@id (FundamentalGroup S 0))
      (circleProjection ⁻¹' {0}) (circleCover.fundamentalGroupMulAction 0).toSemigroupAction.toSMul
      ((id : S → S) ⁻¹' {0})
      (circleIdentityCover.fundamentalGroupMulAction 0).toSemigroupAction.toSMul :=
  @MulActionHom.mk (FundamentalGroup S 0) (FundamentalGroup S 0)
    (@id (FundamentalGroup S 0))
    (circleProjection ⁻¹' {0}) (circleCover.fundamentalGroupMulAction 0).toSemigroupAction.toSMul
    ((id : S → S) ⁻¹' {0})
    (circleIdentityCover.fundamentalGroupMulAction 0).toSemigroupAction.toSMul
    (fun _ ↦ ⟨0, rfl⟩) (fun _ _ ↦ @Subsingleton.elim _ circleIdFiberSubsingleton _ _)

private theorem circleFiberHom_apply (e : circleProjection ⁻¹' {0}) :
    (circleFiberHom e).val = circleOverMap.val e.val :=
  e.property.symm

private theorem circleFiberHom_same_image :
    circleFiberHom circleFiberZero = circleFiberHom circleFiberOne :=
  @Subsingleton.elim _ circleIdFiberSubsingleton _ _

private theorem circleFiberHom_not_injective : ¬ Function.Injective circleFiberHom := by
  intro h
  exact circleFiberZero_ne_one (h circleFiberHom_same_image)

private theorem circleFiberHom_not_bijective : ¬ Function.Bijective circleFiberHom :=
  fun h ↦ circleFiberHom_not_injective h.1

private theorem circleRestriction_apply (e : circleProjection ⁻¹' {0}) :
    ((circleCover.fiberMap circleIdentityCover 0 circleOverMap) e).val =
      circleOverMap.val e.val :=
  circleCover.fiberMap_apply_coe circleIdentityCover 0 circleOverMap e

private theorem circleRestriction_eq :
    circleCover.fiberMap circleIdentityCover 0 circleOverMap = circleFiberHom := by
  apply DFunLike.ext
  intro e
  apply Subtype.ext
  rw [circleRestriction_apply]
  exact (circleFiberHom_apply e).symm

private theorem circleOccupied_forward :
    circleCover.fiberMapEquivOfPathConnected circleIdentityCover (0 : ℝ) circleOverMap =
      circleFiberHom := by
  apply (circleCover.fiberMapEquivOfPathConnected_apply_eq_iff circleIdentityCover (0 : ℝ)
    circleOverMap circleFiberHom).mpr
  exact fun e ↦ (circleFiberHom_apply e).symm

private theorem circleFull_forward :
    circleCover.fiberMapEquiv circleIdentityCover (0 : S) circleOverMap =
      circleFiberHom := by
  apply (circleCover.fiberMapEquiv_apply_eq_iff circleIdentityCover (0 : S)
    circleOverMap circleFiberHom).mpr
  exact fun e ↦ (circleFiberHom_apply e).symm

private def emptyProjection : Empty → Unit := Empty.elim

private theorem emptyCover : IsCoveringMap emptyProjection :=
  IsCoveringMap.of_isEmpty _

private def emptyOverMap : {f : C(Empty, Empty) // emptyProjection ∘ f = emptyProjection} :=
  ⟨⟨Empty.elim, continuous_of_discreteTopology⟩, funext fun e ↦ Empty.elim e⟩

private def emptyFiberHom :
    @MulActionHom (FundamentalGroup Unit ()) (FundamentalGroup Unit ())
      (@id (FundamentalGroup Unit ()))
      (emptyProjection ⁻¹' {()}) (emptyCover.fundamentalGroupMulAction ()).toSemigroupAction.toSMul
      (emptyProjection ⁻¹' {()})
      (emptyCover.fundamentalGroupMulAction ()).toSemigroupAction.toSMul :=
  @MulActionHom.mk (FundamentalGroup Unit ()) (FundamentalGroup Unit ())
    (@id (FundamentalGroup Unit ()))
    (emptyProjection ⁻¹' {()}) (emptyCover.fundamentalGroupMulAction ()).toSemigroupAction.toSMul
    (emptyProjection ⁻¹' {()}) (emptyCover.fundamentalGroupMulAction ()).toSemigroupAction.toSMul
    (fun e ↦ Empty.elim e.val) (fun _ e ↦ Empty.elim e.val)

private theorem emptyFull_forward :
    emptyCover.fiberMapEquiv emptyCover () emptyOverMap = emptyFiberHom := by
  apply (emptyCover.fiberMapEquiv_apply_eq_iff emptyCover () emptyOverMap emptyFiberHom).mpr
  exact fun e ↦ Empty.elim e.val
