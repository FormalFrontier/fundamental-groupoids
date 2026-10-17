/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Covering.Lifting
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.NormNum

/-!
# Concrete based covering-lift models

The doubling cover of `AddCircle (1 : ℝ)` lifts nonconstant quadrupling by
doubling, on a path-connected, locally path-connected but not simply-connected
domain. The two-point discrete cover of a point shows why based uniqueness needs
a connected domain. All maps and covers below are constructed, not hypotheses.

The circle identity has no based lift through doubling: interval lift uniqueness
compares a hypothetical lift of the standard loop with `t ↦ [t / 2]`, whose
endpoint is nonzero. This also certifies that the circle domain is not simply
connected, using Mathlib's simply-connected lifting theorem. No winding numbers or
integer fundamental-group coordinates are used in this obstruction proof.

## References

The based criterion is that of May, *A Concise Course in Algebraic Topology*,
Chapter 3 §7. The covering and interval-lift uniqueness results are those of
Mathlib, in particular the covering-map work of Junyan Xu.
-/

noncomputable section

private abbrev S := AddCircle (1 : ℝ)

private theorem circle_pathConnected : PathConnectedSpace S := inferInstance

private theorem circle_locallyPathConnected : LocallyPathConnectedSpace S :=
  inferInstanceAs (LocallyPathConnectedSpace (Quotient _))

private def doubling : C(S, S) := ⟨fun x ↦ 2 • x, continuous_nsmul 2⟩

private def quadrupling : C(S, S) := ⟨fun x ↦ 4 • x, continuous_nsmul 4⟩

private theorem doubling_cover : IsCoveringMap (doubling : S → S) :=
  (AddCircle.isAddQuotientCoveringMap_nsmul_of_ne_zero (1 : ℝ) 2).isCoveringMap

private theorem doubling_zero : doubling 0 = 0 := by simp [doubling]

private theorem quadrupling_zero : quadrupling 0 = 0 := by simp [quadrupling]

private theorem circle_base : doubling 0 = quadrupling 0 :=
  doubling_zero.trans quadrupling_zero.symm

private theorem doubling_comp_doubling : doubling.comp doubling = quadrupling := by
  ext x
  change 2 • (2 • x) = 4 • x
  rw [← mul_smul]
  rfl

private theorem displayed_lift :
    doubling 0 = 0 ∧ (doubling : S → S) ∘ doubling = quadrupling := by
  refine ⟨doubling_zero, ?_⟩
  exact congrArg (fun g : C(S, S) ↦ (g : S → S)) doubling_comp_doubling

-- Extract the image condition from the displayed lift and covering-map
-- uniqueness, then use the opposite direction to recover unique lifting.
private theorem quadrupling_range_le :
    (FundamentalGroup.map quadrupling 0).range ≤
      (FundamentalGroup.mapOfEq ⟨doubling, doubling_cover.continuous⟩ circle_base).range := by
  let := circle_locallyPathConnected
  apply (doubling_cover.existsUnique_continuousMap_lifts_iff_range_le circle_base).mp
  refine ⟨doubling, displayed_lift, ?_⟩
  intro F hF
  apply ContinuousMap.coe_injective
  exact doubling_cover.eq_of_comp_eq F.continuous doubling.continuous
    (hF.2.trans displayed_lift.2.symm) 0 (hF.1.trans doubling_zero.symm)

private theorem circle_unique_lift :
    ∃! F : C(S, S), F 0 = 0 ∧ (doubling : S → S) ∘ F = quadrupling := by
  let := circle_locallyPathConnected
  exact (doubling_cover.existsUnique_continuousMap_lifts_iff_range_le circle_base).mpr
    quadrupling_range_le

section DisconnectedDomain

private abbrev Two := Fin 2

private def pointProjection : Two → Unit := fun _ ↦ ()

private theorem pointProjection_cover : IsCoveringMap pointProjection :=
  IsCoveringMap.of_discreteTopology pointProjection

private def pointMap : C(Two, Unit) := ContinuousMap.const _ ()

private def identityLift : C(Two, Two) := ContinuousMap.id _

private def zeroLift : C(Two, Two) := ContinuousMap.const _ 0

private theorem two_locallyPathConnected : LocallyPathConnectedSpace Two := inferInstance

private theorem two_not_preconnected : ¬ PreconnectedSpace Two := by
  intro h
  let := h
  have : Subsingleton Two := subsingleton_of_preconnected_totallyDisconnected
  have h01 : (0 : Two) = 1 := this.elim _ _
  exact (by decide : (0 : Two) ≠ 1) h01

private theorem two_not_pathConnected : ¬ PathConnectedSpace Two := by
  intro h
  let := h
  exact two_not_preconnected inferInstance

private theorem identityLift_based :
    identityLift 0 = 0 ∧ pointProjection ∘ identityLift = pointMap := ⟨rfl, rfl⟩

private theorem zeroLift_based :
    zeroLift 0 = 0 ∧ pointProjection ∘ zeroLift = pointMap := ⟨rfl, rfl⟩

private theorem lifts_differ_at_one : identityLift 1 ≠ zeroLift 1 := by decide

private theorem disconnected_nonunique :
    ¬ ∃! F : C(Two, Two), F 0 = 0 ∧ pointProjection ∘ F = pointMap := by
  rintro ⟨F, _, hF⟩
  have h := (hF identityLift identityLift_based).trans (hF zeroLift zeroLift_based).symm
  exact lifts_differ_at_one (congrArg (fun g : C(Two, Two) ↦ g 1) h)

end DisconnectedDomain

section CircleObstruction

private theorem half_ne_zero : (((1 / 2 : ℝ) : S)) ≠ 0 := by
  intro h
  have hreal : (1 / 2 : ℝ) = 0 :=
    (AddCircle.coe_eq_zero_iff_of_mem_Ico (p := (1 : ℝ))
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Ico 0 1)).mp h
  norm_num at hreal

private theorem quadrupling_nonconstant :
    quadrupling (((1 / 8 : ℝ) : S)) ≠ quadrupling 0 := by
  rw [quadrupling_zero]
  have h : quadrupling (((1 / 8 : ℝ) : S)) = ((1 / 2 : ℝ) : S) := by
    change 4 • (((1 / 8 : ℝ) : S)) = _
    rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul]
  rw [h]
  exact half_ne_zero

private def circleLoop : C(unitInterval, S) :=
  ⟨fun t ↦ ((t : ℝ) : S),
    (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val⟩

private def halfLoop : C(unitInterval, S) :=
  ⟨fun t ↦ (((t : ℝ) / 2 : ℝ) : S),
    (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_subtype_val.div_const 2)⟩

private theorem circleLoop_zero : circleLoop 0 = 0 := rfl

private theorem circleLoop_one : circleLoop 1 = 0 := AddCircle.coe_period (1 : ℝ)

private theorem halfLoop_zero : halfLoop 0 = 0 := by
  change (((0 : ℝ) / 2 : ℝ) : S) = 0
  norm_num [AddCircle.coe_zero]

private theorem halfLoop_one : halfLoop 1 = ((1 / 2 : ℝ) : S) := rfl

private theorem halfLoop_lifts (t : unitInterval) : doubling (halfLoop t) = circleLoop t := by
  change 2 • ((((t : ℝ) / 2 : ℝ) : S)) = ((t : ℝ) : S)
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  norm_num [mul_div_cancel₀]

-- Compare two lifts on the connected interval, not on a fundamental-group
-- coordinate model. Their endpoints are incompatible with a circle section.
private theorem identity_no_based_lift :
    ¬ ∃ F : C(S, S), F 0 = 0 ∧ (doubling : S → S) ∘ F = ContinuousMap.id S := by
  rintro ⟨F, hF0, hF⟩
  have hcomp : (doubling : S → S) ∘ F.comp circleLoop = doubling ∘ halfLoop := by
    funext t
    change doubling (F (circleLoop t)) = doubling (halfLoop t)
    rw [halfLoop_lifts]
    exact congrFun hF (circleLoop t)
  have h0 : (F.comp circleLoop) 0 = halfLoop 0 := by
    change F (circleLoop 0) = halfLoop 0
    rw [circleLoop_zero, halfLoop_zero, hF0]
  have hEq := doubling_cover.eq_of_comp_eq
    (F.comp circleLoop).continuous halfLoop.continuous hcomp 0 h0
  have h1 := congrFun hEq 1
  change F (circleLoop 1) = halfLoop 1 at h1
  rw [circleLoop_one, halfLoop_one, hF0] at h1
  exact half_ne_zero h1.symm

private theorem circle_not_simplyConnected : ¬ SimplyConnectedSpace S := by
  intro h
  let := h
  let := circle_locallyPathConnected
  obtain ⟨F, hF, _⟩ := doubling_cover.existsUnique_continuousMap_lifts
    (ContinuousMap.id S) 0 0 doubling_zero
  exact identity_no_based_lift ⟨F, hF⟩

end CircleObstruction
