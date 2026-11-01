/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Cube
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The radius of a finite cube

The radius of a point of a finite cube is the supremum norm of its coordinates
rescaled from `[0, 1]` to `[-1, 1]`. It is a continuous map to the unit interval,
equals one precisely on the coordinate-face boundary, and scales under radial
dilation in the rescaled coordinates. For an empty index type the radius is zero.

The construction uses Mathlib's finite-product norm and its continuity API.
-/

@[expose] public section

universe u

open scoped unitInterval Topology

namespace Cube

/-- The supremum norm of the coordinates rescaled to `[-1, 1]`, as a continuous
map to the unit interval. -/
noncomputable def radius (N : Type u) [Finite N] : C((N → I), I) := by
  classical
  letI := Fintype.ofFinite N
  refine
    { toFun := fun z => ⟨‖fun i : N => 2 * (z i : ℝ) - 1‖, norm_nonneg _, ?_⟩
      continuous_toFun := ?_ }
  · apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 from zero_le_one)).2
    intro i
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [(z i).property.1, (z i).property.2]
  · apply Continuous.subtype_mk
    exact (continuous_pi fun i =>
      (continuous_const.mul (continuous_apply i).subtype_val).sub continuous_const).norm

/-- Evaluation of the radius in terms of the finite-product norm, for any choice
of a `Fintype` instance. -/
@[simp]
theorem radius_apply {N : Type u} [Fintype N] (z : N → I) :
    (radius N z : ℝ) = ‖fun i : N => 2 * (z i : ℝ) - 1‖ := by
  classical
  exact congrArg (fun inst : Fintype N =>
    let : Fintype N := inst
    ‖fun i : N => 2 * (z i : ℝ) - 1‖)
    (Subsingleton.elim (Fintype.ofFinite N) ‹Fintype N›)

variable {N : Type u} [Finite N]

/-- Each rescaled coordinate is bounded in absolute value by the radius. -/
theorem abs_le_radius (z : N → I) (i : N) :
    |2 * (z i : ℝ) - 1| ≤ (radius N z : ℝ) := by
  classical
  let := Fintype.ofFinite N
  rw [radius_apply, ← Real.norm_eq_abs]
  exact norm_le_pi_norm (fun j : N => 2 * (z j : ℝ) - 1) i

/-- A point of a finite cube has radius one exactly when it belongs to a
coordinate face. -/
theorem radius_eq_one_iff (z : N → I) : radius N z = 1 ↔ z ∈ boundary N := by
  classical
  let := Fintype.ofFinite N
  constructor
  · intro hz
    have hr : ‖fun i : N => 2 * (z i : ℝ) - 1‖ = 1 := by
      rw [← radius_apply z, hz, Set.Icc.coe_one]
    have hn : ¬ ∀ i : N, ‖2 * (z i : ℝ) - 1‖ < 1 := by
      intro hi
      have hlt := (pi_norm_lt_iff (show (0 : ℝ) < 1 from zero_lt_one)).2 hi
      rw [hr] at hlt
      exact (lt_irrefl (1 : ℝ)) hlt
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hi' : 1 ≤ |2 * (z i : ℝ) - 1| := by
      simpa only [Real.norm_eq_abs] using (not_lt.mp hi)
    refine ⟨i, ?_⟩
    by_cases hnonneg : 0 ≤ 2 * (z i : ℝ) - 1
    · right
      apply Subtype.ext
      change (z i : ℝ) = 1
      rw [abs_of_nonneg hnonneg] at hi'
      linarith [(z i).property.2]
    · left
      apply Subtype.ext
      change (z i : ℝ) = 0
      rw [abs_of_neg (lt_of_not_ge hnonneg)] at hi'
      linarith [(z i).property.1]
  · rintro ⟨i, hi⟩
    apply Subtype.ext
    change (radius N z : ℝ) = 1
    apply le_antisymm (radius N z).property.2
    rcases hi with hi | hi
    · simpa [hi] using abs_le_radius z i
    · convert abs_le_radius z i using 1
      norm_num [hi]

/-- The cube with no coordinates has radius zero. -/
@[simp]
theorem radius_of_isEmpty [IsEmpty N] (z : N → I) : radius N z = 0 := by
  classical
  let := Fintype.ofFinite N
  apply Subtype.ext
  change (radius N z : ℝ) = 0
  rw [radius_apply, show (fun i : N => 2 * (z i : ℝ) - 1) = 0 from
    funext fun i => isEmptyElim i, norm_zero]

/-- A nonnegative dilation of the rescaled coordinates multiplies the radius
by the dilation factor. -/
theorem radius_scale (z w : N → I) (a : ℝ) (ha : 0 ≤ a)
    (h : ∀ i, 2 * (w i : ℝ) - 1 = a * (2 * (z i : ℝ) - 1)) :
    (radius N w : ℝ) = a * (radius N z : ℝ) := by
  classical
  let := Fintype.ofFinite N
  rw [radius_apply, radius_apply]
  have hw : (fun i : N => 2 * (w i : ℝ) - 1) =
      a • (fun i : N => 2 * (z i : ℝ) - 1) := funext h
  rw [hw, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]

end Cube
