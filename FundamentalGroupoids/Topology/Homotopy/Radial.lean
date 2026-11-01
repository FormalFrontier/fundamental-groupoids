/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Tactic.Ring

/-!
# Radial deformation of a punctured closed ball

In a real normed space, radial projection retracts a positive-radius closed ball
with its centre removed onto its metric sphere. Interpolating the radial scaling
factor from one to the projection factor gives a homotopy relative to the sphere.
The retraction and this strong deformation yield a `ContinuousMap.HomotopyEquiv`.

No nontriviality, completeness or dimension hypothesis is required. In particular,
the constructions also apply when both the punctured ball and sphere are empty.
-/

public section

noncomputable section

universe u

open scoped unitInterval

namespace Metric

variable {E : Type u} [NormedAddCommGroup E]

private theorem puncturedClosedBall_norm_pos {r : ℝ}
    (z : ↥(closedBall (0 : E) r \ {0})) : 0 < ‖(z : E)‖ := by
  apply norm_pos_iff.mpr
  simpa only [Set.mem_singleton_iff] using z.property.2

private theorem puncturedClosedBall_norm_le {r : ℝ}
    (z : ↥(closedBall (0 : E) r \ {0})) : ‖(z : E)‖ ≤ r := by
  simpa only [mem_closedBall, dist_zero_right] using z.property.1

/-- The boundary sphere includes into the closed ball with its centre removed. -/
def sphereToPuncturedClosedBall (r : ℝ) (hr : 0 < r) :
    C(↥(sphere (0 : E) r), ↥(closedBall (0 : E) r \ {0})) := by
  exact
    { toFun z := ⟨z, by
        have hz : ‖(z : E)‖ = r := by
          simpa only [mem_sphere, dist_zero_right] using z.property
        constructor
        · simpa only [mem_closedBall, dist_zero_right, hz] using le_refl r
        · simpa only [Set.mem_singleton_iff] using
            (norm_pos_iff.mp (show 0 < ‖(z : E)‖ by rw [hz]; exact hr))⟩
      continuous_toFun := continuous_induced_rng.2 continuous_subtype_val }

/-- The sphere inclusion leaves the ambient vector unchanged. -/
@[simp]
theorem sphereToPuncturedClosedBall_apply (r : ℝ) (hr : 0 < r)
    (z : ↥(sphere (0 : E) r)) :
    (sphereToPuncturedClosedBall r hr z : E) = (z : E) := by
  rfl

private theorem radial_coefficient_pos (r : ℝ) (hr : 0 < r)
    (t : unitInterval) (z : ↥(closedBall (0 : E) r \ {0})) :
    0 < (1 - (t : ℝ)) + (t : ℝ) * (r / ‖(z : E)‖) := by
  have hq : 0 < r / ‖(z : E)‖ := div_pos hr (puncturedClosedBall_norm_pos z)
  rcases lt_or_eq_of_le t.property.2 with ht | ht
  · exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht) (mul_nonneg t.property.1 hq.le)
  · simpa only [ht, sub_self, zero_add, one_mul] using hq

variable [NormedSpace ℝ E]

/-- Radial projection from a punctured closed ball onto its boundary sphere. -/
def puncturedClosedBallRetraction (r : ℝ) (hr : 0 < r) :
    C(↥(closedBall (0 : E) r \ {0}), ↥(sphere (0 : E) r)) := by
  exact
    { toFun z := ⟨(r / ‖(z : E)‖) • (z : E), by
        rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos hr (puncturedClosedBall_norm_pos z)),
          div_mul_cancel₀ _ (puncturedClosedBall_norm_pos z).ne']⟩
      continuous_toFun :=
        continuous_induced_rng.2
          ((continuous_const.div continuous_subtype_val.norm
            (fun z => (puncturedClosedBall_norm_pos z).ne')).smul
              continuous_subtype_val) }

/-- Radial projection scales a vector to norm `r`. -/
@[simp]
theorem puncturedClosedBallRetraction_apply (r : ℝ) (hr : 0 < r)
    (z : ↥(closedBall (0 : E) r \ {0})) :
    (puncturedClosedBallRetraction r hr z : E) = (r / ‖(z : E)‖) • (z : E) := by
  rfl

/-- Radial projection is the identity on the boundary sphere. -/
@[simp]
theorem puncturedClosedBallRetraction_sphereToPuncturedClosedBall
    (r : ℝ) (hr : 0 < r) (z : ↥(sphere (0 : E) r)) :
    puncturedClosedBallRetraction r hr (sphereToPuncturedClosedBall r hr z) = z := by
  apply Subtype.ext
  have hz : ‖(z : E)‖ = r := by
    simpa only [mem_sphere, dist_zero_right] using z.property
  simp only [puncturedClosedBallRetraction_apply, sphereToPuncturedClosedBall_apply,
    hz, div_self hr.ne', one_smul]

/-- The boundary inclusion followed by radial projection is the identity map. -/
@[simp]
theorem puncturedClosedBallRetraction_comp_sphereToPuncturedClosedBall
    (r : ℝ) (hr : 0 < r) :
    (puncturedClosedBallRetraction (E := E) r hr).comp
      (sphereToPuncturedClosedBall r hr) = ContinuousMap.id ↥(sphere (0 : E) r) := by
  apply ContinuousMap.ext
  intro z
  exact puncturedClosedBallRetraction_sphereToPuncturedClosedBall r hr z

private theorem radial_smul_norm (r : ℝ) (hr : 0 < r)
    (t : unitInterval) (z : ↥(closedBall (0 : E) r \ {0})) :
    ‖((1 - (t : ℝ)) + (t : ℝ) * (r / ‖(z : E)‖)) • (z : E)‖ =
      (1 - (t : ℝ)) * ‖(z : E)‖ + (t : ℝ) * r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (radial_coefficient_pos r hr t z),
    add_mul, mul_assoc, div_mul_cancel₀ _ (puncturedClosedBall_norm_pos z).ne']

private theorem radial_smul_mem (r : ℝ) (hr : 0 < r)
    (t : unitInterval) (z : ↥(closedBall (0 : E) r \ {0})) :
    ((1 - (t : ℝ)) + (t : ℝ) * (r / ‖(z : E)‖)) • (z : E) ∈
      closedBall (0 : E) r \ {0} := by
  constructor
  · rw [mem_closedBall, dist_zero_right, radial_smul_norm r hr t z]
    calc
      (1 - (t : ℝ)) * ‖(z : E)‖ + (t : ℝ) * r ≤
          (1 - (t : ℝ)) * r + (t : ℝ) * r :=
        add_le_add (mul_le_mul_of_nonneg_left (puncturedClosedBall_norm_le z)
          (sub_nonneg.mpr t.property.2)) le_rfl
      _ = r := by ring
  · simpa only [Set.mem_singleton_iff] using
      (smul_ne_zero (radial_coefficient_pos r hr t z).ne'
        (norm_pos_iff.mp (puncturedClosedBall_norm_pos z)))

/-- The punctured closed ball strongly deforms onto its boundary sphere.

The homotopy runs from the identity to inclusion after radial projection and
fixes every point whose ambient vector lies on the boundary sphere. -/
def puncturedClosedBallDeformation (r : ℝ) (hr : 0 < r) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id ↥(closedBall (0 : E) r \ {0}))
      ((sphereToPuncturedClosedBall r hr).comp (puncturedClosedBallRetraction r hr))
      {z | (z : E) ∈ sphere (0 : E) r} := by
  exact
    { toFun p := ⟨((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (r / ‖(p.2 : E)‖)) • (p.2 : E),
        radial_smul_mem r hr p.1 p.2⟩
      continuous_toFun := by
        have ht : Continuous (fun p : unitInterval × ↥(closedBall (0 : E) r \ {0}) =>
            (p.1 : ℝ)) := continuous_subtype_val.comp continuous_fst
        have hz : Continuous (fun p : unitInterval × ↥(closedBall (0 : E) r \ {0}) =>
            (p.2 : E)) := continuous_subtype_val.comp continuous_snd
        exact continuous_induced_rng.2
          (((continuous_const.sub ht).add (ht.mul (continuous_const.div hz.norm
            (fun p => (puncturedClosedBall_norm_pos p.2).ne')))).smul hz)
      map_zero_left z := by
        apply Subtype.ext
        change ((1 - (0 : ℝ)) + (0 : ℝ) * (r / ‖(z : E)‖)) • (z : E) = (z : E)
        simp
      map_one_left z := by
        apply Subtype.ext
        change ((1 - (1 : ℝ)) + (1 : ℝ) * (r / ‖(z : E)‖)) • (z : E) =
          (r / ‖(z : E)‖) • (z : E)
        simp
      prop' t z hz := by
        apply Subtype.ext
        have hznorm : ‖(z : E)‖ = r := by
          simpa only [Set.mem_ofPred_eq, mem_sphere, dist_zero_right] using hz
        change ((1 - (t : ℝ)) + (t : ℝ) * (r / ‖(z : E)‖)) • (z : E) = (z : E)
        rw [hznorm, div_self hr.ne', mul_one, sub_add_cancel, one_smul] }

/-- The strong radial deformation interpolates the scalar projection factor. -/
@[simp]
theorem puncturedClosedBallDeformation_apply (r : ℝ) (hr : 0 < r)
    (t : unitInterval) (z : ↥(closedBall (0 : E) r \ {0})) :
    (puncturedClosedBallDeformation r hr (t, z) : E) =
      ((1 - (t : ℝ)) + (t : ℝ) * (r / ‖(z : E)‖)) • (z : E) := by
  rfl

/-- The strong radial deformation starts at the identity. -/
theorem puncturedClosedBallDeformation_zero (r : ℝ) (hr : 0 < r)
    (z : ↥(closedBall (0 : E) r \ {0})) :
    puncturedClosedBallDeformation r hr (0, z) = z := by
  exact (puncturedClosedBallDeformation r hr).apply_zero z

/-- The strong radial deformation ends at inclusion after radial projection. -/
theorem puncturedClosedBallDeformation_one (r : ℝ) (hr : 0 < r)
    (z : ↥(closedBall (0 : E) r \ {0})) :
    puncturedClosedBallDeformation r hr (1, z) =
      sphereToPuncturedClosedBall r hr (puncturedClosedBallRetraction r hr z) := by
  exact (puncturedClosedBallDeformation r hr).apply_one z

/-- Every boundary point stays fixed throughout the strong radial deformation. -/
@[simp]
theorem puncturedClosedBallDeformation_boundary (r : ℝ) (hr : 0 < r)
    (t : unitInterval) (z : ↥(sphere (0 : E) r)) :
    puncturedClosedBallDeformation r hr (t, sphereToPuncturedClosedBall r hr z) =
      sphereToPuncturedClosedBall r hr z := by
  apply (puncturedClosedBallDeformation r hr).eq_fst t
  simpa only [Set.mem_ofPred_eq, sphereToPuncturedClosedBall_apply] using z.property

/-- A punctured positive-radius closed ball is homotopy equivalent to its sphere,
with radial projection as the forward map and boundary inclusion as the inverse. -/
def puncturedClosedBallHomotopyEquivSphere (r : ℝ) (hr : 0 < r) :
    ContinuousMap.HomotopyEquiv
      ↥(closedBall (0 : E) r \ {0}) ↥(sphere (0 : E) r) := by
  exact
    { toFun := puncturedClosedBallRetraction r hr
      invFun := sphereToPuncturedClosedBall r hr
      left_inv := ⟨(puncturedClosedBallDeformation r hr).toHomotopy.symm⟩
      right_inv := by
        simpa only [puncturedClosedBallRetraction_comp_sphereToPuncturedClosedBall] using
          (ContinuousMap.Homotopic.refl (ContinuousMap.id ↥(sphere (0 : E) r))) }

/-- The homotopy equivalence maps a punctured-ball point by radial projection. -/
@[simp]
theorem puncturedClosedBallHomotopyEquivSphere_apply (r : ℝ) (hr : 0 < r)
    (z : ↥(closedBall (0 : E) r \ {0})) :
    puncturedClosedBallHomotopyEquivSphere r hr z = puncturedClosedBallRetraction r hr z := by
  rfl

/-- The inverse homotopy equivalence is the inclusion of the sphere. -/
@[simp]
theorem puncturedClosedBallHomotopyEquivSphere_symm_apply (r : ℝ) (hr : 0 < r)
    (z : ↥(sphere (0 : E) r)) :
    (puncturedClosedBallHomotopyEquivSphere r hr).symm z =
      sphereToPuncturedClosedBall r hr z := by
  rfl

end Metric
