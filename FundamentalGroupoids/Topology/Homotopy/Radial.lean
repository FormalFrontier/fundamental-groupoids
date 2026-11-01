/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Radial deformations of punctured balls

In a real normed space, radial projection retracts a positive-radius closed ball
with its centre removed onto its boundary sphere. The same normalization retracts
an open ball with its centre removed onto any positive-radius sphere strictly
inside it. Interpolating the radial scaling factor gives strong deformations and
`ContinuousMap.HomotopyEquiv`s, with radial projection forward and inclusion inverse.

The two constructions share a target-radius normalization and homotopy on nonzero
vectors. Convexity of the source ball supplies the respective closed or strict
radius bound. No nontriviality, completeness, dimension or nonemptiness hypothesis
is required; in particular the constructions cover the zero space.
-/

public section

noncomputable section

universe u

open scoped unitInterval

namespace Metric

variable {E : Type u} [NormedAddCommGroup E]

private theorem punctured_norm_pos {s : Set E}
    (z : ↥(s \ {0})) : 0 < ‖(z : E)‖ := by
  apply norm_pos_iff.mpr
  simpa only [Set.mem_singleton_iff] using z.property.2

private theorem radial_sphere_subset_closedBall (a r : ℝ) (har : a ≤ r) :
    sphere (0 : E) a ⊆ closedBall (0 : E) r := by
  intro z hz
  have hznorm : ‖z‖ = a := by
    simpa only [mem_sphere, dist_zero_right] using hz
  simpa only [mem_closedBall, dist_zero_right, hznorm] using har

private theorem radial_sphere_subset_ball (a r : ℝ) (har : a < r) :
    sphere (0 : E) a ⊆ ball (0 : E) r := by
  intro z hz
  have hznorm : ‖z‖ = a := by
    simpa only [mem_sphere, dist_zero_right] using hz
  simpa only [mem_ball, dist_zero_right, hznorm] using har

private def sphereToPuncturedSet {s : Set E} (a : ℝ) (ha : 0 < a)
    (hs : sphere (0 : E) a ⊆ s) : C(↥(sphere (0 : E) a), ↥(s \ {0})) := by
  exact
    { toFun z := ⟨z, by
        constructor
        · exact hs z.property
        · have hz : ‖(z : E)‖ = a := by
            simpa only [mem_sphere, dist_zero_right] using z.property
          simpa only [Set.mem_singleton_iff] using
            (norm_pos_iff.mp (show 0 < ‖(z : E)‖ by rw [hz]; exact ha))⟩
      continuous_toFun := continuous_induced_rng.2 continuous_subtype_val }

/-- The boundary sphere includes into the closed ball with its centre removed. -/
def sphereToPuncturedClosedBall (r : ℝ) (hr : 0 < r) :
    C(↥(sphere (0 : E) r), ↥(closedBall (0 : E) r \ {0})) := by
  exact sphereToPuncturedSet r hr (radial_sphere_subset_closedBall r r le_rfl)

/-- The sphere inclusion leaves the ambient vector unchanged. -/
@[simp]
theorem sphereToPuncturedClosedBall_apply (r : ℝ) (hr : 0 < r)
    (z : ↥(sphere (0 : E) r)) :
    (sphereToPuncturedClosedBall r hr z : E) = (z : E) := by
  rfl

/-- A positive-radius inner sphere includes into an open ball with its centre removed. -/
def sphereToPuncturedBall (a r : ℝ) (ha : 0 < a) (har : a < r) :
    C(↥(sphere (0 : E) a), ↥(ball (0 : E) r \ {0})) := by
  exact sphereToPuncturedSet a ha (radial_sphere_subset_ball a r har)

/-- Inclusion of an inner sphere leaves the ambient vector unchanged. -/
@[simp]
theorem sphereToPuncturedBall_apply (a r : ℝ) (ha : 0 < a) (har : a < r)
    (z : ↥(sphere (0 : E) a)) :
    (sphereToPuncturedBall a r ha har z : E) = (z : E) := by
  rfl

/-- The range of the inner-sphere inclusion is its ambient sphere predicate. -/
theorem sphereToPuncturedBall_range (a r : ℝ) (ha : 0 < a) (har : a < r) :
    Set.range (sphereToPuncturedBall (E := E) a r ha har) =
      {z : ↥(ball (0 : E) r \ {0}) | (z : E) ∈ sphere (0 : E) a} := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨s, rfl⟩
    simpa only [Set.mem_ofPred_eq, sphereToPuncturedBall_apply] using s.property
  · intro hz
    refine ⟨⟨(z : E), hz⟩, ?_⟩
    apply Subtype.ext
    rfl

private theorem radial_coefficient_pos (a : ℝ) (ha : 0 < a)
    (t : unitInterval) {n : ℝ} (hn : 0 < n) :
    0 < (1 - (t : ℝ)) + (t : ℝ) * (a / n) := by
  have hq : 0 < a / n := div_pos ha hn
  rcases lt_or_eq_of_le t.property.2 with ht | ht
  · exact add_pos_of_pos_of_nonneg (sub_pos.mpr ht) (mul_nonneg t.property.1 hq.le)
  · simpa only [ht, sub_self, zero_add, one_mul] using hq

variable [NormedSpace ℝ E]

private def radialNormalize (a : ℝ) (z : E) : E := (a / ‖z‖) • z

private def radialHomotopy (a : ℝ) (t : unitInterval) (z : E) : E :=
  ((1 - (t : ℝ)) + (t : ℝ) * (a / ‖z‖)) • z

private theorem radialNormalize_norm (a : ℝ) (ha : 0 < a)
    (z : E) (hz : 0 < ‖z‖) : ‖radialNormalize a z‖ = a := by
  rw [radialNormalize, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ha hz),
    div_mul_cancel₀ _ hz.ne']

private theorem radialHomotopy_norm (a : ℝ) (ha : 0 < a)
    (t : unitInterval) (z : E) (hz : 0 < ‖z‖) :
    ‖radialHomotopy a t z‖ = (1 - (t : ℝ)) * ‖z‖ + (t : ℝ) * a := by
  rw [radialHomotopy, norm_smul, Real.norm_eq_abs,
    abs_of_pos (radial_coefficient_pos a ha t hz), add_mul, mul_assoc,
    div_mul_cancel₀ _ hz.ne']

private theorem radialHomotopy_ne_zero (a : ℝ) (ha : 0 < a)
    (t : unitInterval) (z : E) (hz : 0 < ‖z‖) : radialHomotopy a t z ≠ 0 := by
  exact smul_ne_zero (radial_coefficient_pos a ha t hz).ne' (norm_pos_iff.mp hz)

private theorem radialHomotopy_zero (a : ℝ) (z : E) : radialHomotopy a 0 z = z := by
  change ((1 - (0 : ℝ)) + (0 : ℝ) * (a / ‖z‖)) • z = z
  simp

private theorem radialHomotopy_one (a : ℝ) (z : E) :
    radialHomotopy a 1 z = radialNormalize a z := by
  change ((1 - (1 : ℝ)) + (1 : ℝ) * (a / ‖z‖)) • z = (a / ‖z‖) • z
  simp

private theorem radialHomotopy_of_norm_eq (a : ℝ) (ha : 0 < a)
    (t : unitInterval) (z : E) (hz : ‖z‖ = a) : radialHomotopy a t z = z := by
  simp only [radialHomotopy, hz, div_self ha.ne', mul_one, sub_add_cancel, one_smul]

private theorem continuous_radialNormalize {X : Type*} [TopologicalSpace X]
    (a : ℝ) {f : X → E} (hf : Continuous f) (h0 : ∀ x, 0 < ‖f x‖) :
    Continuous (fun x => radialNormalize a (f x)) := by
  exact (continuous_const.div hf.norm (fun x => (h0 x).ne')).smul hf

private theorem continuous_radialHomotopy {X : Type*} [TopologicalSpace X]
    (a : ℝ) {t : X → unitInterval} {f : X → E}
    (ht : Continuous t) (hf : Continuous f) (h0 : ∀ x, 0 < ‖f x‖) :
    Continuous (fun x => radialHomotopy a (t x) (f x)) := by
  have ht' : Continuous (fun x => (t x : ℝ)) := continuous_subtype_val.comp ht
  exact (((continuous_const.sub ht').add (ht'.mul (continuous_const.div hf.norm
    (fun x => (h0 x).ne')))).smul hf)

private def puncturedSetProjection (s : Set E) (a : ℝ) (ha : 0 < a) :
    C(↥(s \ {0}), ↥(sphere (0 : E) a)) := by
  exact
    { toFun z := ⟨radialNormalize a (z : E), by
        simpa only [mem_sphere, dist_zero_right] using
          radialNormalize_norm a ha (z : E) (punctured_norm_pos z)⟩
      continuous_toFun :=
        continuous_induced_rng.2
          (continuous_radialNormalize a continuous_subtype_val
            (fun z => punctured_norm_pos z)) }

private theorem radialHomotopy_mem {s : Set E} (hs : Convex ℝ s)
    (a : ℝ) (ha : 0 < a) (hSphere : sphere (0 : E) a ⊆ s)
    (t : unitInterval) (z : ↥(s \ {0})) : radialHomotopy a t (z : E) ∈ s \ {0} := by
  constructor
  · have hproj : radialNormalize a (z : E) ∈ s := by
      apply hSphere
      simpa only [mem_sphere, dist_zero_right] using
        radialNormalize_norm a ha (z : E) (punctured_norm_pos z)
    have hline := hs.lineMap_mem z.property.1 hproj t.property
    simpa only [AffineMap.lineMap_apply_module, radialNormalize, radialHomotopy,
      smul_smul, ← add_smul] using hline
  · simpa only [Set.mem_singleton_iff] using
      radialHomotopy_ne_zero a ha t (z : E) (punctured_norm_pos z)

private def puncturedConvexDeformation {s : Set E} (hs : Convex ℝ s)
    (a : ℝ) (ha : 0 < a) (hSphere : sphere (0 : E) a ⊆ s) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id ↥(s \ {0}))
      ((sphereToPuncturedSet a ha hSphere).comp (puncturedSetProjection s a ha))
      {z | (z : E) ∈ sphere (0 : E) a} := by
  exact
    { toFun p := ⟨radialHomotopy a p.1 (p.2 : E),
        radialHomotopy_mem hs a ha hSphere p.1 p.2⟩
      continuous_toFun :=
        continuous_induced_rng.2
          (continuous_radialHomotopy a continuous_fst
            (continuous_subtype_val.comp continuous_snd)
            (fun p => punctured_norm_pos p.2))
      map_zero_left z := by
        apply Subtype.ext
        exact radialHomotopy_zero a (z : E)
      map_one_left z := by
        apply Subtype.ext
        exact radialHomotopy_one a (z : E)
      prop' t z hz := by
        apply Subtype.ext
        have hznorm : ‖(z : E)‖ = a := by
          simpa only [Set.mem_ofPred_eq, mem_sphere, dist_zero_right] using hz
        exact radialHomotopy_of_norm_eq a ha t (z : E) hznorm }

/-- Radial projection from a punctured closed ball onto its boundary sphere. -/
def puncturedClosedBallRetraction (r : ℝ) (hr : 0 < r) :
    C(↥(closedBall (0 : E) r \ {0}), ↥(sphere (0 : E) r)) := by
  exact puncturedSetProjection (closedBall (0 : E) r) r hr

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

/-- The punctured closed ball strongly deforms onto its boundary sphere.

The homotopy runs from the identity to inclusion after radial projection and
fixes every point whose ambient vector lies on the boundary sphere. -/
def puncturedClosedBallDeformation (r : ℝ) (hr : 0 < r) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id ↥(closedBall (0 : E) r \ {0}))
      ((sphereToPuncturedClosedBall r hr).comp (puncturedClosedBallRetraction r hr))
      {z | (z : E) ∈ sphere (0 : E) r} := by
  exact puncturedConvexDeformation (convex_closedBall (0 : E) r) r hr
    (radial_sphere_subset_closedBall r r le_rfl)

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

/-- Radial projection from a punctured open ball onto a positive-radius sphere.

The projection itself does not need the sphere to lie inside the source ball. -/
def puncturedBallRetraction (a r : ℝ) (ha : 0 < a) :
    C(↥(ball (0 : E) r \ {0}), ↥(sphere (0 : E) a)) := by
  exact puncturedSetProjection (ball (0 : E) r) a ha

/-- Radial projection from an open ball scales a vector to norm `a`. -/
@[simp]
theorem puncturedBallRetraction_apply (a r : ℝ) (ha : 0 < a)
    (z : ↥(ball (0 : E) r \ {0})) :
    (puncturedBallRetraction a r ha z : E) = (a / ‖(z : E)‖) • (z : E) := by
  rfl

/-- Radial projection fixes the included inner sphere. -/
@[simp]
theorem puncturedBallRetraction_sphereToPuncturedBall
    (a r : ℝ) (ha : 0 < a) (har : a < r) (z : ↥(sphere (0 : E) a)) :
    puncturedBallRetraction a r ha (sphereToPuncturedBall a r ha har z) = z := by
  apply Subtype.ext
  have hz : ‖(z : E)‖ = a := by
    simpa only [mem_sphere, dist_zero_right] using z.property
  simp only [puncturedBallRetraction_apply, sphereToPuncturedBall_apply,
    hz, div_self ha.ne', one_smul]

/-- Inclusion of the inner sphere followed by radial projection is the identity. -/
@[simp]
theorem puncturedBallRetraction_comp_sphereToPuncturedBall
    (a r : ℝ) (ha : 0 < a) (har : a < r) :
    (puncturedBallRetraction (E := E) a r ha).comp (sphereToPuncturedBall a r ha har) =
      ContinuousMap.id ↥(sphere (0 : E) a) := by
  apply ContinuousMap.ext
  intro z
  exact puncturedBallRetraction_sphereToPuncturedBall a r ha har z

/-- A punctured open ball strongly deforms onto a positive-radius inner sphere.

The homotopy runs from the identity to inclusion after radial projection and is
relative to the range of the sphere inclusion. -/
def puncturedBallDeformation (a r : ℝ) (ha : 0 < a) (har : a < r) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id ↥(ball (0 : E) r \ {0}))
      ((sphereToPuncturedBall a r ha har).comp (puncturedBallRetraction a r ha))
      (Set.range (sphereToPuncturedBall a r ha har)) := by
  let H := puncturedConvexDeformation (convex_ball (0 : E) r) a ha
    (radial_sphere_subset_ball a r har)
  exact
    { toHomotopy := H.toHomotopy
      prop' t z hz := by
        apply H.eq_fst t
        rw [sphereToPuncturedBall_range] at hz
        exact hz }

/-- The open-ball deformation interpolates the scalar projection factor. -/
@[simp]
theorem puncturedBallDeformation_apply (a r : ℝ) (ha : 0 < a) (har : a < r)
    (t : unitInterval) (z : ↥(ball (0 : E) r \ {0})) :
    (puncturedBallDeformation a r ha har (t, z) : E) =
      ((1 - (t : ℝ)) + (t : ℝ) * (a / ‖(z : E)‖)) • (z : E) := by
  rfl

/-- The norm along the deformation interpolates between the input norm and `a`. -/
theorem puncturedBallDeformation_norm (a r : ℝ) (ha : 0 < a) (har : a < r)
    (t : unitInterval) (z : ↥(ball (0 : E) r \ {0})) :
    ‖(puncturedBallDeformation a r ha har (t, z) : E)‖ =
      (1 - (t : ℝ)) * ‖(z : E)‖ + (t : ℝ) * a := by
  rw [puncturedBallDeformation_apply]
  exact radialHomotopy_norm a ha t (z : E) (punctured_norm_pos z)

/-- The open-ball deformation starts at the identity. -/
theorem puncturedBallDeformation_zero (a r : ℝ) (ha : 0 < a) (har : a < r)
    (z : ↥(ball (0 : E) r \ {0})) :
    puncturedBallDeformation a r ha har (0, z) = z := by
  exact (puncturedBallDeformation a r ha har).apply_zero z

/-- The open-ball deformation ends at inclusion after radial projection. -/
theorem puncturedBallDeformation_one (a r : ℝ) (ha : 0 < a) (har : a < r)
    (z : ↥(ball (0 : E) r \ {0})) :
    puncturedBallDeformation a r ha har (1, z) =
      sphereToPuncturedBall a r ha har (puncturedBallRetraction a r ha z) := by
  exact (puncturedBallDeformation a r ha har).apply_one z

/-- Every point in the range of the inner-sphere inclusion stays fixed. -/
theorem puncturedBallDeformation_fixed (a r : ℝ) (ha : 0 < a) (har : a < r)
    (t : unitInterval) (z : ↥(ball (0 : E) r \ {0}))
    (hz : z ∈ Set.range (sphereToPuncturedBall a r ha har)) :
    puncturedBallDeformation a r ha har (t, z) = z := by
  exact (puncturedBallDeformation a r ha har).eq_fst t hz

/-- Every included inner-sphere point stays fixed throughout the deformation. -/
@[simp]
theorem puncturedBallDeformation_sphere (a r : ℝ) (ha : 0 < a) (har : a < r)
    (t : unitInterval) (z : ↥(sphere (0 : E) a)) :
    puncturedBallDeformation a r ha har (t, sphereToPuncturedBall a r ha har z) =
      sphereToPuncturedBall a r ha har z := by
  exact (puncturedBallDeformation a r ha har).eq_fst t ⟨z, rfl⟩

/-- A punctured open ball is homotopy equivalent to any positive-radius inner sphere,
with radial projection as the forward map and sphere inclusion as the inverse. -/
def puncturedBallHomotopyEquivSphere (a r : ℝ) (ha : 0 < a) (har : a < r) :
    ContinuousMap.HomotopyEquiv
      ↥(ball (0 : E) r \ {0}) ↥(sphere (0 : E) a) := by
  exact
    { toFun := puncturedBallRetraction a r ha
      invFun := sphereToPuncturedBall a r ha har
      left_inv := ⟨(puncturedBallDeformation a r ha har).toHomotopy.symm⟩
      right_inv := by
        simpa only [puncturedBallRetraction_comp_sphereToPuncturedBall] using
          (ContinuousMap.Homotopic.refl (ContinuousMap.id ↥(sphere (0 : E) a))) }

/-- The open-ball homotopy equivalence maps points by radial projection. -/
@[simp]
theorem puncturedBallHomotopyEquivSphere_apply (a r : ℝ) (ha : 0 < a) (har : a < r)
    (z : ↥(ball (0 : E) r \ {0})) :
    puncturedBallHomotopyEquivSphere a r ha har z = puncturedBallRetraction a r ha z := by
  rfl

/-- The inverse open-ball homotopy equivalence is the inner-sphere inclusion. -/
@[simp]
theorem puncturedBallHomotopyEquivSphere_symm_apply (a r : ℝ) (ha : 0 < a) (har : a < r)
    (z : ↥(sphere (0 : E) a)) :
    (puncturedBallHomotopyEquivSphere a r ha har).symm z =
      sphereToPuncturedBall a r ha har z := by
  rfl

end Metric
