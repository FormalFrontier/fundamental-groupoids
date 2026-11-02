/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.PuncturedComponent
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Circles and radial paths in punctured disk attachments

The circle of radius `1 / 2` in an attached disk lies in the punctured part of the
ambient attachment component containing the common basepoint. The positive real
radius gives a path from that basepoint to the point of the circle over `1`.

The component is the intersection of an ambient attachment path component with
the punctured attachment; it is not defined as a path component of that subspace.
The retraction formulas below are pointwise formulas in the original space.
-/

@[expose] public section

universe u v

namespace TopCat

variable {X : Type u} [TopologicalSpace X] {J : Type v}

private theorem continuous_circle_coe : Continuous (fun z : Circle => (z : ℂ)) := by
  simpa only [diskBoundary_coe] using
    (show Continuous (fun z : Circle => (diskBoundary z : ℂ)) from
      continuous_subtype_val.comp diskBoundary.continuous)

private theorem radial_mem_puncturedDisk (r : ℝ) (hr : 0 < r) (hr' : r ≤ 1)
    (z : Circle) : r • (z : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 \ {0} := by
  have hn : ‖r • (z : ℂ)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe, mul_one]
  constructor
  · simpa only [Metric.mem_closedBall, dist_zero_right, hn] using hr'
  · simp only [Set.mem_singleton_iff]
    intro hz
    have hzero : r = 0 := hn.symm.trans (by rw [hz, norm_zero])
    exact hr.ne' hzero

private theorem radial_direction (r : ℝ) (hr : 0 < r) (z : Circle) :
    (z : ℂ) = (1 / ‖r • (z : ℂ)‖) • (r • (z : ℂ)) := by
  have hn : ‖r • (z : ℂ)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, Circle.norm_coe, mul_one]
  rw [hn, smul_smul, div_mul_cancel₀ _ hr.ne', one_smul]

/-- The circle of radius one half in the punctured closed unit disk. -/
noncomputable def puncturedDiskHalfCircle :
    C(Circle, ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) := by
  exact ⟨fun z => ⟨(1 / 2 : ℝ) • (z : ℂ),
      by exact radial_mem_puncturedDisk (1 / 2) (by norm_num) (by norm_num) z⟩,
    by
      exact
        ((continuous_const : Continuous (fun _ : Circle => (1 / 2 : ℝ))).smul
          continuous_circle_coe).subtype_mk
          (fun z => by
            exact radial_mem_puncturedDisk (1 / 2) (by norm_num) (by norm_num) z)⟩

/-- The half-radius circle has the specified complex coordinate. -/
@[simp]
theorem puncturedDiskHalfCircle_coe (z : Circle) :
    (puncturedDiskHalfCircle z : ℂ) = (1 / 2 : ℝ) • (z : ℂ) := by
  rfl

/-- Normalizing a point on the half-radius circle recovers its circle coordinate. -/
theorem puncturedDiskHalfCircle_direction (z : Circle) :
    (z : ℂ) = (1 / ‖(puncturedDiskHalfCircle z : ℂ)‖) •
      (puncturedDiskHalfCircle z : ℂ) := by
  rw [puncturedDiskHalfCircle_coe]
  exact radial_direction (1 / 2) (by norm_num) z

/-- Retraction of the characteristic half-radius circle evaluates the attaching map. -/
@[simp]
theorem diskAttachmentPuncturedRetraction_halfCircle
    (f : J → C(Circle, X)) (j : J) (z : Circle) :
    diskAttachmentPuncturedRetraction f
        (diskAttachmentPuncturedDisk f j (puncturedDiskHalfCircle z)) = f j z := by
  exact diskAttachmentPuncturedRetraction_disk f j _ z
    (puncturedDiskHalfCircle_direction z)

private theorem radialCoefficient_pos (t : unitInterval) : 0 < 1 - (t : ℝ) / 2 := by
  have ht := t.property.2
  linarith

private theorem radialCoefficient_le_one (t : unitInterval) :
    1 - (t : ℝ) / 2 ≤ 1 := by
  have ht := t.property.1
  linarith

/-- The inward radial segment from the unit boundary to the half-radius circle. -/
noncomputable def puncturedDiskRadialPath (z : Circle) :
    Path (puncturedDiskBoundary z) (puncturedDiskHalfCircle z) := by
  exact
    { toFun := fun t => ⟨(1 - (t : ℝ) / 2) • (z : ℂ),
        by
          exact radial_mem_puncturedDisk _ (radialCoefficient_pos t)
            (radialCoefficient_le_one t) z⟩
      continuous_toFun := by
        have hc : Continuous (fun t : unitInterval => (1 - (t : ℝ) / 2 : ℝ)) :=
          continuous_const.sub (continuous_subtype_val.div_const 2)
        exact (hc.smul
          (continuous_const : Continuous (fun _ : unitInterval => (z : ℂ)))).subtype_mk
          (fun t => by
            exact radial_mem_puncturedDisk _ (radialCoefficient_pos t)
              (radialCoefficient_le_one t) z)
      source' := by
        apply Subtype.ext
        simp only [Set.Icc.coe_zero, zero_div, sub_zero, one_smul,
          puncturedDiskBoundary_coe]
      target' := by
        apply Subtype.ext
        simp only [Set.Icc.coe_one, puncturedDiskHalfCircle_coe]
        norm_num }

/-- The radial path has affine radial coordinate, with no angular change. -/
@[simp]
theorem puncturedDiskRadialPath_coe (z : Circle) (t : unitInterval) :
    (puncturedDiskRadialPath z t : ℂ) = (1 - (t : ℝ) / 2) • (z : ℂ) := by
  rfl

/-- Every point of the radial segment has the original unit direction. -/
theorem puncturedDiskRadialPath_direction (z : Circle) (t : unitInterval) :
    (z : ℂ) = (1 / ‖(puncturedDiskRadialPath z t : ℂ)‖) •
      (puncturedDiskRadialPath z t : ℂ) := by
  rw [puncturedDiskRadialPath_coe]
  exact radial_direction _ (radialCoefficient_pos t) z

/-- Retraction of a characteristic radial segment keeps its original circle direction. -/
@[simp]
theorem diskAttachmentPuncturedRetraction_radialPath
    (f : J → C(Circle, X)) (j : J) (z : Circle) (t : unitInterval) :
    diskAttachmentPuncturedRetraction f
        (diskAttachmentPuncturedDisk f j (puncturedDiskRadialPath z t)) = f j z := by
  exact diskAttachmentPuncturedRetraction_disk f j _ z
    (puncturedDiskRadialPath_direction z t)

private noncomputable def puncturedRadialImage (f : J → C(Circle, X)) (j : J) (z : Circle) :
    Path (diskAttachmentPuncturedInclusion f (f j z))
      (diskAttachmentPuncturedDisk f j (puncturedDiskHalfCircle z)) := by
  exact ((puncturedDiskRadialPath z).map (diskAttachmentPuncturedDisk f j).continuous).cast
    (diskAttachmentPuncturedDisk_boundary f j z).symm rfl

private theorem halfCircle_mem_component (f : J → C(Circle, X)) (x : X)
    (j : J) (hj : f j 1 = x) (z : Circle) :
    diskAttachmentPuncturedDisk f j (puncturedDiskHalfCircle z) ∈
      diskAttachmentPuncturedComponentSet f x := by
  rw [mem_diskAttachmentPuncturedComponentSet]
  have hz : Joined x (f j z) := by
    simpa only [hj] using
      ((PathConnectedSpace.joined (1 : Circle) z).map (f j).continuous)
  exact (hz.map (diskAttachmentInclusion f).continuous).trans
    ⟨(puncturedRadialImage f j z).map continuous_subtype_val⟩

/-- The half-radius circle in an attached disk, as a map into the punctured
part of the ambient attachment component of the common basepoint. -/
noncomputable def diskAttachmentPuncturedComponentHalfCircle (f : J → C(Circle, X)) (x : X)
    (j : J) (hj : f j 1 = x) :
    C(Circle, diskAttachmentPuncturedComponent f x) := by
  exact ⟨fun z => ⟨diskAttachmentPuncturedDisk f j (puncturedDiskHalfCircle z),
      by exact halfCircle_mem_component f x j hj z⟩,
    by
      exact
        ((diskAttachmentPuncturedDisk f j).continuous.comp
          puncturedDiskHalfCircle.continuous).subtype_mk
          (fun z => by exact halfCircle_mem_component f x j hj z)⟩

/-- The component circle is the characteristic disk map at radius one half. -/
@[simp]
theorem diskAttachmentPuncturedComponentHalfCircle_coe
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) (z : Circle) :
    (diskAttachmentPuncturedComponentHalfCircle f x j hj z : diskAttachmentPunctured f) =
      diskAttachmentPuncturedDisk f j (puncturedDiskHalfCircle z) := by
  rfl

private noncomputable def basedPuncturedRadial (f : J → C(Circle, X)) (x : X)
    (j : J) (hj : f j 1 = x) :
    Path (diskAttachmentPuncturedInclusion f x)
      (diskAttachmentPuncturedDisk f j (puncturedDiskHalfCircle 1)) := by
  exact (puncturedRadialImage f j 1).cast (by rw [hj]) rfl

private theorem basedPuncturedRadial_range (f : J → C(Circle, X)) (x : X)
    (j : J) (hj : f j 1 = x) :
    Set.range (basedPuncturedRadial f x j hj) ⊆
      diskAttachmentPuncturedComponentSet f x := by
  rintro w ⟨t, rfl⟩
  rw [mem_diskAttachmentPuncturedComponentSet]
  let p := (basedPuncturedRadial f x j hj).map continuous_subtype_val
  exact ⟨(p.truncateOfLE t.property.1).cast
    p.extend_zero.symm (p.extend_extends' t).symm⟩

/-- The positive real radial path from the common basepoint to the point over `1`
on the half-radius circle in the selected disk. -/
noncomputable def diskAttachmentPuncturedComponentRadialPath (f : J → C(Circle, X)) (x : X)
    (j : J) (hj : f j 1 = x) :
    Path (diskAttachmentPuncturedComponentBasepoint f x)
      (diskAttachmentPuncturedComponentHalfCircle f x j hj 1) := by
  let p : Path (diskAttachmentPuncturedInclusion f x)
      (diskAttachmentPuncturedDisk f j (puncturedDiskHalfCircle 1)) :=
    (((puncturedDiskRadialPath 1).map (diskAttachmentPuncturedDisk f j).continuous).cast
      (diskAttachmentPuncturedDisk_boundary f j 1).symm rfl).cast (by rw [hj]) rfl
  exact (p.codRestrict (by exact basedPuncturedRadial_range f x j hj)).cast
    (by apply Subtype.ext; rfl) (by apply Subtype.ext; rfl)

/-- Forgetting the component gives the characteristic image of the positive radius. -/
@[simp]
theorem diskAttachmentPuncturedComponentRadialPath_coe
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (t : unitInterval) :
    (diskAttachmentPuncturedComponentRadialPath f x j hj t : diskAttachmentPunctured f) =
      diskAttachmentPuncturedDisk f j (puncturedDiskRadialPath 1 t) := by
  rfl

/-- Retraction of the half-radius circle evaluates the attaching map pointwise. -/
theorem diskAttachmentPuncturedComponentRetraction_halfCircle
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) (z : Circle) :
    (diskAttachmentPuncturedComponentRetraction f x
        (diskAttachmentPuncturedComponentHalfCircle f x j hj z) : X) = f j z := by
  rw [diskAttachmentPuncturedComponentRetraction_coe,
    diskAttachmentPuncturedComponentHalfCircle_coe]
  exact diskAttachmentPuncturedRetraction_halfCircle f j z

/-- Forgetting the original-space component after retraction of the half-radius
circle gives exactly the attaching map. -/
theorem diskAttachmentPuncturedComponentRetraction_comp_halfCircle
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    ((ContinuousMap.subtypeVal (pathComponent x)).comp
        (diskAttachmentPuncturedComponentRetraction f x)).comp
        (diskAttachmentPuncturedComponentHalfCircle f x j hj) = f j := by
  ext z
  exact diskAttachmentPuncturedComponentRetraction_halfCircle f x j hj z

/-- Retraction of the radial path is pointwise the constant basepoint. -/
theorem diskAttachmentPuncturedComponentRetraction_radialPath
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (t : unitInterval) :
    (diskAttachmentPuncturedComponentRetraction f x
        (diskAttachmentPuncturedComponentRadialPath f x j hj t) : X) = x := by
  rw [diskAttachmentPuncturedComponentRetraction_coe,
    diskAttachmentPuncturedComponentRadialPath_coe]
  exact (diskAttachmentPuncturedRetraction_radialPath f j 1 t).trans hj

/-- In the original-space component itself, every point of the radial path retracts
to its distinguished point. -/
theorem diskAttachmentPuncturedComponentRetraction_radialPath_eq
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (t : unitInterval) :
    diskAttachmentPuncturedComponentRetraction f x
        (diskAttachmentPuncturedComponentRadialPath f x j hj t) =
      (⟨x, Joined.refl x⟩ : ↥(pathComponent x)) := by
  apply Subtype.ext
  exact diskAttachmentPuncturedComponentRetraction_radialPath f x j hj t

end TopCat
