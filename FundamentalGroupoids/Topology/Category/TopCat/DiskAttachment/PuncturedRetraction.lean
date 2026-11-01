/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.Punctured
public import FundamentalGroupoids.Topology.Homotopy.Radial
import FundamentalGroupoids.Topology.Homotopy.ComplexPuncturedBall

/-!
# Radial deformation of punctured disk attachments

Removing the characteristic disk centres leaves a strong deformation retraction
onto the original-space image. On each punctured disk the retraction follows its
unit direction and the homotopy moves radially outwards, fixing its boundary.
The scalar expression `(1 / ‖z‖) • z` denotes the normalized complex direction.

The maps descend from the original-space and punctured-disk maps. Currying into
continuous paths permits the homotopy to descend by the same universal property;
uncurrying requires local compactness only of the parameter interval.
-/

open Topology

universe u v

noncomputable section

namespace TopCat

variable {X : Type u} [TopologicalSpace X] {J : Type v}

private def puncturedDiskDirection :
    C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}), Circle) := by
  exact ((Complex.circleHomeomorphSphere 1 zero_lt_one).symm :
    C(↥(Metric.sphere (0 : ℂ) 1), Circle)).comp
      (Metric.puncturedClosedBallRetraction (E := ℂ) 1 zero_lt_one)

private theorem puncturedDiskDirection_coe_radial
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    (puncturedDiskDirection z : ℂ) =
      (Metric.puncturedClosedBallRetraction (E := ℂ) 1 zero_lt_one z : ℂ) := by
  calc
    (puncturedDiskDirection z : ℂ) =
        ((Complex.circleHomeomorphSphere 1 zero_lt_one).symm
          (Metric.puncturedClosedBallRetraction (E := ℂ) 1 zero_lt_one z) : ℂ) := by
      rfl
    _ = (Metric.puncturedClosedBallRetraction (E := ℂ) 1 zero_lt_one z : ℂ) := by
      simpa only [inv_one, one_smul] using
        Complex.circleHomeomorphSphere_symm_apply 1 zero_lt_one
          (Metric.puncturedClosedBallRetraction (E := ℂ) 1 zero_lt_one z)

private theorem puncturedDiskDirection_coe
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    (puncturedDiskDirection z : ℂ) = (1 / ‖(z : ℂ)‖) • (z : ℂ) := by
  exact (puncturedDiskDirection_coe_radial z).trans
    (Metric.puncturedClosedBallRetraction_apply (E := ℂ) 1 zero_lt_one z)

private theorem puncturedDiskDirection_boundary (b : Circle) :
    puncturedDiskDirection (puncturedDiskBoundary b) = b := by
  apply Circle.coe_injective
  calc
    (puncturedDiskDirection (puncturedDiskBoundary b) : ℂ) =
        (1 / ‖(puncturedDiskBoundary b : ℂ)‖) • (puncturedDiskBoundary b : ℂ) :=
      puncturedDiskDirection_coe (puncturedDiskBoundary b)
    _ = (b : ℂ) := by
      simp only [puncturedDiskBoundary_coe, Circle.norm_coe, div_one, one_smul]

private theorem direction_attaching_condition (f : J → C(Circle, X)) (j : J) (b : Circle) :
    ((f j).comp puncturedDiskDirection) (puncturedDiskBoundary b) =
      (ContinuousMap.id X) (f j b) := by
  change f j (puncturedDiskDirection (puncturedDiskBoundary b)) = f j b
  rw [puncturedDiskDirection_boundary]

public section

/-- The retraction of the punctured attachment onto its original space.
Each punctured disk is sent through its attaching map in the normalized direction. -/
def diskAttachmentPuncturedRetraction (f : J → C(Circle, X)) :
    C(diskAttachmentPunctured f, X) := by
  exact diskAttachmentPuncturedDesc f (ContinuousMap.id X)
    (fun j => (f j).comp puncturedDiskDirection) (direction_attaching_condition f)

/-- The punctured retraction is identity on the original-space map. -/
@[simp]
theorem diskAttachmentPuncturedRetraction_inclusion (f : J → C(Circle, X)) (x : X) :
    diskAttachmentPuncturedRetraction f (diskAttachmentPuncturedInclusion f x) = x := by
  exact diskAttachmentPuncturedDesc_inclusion f (ContinuousMap.id X)
    (fun j => (f j).comp puncturedDiskDirection) (direction_attaching_condition f) x

/-- The punctured retraction is a left inverse to the original-space map. -/
@[simp]
theorem diskAttachmentPuncturedRetraction_comp_inclusion (f : J → C(Circle, X)) :
    (diskAttachmentPuncturedRetraction f).comp (diskAttachmentPuncturedInclusion f) =
      ContinuousMap.id X := by
  ext x
  exact diskAttachmentPuncturedRetraction_inclusion f x

/-- On a punctured disk the retraction evaluates the attaching map at its unit direction. -/
theorem diskAttachmentPuncturedRetraction_disk (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) (b : Circle)
    (hb : (b : ℂ) = (1 / ‖(z : ℂ)‖) • (z : ℂ)) :
    diskAttachmentPuncturedRetraction f (diskAttachmentPuncturedDisk f j z) = f j b := by
  have hd : puncturedDiskDirection z = b :=
    Circle.coe_injective ((puncturedDiskDirection_coe z).trans hb.symm)
  change diskAttachmentPuncturedDesc f (ContinuousMap.id X)
    (fun j => (f j).comp puncturedDiskDirection) (direction_attaching_condition f)
    (diskAttachmentPuncturedDisk f j z) = f j b
  rw [diskAttachmentPuncturedDesc_disk]
  change f j (puncturedDiskDirection z) = f j b
  rw [hd]

/-- Every punctured-disk point has a unit direction computing its retraction. -/
theorem diskAttachmentPuncturedRetraction_disk_exists (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    ∃ b : Circle, (b : ℂ) = (1 / ‖(z : ℂ)‖) • (z : ℂ) ∧
      diskAttachmentPuncturedRetraction f (diskAttachmentPuncturedDisk f j z) = f j b := by
  exact ⟨puncturedDiskDirection z, puncturedDiskDirection_coe z,
    diskAttachmentPuncturedRetraction_disk f j z _ (puncturedDiskDirection_coe z)⟩

end

private theorem puncturedRetraction_disk_direction (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    diskAttachmentPuncturedRetraction f (diskAttachmentPuncturedDisk f j z) =
      f j (puncturedDiskDirection z) := by
  exact diskAttachmentPuncturedRetraction_disk f j z _ (puncturedDiskDirection_coe z)

private def originalPaths (f : J → C(Circle, X)) :
    C(X, C(unitInterval, diskAttachmentPunctured f)) := by
  exact (⟨fun p : X × unitInterval => diskAttachmentPuncturedInclusion f p.1,
    (diskAttachmentPuncturedInclusion f).continuous.comp continuous_fst⟩ :
      C(X × unitInterval, diskAttachmentPunctured f)).curry

private theorem originalPaths_apply (f : J → C(Circle, X)) (x : X) (t : unitInterval) :
    originalPaths f x t = diskAttachmentPuncturedInclusion f x := by
  exact ContinuousMap.curry_apply _ x t

private def radialPaths (f : J → C(Circle, X)) (j : J) :
    C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}), C(unitInterval, diskAttachmentPunctured f)) := by
  let F := Metric.puncturedClosedBallDeformation (E := ℂ) 1 zero_lt_one
  exact (⟨fun p => diskAttachmentPuncturedDisk f j (F (p.2, p.1)),
    (diskAttachmentPuncturedDisk f j).continuous.comp
      (F.toHomotopy.toContinuousMap.continuous.comp
        (continuous_snd.prodMk continuous_fst))⟩ :
      C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}) × unitInterval,
        diskAttachmentPunctured f)).curry

private theorem radialPaths_apply (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) (t : unitInterval) :
    radialPaths f j z t = diskAttachmentPuncturedDisk f j
      (Metric.puncturedClosedBallDeformation (E := ℂ) 1 zero_lt_one (t, z)) := by
  exact ContinuousMap.curry_apply _ z t

private theorem radialDeformation_boundary (b : Circle) (t : unitInterval) :
    Metric.puncturedClosedBallDeformation (E := ℂ) 1 zero_lt_one
      (t, puncturedDiskBoundary b) = puncturedDiskBoundary b := by
  apply (Metric.puncturedClosedBallDeformation (E := ℂ) 1 zero_lt_one).prop' t
  change (puncturedDiskBoundary b : ℂ) ∈ Metric.sphere (0 : ℂ) 1
  rw [puncturedDiskBoundary_coe]
  simpa only [Metric.mem_sphere, dist_zero_right] using Circle.norm_coe b

private theorem radialDeformation_one
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    Metric.puncturedClosedBallDeformation (E := ℂ) 1 zero_lt_one (1, z) =
      puncturedDiskBoundary (puncturedDiskDirection z) := by
  rw [Metric.puncturedClosedBallDeformation_one]
  apply Subtype.ext
  rw [Metric.sphereToPuncturedClosedBall_apply, puncturedDiskBoundary_coe]
  exact (puncturedDiskDirection_coe_radial z).symm

private theorem radialPaths_boundary (f : J → C(Circle, X)) (j : J) (b : Circle) :
    radialPaths f j (puncturedDiskBoundary b) = originalPaths f (f j b) := by
  ext t
  rw [radialPaths_apply, originalPaths_apply, radialDeformation_boundary,
    diskAttachmentPuncturedDisk_boundary]

private def puncturedPaths (f : J → C(Circle, X)) :
    C(diskAttachmentPunctured f, C(unitInterval, diskAttachmentPunctured f)) := by
  exact diskAttachmentPuncturedDesc f (originalPaths f) (radialPaths f)
    (radialPaths_boundary f)

private theorem puncturedPaths_inclusion (f : J → C(Circle, X)) (x : X) (t : unitInterval) :
    puncturedPaths f (diskAttachmentPuncturedInclusion f x) t =
      diskAttachmentPuncturedInclusion f x := by
  change diskAttachmentPuncturedDesc f (originalPaths f) (radialPaths f)
    (radialPaths_boundary f)
    (diskAttachmentPuncturedInclusion f x) t = diskAttachmentPuncturedInclusion f x
  rw [diskAttachmentPuncturedDesc_inclusion]
  exact originalPaths_apply f x t

private theorem puncturedPaths_disk (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) (t : unitInterval) :
    puncturedPaths f (diskAttachmentPuncturedDisk f j z) t =
      diskAttachmentPuncturedDisk f j
        (Metric.puncturedClosedBallDeformation (E := ℂ) 1 zero_lt_one (t, z)) := by
  change diskAttachmentPuncturedDesc f (originalPaths f) (radialPaths f)
    (radialPaths_boundary f)
    (diskAttachmentPuncturedDisk f j z) t = _
  rw [diskAttachmentPuncturedDesc_disk]
  exact radialPaths_apply f j z t

public section

/-- The outward radial deformation of the punctured attachment onto its original-space
image, fixing that image throughout. -/
def diskAttachmentPuncturedDeformation (f : J → C(Circle, X)) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (diskAttachmentPunctured f))
      ((diskAttachmentPuncturedInclusion f).comp (diskAttachmentPuncturedRetraction f))
      (Set.range (diskAttachmentPuncturedInclusion f)) := by
  refine
    { toFun := fun p => puncturedPaths f p.2 p.1
      continuous_toFun := (puncturedPaths f).uncurry.continuous.comp
        (continuous_snd.prodMk continuous_fst)
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro p
    change puncturedPaths f p 0 = p
    refine diskAttachmentPunctured_induction f
      (P := fun q => puncturedPaths f q 0 = q) ?_ ?_ p
    · intro x
      exact puncturedPaths_inclusion f x 0
    · intro j z
      rw [puncturedPaths_disk, Metric.puncturedClosedBallDeformation_zero]
  · intro p
    change puncturedPaths f p 1 =
      diskAttachmentPuncturedInclusion f (diskAttachmentPuncturedRetraction f p)
    refine diskAttachmentPunctured_induction f
      (P := fun q => puncturedPaths f q 1 =
        diskAttachmentPuncturedInclusion f (diskAttachmentPuncturedRetraction f q)) ?_ ?_ p
    · intro x
      rw [puncturedPaths_inclusion, diskAttachmentPuncturedRetraction_inclusion]
    · intro j z
      rw [puncturedPaths_disk, radialDeformation_one, diskAttachmentPuncturedDisk_boundary,
        puncturedRetraction_disk_direction]
  · intro t p hp
    rcases hp with ⟨x, rfl⟩
    exact puncturedPaths_inclusion f x t

private theorem puncturedDeformation_apply (f : J → C(Circle, X))
    (t : unitInterval) (p : diskAttachmentPunctured f) :
    diskAttachmentPuncturedDeformation f (t, p) = puncturedPaths f p t := by
  rfl

/-- The radial deformation fixes the original-space map at every time. -/
@[simp]
theorem diskAttachmentPuncturedDeformation_inclusion (f : J → C(Circle, X))
    (t : unitInterval) (x : X) :
    diskAttachmentPuncturedDeformation f (t, diskAttachmentPuncturedInclusion f x) =
      diskAttachmentPuncturedInclusion f x := by
  rw [puncturedDeformation_apply, puncturedPaths_inclusion]

/-- On each punctured disk the deformation is the punctured closed-ball radial deformation. -/
theorem diskAttachmentPuncturedDeformation_disk (f : J → C(Circle, X)) (j : J)
    (t : unitInterval) (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    diskAttachmentPuncturedDeformation f (t, diskAttachmentPuncturedDisk f j z) =
      diskAttachmentPuncturedDisk f j
        (Metric.puncturedClosedBallDeformation (E := ℂ) 1 zero_lt_one (t, z)) := by
  rw [puncturedDeformation_apply, puncturedPaths_disk]

/-- The disk formula can be read directly in complex coordinates, with the radial
coefficient `1 - t + t / ‖z‖`. -/
theorem diskAttachmentPuncturedDeformation_disk_of_coe (f : J → C(Circle, X)) (j : J)
    (t : unitInterval) (z w : ↥(Metric.closedBall (0 : ℂ) 1 \ {0}))
    (hw : (w : ℂ) = ((1 - (t : ℝ)) + (t : ℝ) / ‖(z : ℂ)‖) • (z : ℂ)) :
    diskAttachmentPuncturedDeformation f (t, diskAttachmentPuncturedDisk f j z) =
      diskAttachmentPuncturedDisk f j w := by
  rw [diskAttachmentPuncturedDeformation_disk]
  apply congrArg (diskAttachmentPuncturedDisk f j)
  apply Subtype.ext
  rw [Metric.puncturedClosedBallDeformation_apply]
  simpa only [div_eq_mul_inv, one_mul] using hw.symm

/-- Each radial path has the stated complex coordinate in the punctured closed disk. -/
theorem diskAttachmentPuncturedDeformation_disk_exists (f : J → C(Circle, X)) (j : J)
    (t : unitInterval) (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    ∃ w : ↥(Metric.closedBall (0 : ℂ) 1 \ {0}),
      (w : ℂ) = ((1 - (t : ℝ)) + (t : ℝ) / ‖(z : ℂ)‖) • (z : ℂ) ∧
        diskAttachmentPuncturedDeformation f (t, diskAttachmentPuncturedDisk f j z) =
          diskAttachmentPuncturedDisk f j w := by
  refine ⟨Metric.puncturedClosedBallDeformation (E := ℂ) 1 zero_lt_one (t, z), ?_,
    diskAttachmentPuncturedDeformation_disk f j t z⟩
  simpa only [div_eq_mul_inv, one_mul] using
    Metric.puncturedClosedBallDeformation_apply (E := ℂ) 1 zero_lt_one t z

/-- The radial deformation starts at the identity. -/
theorem diskAttachmentPuncturedDeformation_zero (f : J → C(Circle, X))
    (p : diskAttachmentPunctured f) : diskAttachmentPuncturedDeformation f (0, p) = p := by
  exact (diskAttachmentPuncturedDeformation f).toHomotopy.map_zero_left p

/-- The radial deformation ends at the original inclusion after retraction. -/
theorem diskAttachmentPuncturedDeformation_one (f : J → C(Circle, X))
    (p : diskAttachmentPunctured f) :
    diskAttachmentPuncturedDeformation f (1, p) =
      diskAttachmentPuncturedInclusion f (diskAttachmentPuncturedRetraction f p) := by
  exact (diskAttachmentPuncturedDeformation f).toHomotopy.map_one_left p

end

end TopCat
