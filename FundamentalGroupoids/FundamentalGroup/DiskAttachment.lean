/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle
public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment
public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.PuncturedCircle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Fundamental groups of disk attachments

Every attaching boundary circle induces the trivial fundamental-group homomorphism
into a disk attachment, at every basepoint. The attaching square factors this map
through the characteristic closed disk. That disk is convex and contractible, so
its fundamental groups are subsingleton.

When an attaching map sends `1` to a chosen point, the same conclusion holds for
the composite of its based homomorphism and the inclusion homomorphism.

The positive half-radius circle in the punctured ambient component is based by
its positive radial path. The class of this whiskered loop retracts to exactly
the positive attaching loop class in the original space.

## Limitations

These results annihilate the attaching relations; they do not characterize the
kernel or assert surjectivity of the inclusion homomorphism.
-/

@[expose] public section

universe u v

namespace TopCat

variable {X : Type u} [TopologicalSpace X] {J : Type v}

/-- The positively oriented circle loop, based at the common basepoint by the
positive real radial path. Concatenation is in the order of traversal. -/
noncomputable def diskAttachmentPuncturedComponentLoop (f : J → C(Circle, X)) (x : X)
    (j : J) (hj : f j 1 = x) :
    Path (diskAttachmentPuncturedComponentBasepoint f x)
      (diskAttachmentPuncturedComponentBasepoint f x) := by
  exact ((diskAttachmentPuncturedComponentRadialPath f x j hj).trans
    ((Circle.loop 1).map (diskAttachmentPuncturedComponentHalfCircle f x j hj).continuous)).trans
      (diskAttachmentPuncturedComponentRadialPath f x j hj).symm

/-- The based loop traverses the radius, the positive circle, and the reverse radius. -/
theorem diskAttachmentPuncturedComponentLoop_eq
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    diskAttachmentPuncturedComponentLoop f x j hj =
      ((diskAttachmentPuncturedComponentRadialPath f x j hj).trans
        ((Circle.loop 1).map
          (diskAttachmentPuncturedComponentHalfCircle f x j hj).continuous)).trans
        (diskAttachmentPuncturedComponentRadialPath f x j hj).symm := by
  rfl

end TopCat

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X] {J : Type v}

/-- Every element of the fundamental group of an attaching boundary circle maps
to the identity in the disk attachment, at any point of that circle. -/
theorem map_diskAttachment_boundary_eq_one (f : J → C(Circle, X)) (j : J)
    (z : Circle) (a : FundamentalGroup Circle z) :
    map ((TopCat.diskAttachmentInclusion f).comp (f j)) z a = 1 := by
  let : ContractibleSpace ↥(Metric.closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) (1 : ℝ)).contractibleSpace ⟨0, by simp⟩
  -- The target group varies with the boundary map, so transport the entire assertion.
  apply Eq.mp (congrArg
    (fun g : C(Circle, TopCat.diskAttachment f) => map g z a = 1)
    (TopCat.diskAttachment_boundary f j))
  rw [map_comp, MonoidHom.comp_apply]
  have ha : map TopCat.diskBoundary z a = 1 := Subsingleton.elim _ _
  rw [ha, map_one]

/-- If an attaching map sends `1` to a chosen point, its based fundamental-group
homomorphism becomes trivial after the inclusion into the disk attachment. -/
theorem map_diskAttachmentInclusion_mapOfEq_eq_one (f : J → C(Circle, X))
    (x : X) (j : J) (h : f j 1 = x) (a : FundamentalGroup Circle 1) :
    map (TopCat.diskAttachmentInclusion f) x (mapOfEq (f j) h a) = 1 := by
  subst x
  simpa only [mapOfEq_rfl, map_comp, MonoidHom.comp_apply] using
    map_diskAttachment_boundary_eq_one f j (1 : Circle) a

/-- The fundamental-group class of the positive half-radius circle in a selected
attached disk, based by its positive real radial path. -/
noncomputable def diskAttachmentPuncturedComponentGenerator (f : J → C(Circle, X)) (x : X)
    (j : J) (hj : f j 1 = x) :
    FundamentalGroup (TopCat.diskAttachmentPuncturedComponent f x)
      (TopCat.diskAttachmentPuncturedComponentBasepoint f x) := by
  exact fromPath ⟦TopCat.diskAttachmentPuncturedComponentLoop f x j hj⟧

/-- The disk generator is represented by the radial-whiskered positive circle loop. -/
theorem diskAttachmentPuncturedComponentGenerator_eq
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    diskAttachmentPuncturedComponentGenerator f x j hj =
      fromPath ⟦TopCat.diskAttachmentPuncturedComponentLoop f x j hj⟧ := by
  rfl

/-- Change of basepoint back along the radial path sends the positive half-circle
loop class to the disk generator. -/
theorem diskAttachmentPuncturedComponentHalfCircle_transport
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    fundamentalGroupMulEquivOfPath
        (TopCat.diskAttachmentPuncturedComponentRadialPath f x j hj).symm
        (map (TopCat.diskAttachmentPuncturedComponentHalfCircle f x j hj) 1
          (fromPath ⟦Circle.loop 1⟧)) =
      diskAttachmentPuncturedComponentGenerator f x j hj := by
  rw [map_fromPath, fundamentalGroupMulEquivOfPath_fromPath, Path.symm_symm,
    diskAttachmentPuncturedComponentGenerator_eq,
    TopCat.diskAttachmentPuncturedComponentLoop_eq]

/-- Retraction, followed by inclusion of the original-space component into the
original space, sends the half-radius disk generator to the positive attaching
loop class. The radial whiskers become constant, so no inverse or conjugate of
the attaching class occurs. -/
theorem mapOfEq_diskAttachmentPuncturedComponentGenerator
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    mapOfEq
        ((ContinuousMap.subtypeVal (pathComponent x)).comp
          (TopCat.diskAttachmentPuncturedComponentRetraction f x))
        (by
          simpa only [ContinuousMap.comp_apply, ContinuousMap.subtypeVal_apply] using
            (TopCat.diskAttachmentPuncturedComponentRetraction_basepoint_coe f x))
        (diskAttachmentPuncturedComponentGenerator f x j hj) =
      mapOfEq (f j) hj (fromPath ⟦Circle.loop 1⟧) := by
  let R : C(TopCat.diskAttachmentPuncturedComponent f x, X) :=
    (ContinuousMap.subtypeVal (pathComponent x)).comp
      (TopCat.diskAttachmentPuncturedComponentRetraction f x)
  let β := TopCat.diskAttachmentPuncturedComponentRadialPath f x j hj
  let γ := TopCat.diskAttachmentPuncturedComponentHalfCircle f x j hj
  have h0 : R (TopCat.diskAttachmentPuncturedComponentBasepoint f x) = x := by
    simpa only [R, ContinuousMap.comp_apply, ContinuousMap.subtypeVal_apply] using
      (TopCat.diskAttachmentPuncturedComponentRetraction_basepoint_coe f x)
  have h1 : R (γ 1) = x :=
    (TopCat.diskAttachmentPuncturedComponentRetraction_halfCircle f x j hj 1).trans hj
  have hβ : (β.map R.continuous).cast h0.symm h1.symm = Path.refl x := by
    ext t
    exact TopCat.diskAttachmentPuncturedComponentRetraction_radialPath f x j hj t
  have hγ : (((Circle.loop 1).map γ.continuous).map R.continuous).cast h1.symm h1.symm =
      ((Circle.loop 1).map (f j).continuous).cast hj.symm hj.symm := by
    ext t
    exact TopCat.diskAttachmentPuncturedComponentRetraction_halfCircle f x j hj
      (Circle.loop 1 t)
  have himage :
      (((TopCat.diskAttachmentPuncturedComponentLoop f x j hj).map R.continuous).cast
        h0.symm h0.symm).Homotopic
        (((Circle.loop 1).map (f j).continuous).cast hj.symm hj.symm) := by
    rw [TopCat.diskAttachmentPuncturedComponentLoop_eq,
      Path.map_trans, Path.map_trans, ← Path.map_symm]
    rw [Path.cast_trans _ _ h0.symm h1.symm h0.symm,
      Path.cast_trans _ _ h0.symm h1.symm h1.symm,
      Path.cast_symm, hβ, hγ, Path.refl_symm]
    exact (Path.Homotopic.trans_refl _).trans (Path.Homotopic.refl_trans _)
  calc
    mapOfEq R h0 (diskAttachmentPuncturedComponentGenerator f x j hj) =
        mapOfEq R h0
          (fromPath ⟦TopCat.diskAttachmentPuncturedComponentLoop f x j hj⟧) :=
      congrArg (mapOfEq R h0) (diskAttachmentPuncturedComponentGenerator_eq f x j hj)
    _ = fromPath
        ⟦((TopCat.diskAttachmentPuncturedComponentLoop f x j hj).map R.continuous).cast
          h0.symm h0.symm⟧ :=
      mapOfEq_fromPath R h0 (TopCat.diskAttachmentPuncturedComponentLoop f x j hj)
    _ = fromPath ⟦((Circle.loop 1).map (f j).continuous).cast hj.symm hj.symm⟧ :=
      congrArg fromPath (Quotient.sound himage)
    _ = mapOfEq (f j) hj (fromPath ⟦Circle.loop 1⟧) :=
      (mapOfEq_fromPath (f j) hj (Circle.loop 1)).symm

end FundamentalGroup
