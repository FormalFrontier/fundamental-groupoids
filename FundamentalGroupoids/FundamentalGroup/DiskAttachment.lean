/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup
public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment
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

## Limitations

These results annihilate the attaching relations; they do not characterize the
kernel or assert surjectivity of the inclusion homomorphism.
-/

@[expose] public section

universe u v

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

end FundamentalGroup
