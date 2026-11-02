/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup.DiskAttachment.PuncturedComponent.Basic
public import FundamentalGroupoids.FundamentalGroup.DiskAttachment

/-!
# Fundamental group of a punctured attachment component

The radial retraction identifies the fundamental group of the punctured part of
an attachment component with that of the original space. The forward map is the
restricted retraction followed by inclusion of the original-space path component.
The inverse is induced by the component inclusion, after the inverse of the
path-component inclusion isomorphism.

The strict retraction identity and the restricted relative deformation give the
two whole-homomorphism inverse identities directly. They construct the
isomorphism with the component-inclusion inverse described above. No basedness
assumption on the attaching maps, or openness assumption on path components, is
needed. The two spaces and the disk-index type retain their natural universes.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 1, §4, for
  homotopy invariance of fundamental groups.
* `FundamentalGroup.mapOfEq_eq_of_homotopicRel`, for the basepoint-fixing
  homotopy identity used together with the strict retraction identity.
-/

@[expose] public section

universe u v

namespace FundamentalGroup

open TopCat

variable {X : Type u} [TopologicalSpace X] {J : Type v}

/-- The retraction isomorphism sends the positive generator of a selected disk to
its positive attaching loop class. Only that attaching map must preserve the
chosen basepoint. -/
theorem diskAttachmentPuncturedComponentMulEquiv_generator
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    diskAttachmentPuncturedComponentMulEquiv f x
        (diskAttachmentPuncturedComponentGenerator f x j hj) =
      mapOfEq (f j) hj (fromPath ⟦Circle.loop 1⟧) := by
  rw [diskAttachmentPuncturedComponentMulEquiv_apply]
  exact mapOfEq_diskAttachmentPuncturedComponentGenerator f x j hj

end FundamentalGroup
