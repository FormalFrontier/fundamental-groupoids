/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment

/-!
# Removing the centres of attached disks

The centres of the characteristic disks form a closed subset of a disk attachment,
even for an infinite family. Its complement has the inherited subspace topology.
The original-space map and the punctured-disk maps take values in this complement.
Compatible functions on these pieces descend without a continuity assumption at the
removed centres; continuous functions descend to a continuous map.
-/

open Topology

universe u v w

noncomputable section

namespace TopCat

variable {X : Type u} [TopologicalSpace X] {J : Type v}

@[expose] public section

/-- The image of the centre of an attached disk. -/
def diskAttachmentCenter (f : J → C(Circle, X)) (j : J) : diskAttachment f :=
  diskAttachmentDisk f j ⟨0, by simp⟩

/-- The centres of the characteristic disks. -/
def diskAttachmentCenters (f : J → C(Circle, X)) : Set (diskAttachment f) :=
  Set.range (diskAttachmentCenter f)

/-- Membership in the set of centres is witnessed by a disk index. -/
theorem mem_diskAttachmentCenters (f : J → C(Circle, X)) (p : diskAttachment f) :
    p ∈ diskAttachmentCenters f ↔ ∃ j, diskAttachmentCenter f j = p := by
  rfl

/-- The centre can also be evaluated on the open-disk characteristic map. -/
theorem diskAttachmentCenter_eq_interior (f : J → C(Circle, X)) (j : J) :
    diskAttachmentCenter f j = diskAttachmentInterior f j ⟨0, by simp⟩ := by
  exact (diskAttachmentInterior_apply f j ⟨0, by simp⟩).symm

/-- A centre cannot lie in the original-space image. -/
theorem diskAttachmentCenter_ne_inclusion (f : J → C(Circle, X)) (j : J) (x : X) :
    diskAttachmentCenter f j ≠ diskAttachmentInclusion f x := by
  rw [diskAttachmentCenter_eq_interior]
  exact diskAttachmentInterior_ne_inclusion f j _ x

/-- A closed-disk point is a specified centre precisely at zero in the same disk. -/
theorem diskAttachmentCenter_eq_disk_iff (f : J → C(Circle, X)) (j k : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1)) :
    diskAttachmentCenter f j = diskAttachmentDisk f k z ↔ j = k ∧ (z : ℂ) = 0 := by
  rw [diskAttachmentCenter_eq_interior, diskAttachmentInterior_eq_disk_iff]
  exact and_congr Iff.rfl eq_comm

/-- Distinct attached disks have distinct centres. -/
theorem diskAttachmentCenter_injective (f : J → C(Circle, X)) :
    Function.Injective (diskAttachmentCenter f) := by
  intro j k h
  exact ((diskAttachmentCenter_eq_disk_iff f j k ⟨0, by simp⟩).mp h).1

/-- No original-space point maps to a centre. -/
@[simp]
theorem diskAttachmentInclusion_preimage_centers (f : J → C(Circle, X)) :
    diskAttachmentInclusion f ⁻¹' diskAttachmentCenters f = ∅ := by
  ext x
  change (∃ j, diskAttachmentCenter f j = diskAttachmentInclusion f x) ↔ False
  constructor
  · rintro ⟨j, hj⟩
    exact diskAttachmentCenter_ne_inclusion f j x hj
  · exact False.elim

/-- The preimage of all centres in a closed disk is its singleton centre. -/
@[simp]
theorem diskAttachmentDisk_preimage_centers (f : J → C(Circle, X)) (j : J) :
    diskAttachmentDisk f j ⁻¹' diskAttachmentCenters f = {⟨0, by simp⟩} := by
  ext z
  change (∃ k, diskAttachmentCenter f k = diskAttachmentDisk f j z) ↔
    z = ⟨0, by simp⟩
  constructor
  · rintro ⟨k, hk⟩
    apply Subtype.ext
    exact ((diskAttachmentCenter_eq_disk_iff f k j z).mp hk).2
  · intro hz
    subst z
    exact ⟨j, rfl⟩

/-- The centre set is closed, with no finiteness assumption on the disk family. -/
theorem isClosed_diskAttachmentCenters (f : J → C(Circle, X)) :
    IsClosed (diskAttachmentCenters f) := by
  apply (isClosed_diskAttachment_iff f _).2
  constructor
  · rw [diskAttachmentInclusion_preimage_centers]
    exact isClosed_empty
  · intro j
    rw [diskAttachmentDisk_preimage_centers]
    exact isClosed_singleton

/-- Original-space points avoid the centre set. -/
@[simp]
theorem diskAttachmentInclusion_not_mem_centers (f : J → C(Circle, X)) (x : X) :
    diskAttachmentInclusion f x ∉ diskAttachmentCenters f := by
  rintro ⟨j, hj⟩
  exact diskAttachmentCenter_ne_inclusion f j x hj

/-- A point of a characteristic closed disk is a centre exactly at zero. -/
@[simp]
theorem diskAttachmentDisk_mem_centers_iff (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1)) :
    diskAttachmentDisk f j z ∈ diskAttachmentCenters f ↔ (z : ℂ) = 0 := by
  change z ∈ diskAttachmentDisk f j ⁻¹' diskAttachmentCenters f ↔ (z : ℂ) = 0
  rw [diskAttachmentDisk_preimage_centers]
  exact Subtype.ext_iff

/-- The attachment with all characteristic disk centres removed, with its subspace topology. -/
abbrev diskAttachmentPunctured (f : J → C(Circle, X)) :=
  ↥((diskAttachmentCenters f)ᶜ)

/-- The punctured attachment is an open subspace of the attachment. -/
theorem isOpen_diskAttachmentPunctured (f : J → C(Circle, X)) :
    IsOpen ((diskAttachmentCenters f)ᶜ) :=
  (isClosed_diskAttachmentCenters f).isOpen_compl

/-- The original-space map with codomain restricted away from the centres. -/
def diskAttachmentPuncturedInclusion (f : J → C(Circle, X)) :
    C(X, diskAttachmentPunctured f) :=
  ⟨fun x => ⟨diskAttachmentInclusion f x, diskAttachmentInclusion_not_mem_centers f x⟩,
    (diskAttachmentInclusion f).continuous.subtype_mk _⟩

/-- The restricted original-space map has the same underlying attachment point. -/
@[simp]
theorem diskAttachmentPuncturedInclusion_coe (f : J → C(Circle, X)) (x : X) :
    (diskAttachmentPuncturedInclusion f x : diskAttachment f) =
      diskAttachmentInclusion f x := by
  rfl

/-- A characteristic map restricted to the punctured closed disk. -/
def diskAttachmentPuncturedDisk (f : J → C(Circle, X)) (j : J) :
    C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}), diskAttachmentPunctured f) := by
  let q : C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}),
      ↥(Metric.closedBall (0 : ℂ) 1)) :=
    ⟨fun z => ⟨(z : ℂ), z.property.1⟩,
      continuous_subtype_val.subtype_mk fun z => z.property.1⟩
  let h : ∀ z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0}),
      diskAttachmentDisk f j (q z) ∉ diskAttachmentCenters f :=
    fun z hz => z.property.2 ((diskAttachmentDisk_mem_centers_iff f j (q z)).mp hz)
  exact ⟨fun z => ⟨diskAttachmentDisk f j (q z), h z⟩,
    ((diskAttachmentDisk f j).continuous.comp q.continuous).subtype_mk h⟩

/-- The restricted disk map has the same underlying attachment point. -/
@[simp]
theorem diskAttachmentPuncturedDisk_coe (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    (diskAttachmentPuncturedDisk f j z : diskAttachment f) =
      diskAttachmentDisk f j ⟨(z : ℂ), z.property.1⟩ := by
  rfl

/-- A boundary point is nonzero. -/
theorem diskBoundary_ne_zero (z : Circle) : (diskBoundary z : ℂ) ≠ 0 := by
  intro hz
  have hn := Circle.norm_coe z
  rw [← diskBoundary_coe z, hz, norm_zero] at hn
  exact zero_ne_one hn

/-- The boundary inclusion into the punctured closed disk. -/
def puncturedDiskBoundary :
    C(Circle, ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :=
  ⟨fun z => ⟨(diskBoundary z : ℂ), (diskBoundary z).property, diskBoundary_ne_zero z⟩,
    (continuous_subtype_val.comp diskBoundary.continuous).subtype_mk _⟩

/-- The punctured boundary inclusion preserves the underlying complex number. -/
@[simp]
theorem puncturedDiskBoundary_coe (z : Circle) :
    (puncturedDiskBoundary z : ℂ) = (z : ℂ) := by
  exact diskBoundary_coe z

/-- The attaching equality persists after removing the centres. -/
@[simp]
theorem diskAttachmentPuncturedDisk_boundary (f : J → C(Circle, X)) (j : J) (z : Circle) :
    diskAttachmentPuncturedDisk f j (puncturedDiskBoundary z) =
      diskAttachmentPuncturedInclusion f (f j z) := by
  apply Subtype.ext
  exact diskAttachmentDisk_boundary f j z

/-- The restricted attaching square as an equality of continuous maps. -/
theorem diskAttachmentPunctured_boundary (f : J → C(Circle, X)) (j : J) :
    (diskAttachmentPuncturedDisk f j).comp puncturedDiskBoundary =
      (diskAttachmentPuncturedInclusion f).comp (f j) := by
  ext z
  exact congrArg Subtype.val (diskAttachmentPuncturedDisk_boundary f j z)

/-- The original-space map into the punctured attachment is injective. -/
theorem diskAttachmentPuncturedInclusion_injective (f : J → C(Circle, X)) :
    Function.Injective (diskAttachmentPuncturedInclusion f) := by
  intro x y h
  exact diskAttachmentInclusion_injective f (congrArg Subtype.val h)

/-- A predicate on the punctured attachment is determined on the original space
and on the punctured disks. -/
theorem diskAttachmentPunctured_induction (f : J → C(Circle, X))
    {P : diskAttachmentPunctured f → Prop}
    (hX : ∀ x, P (diskAttachmentPuncturedInclusion f x))
    (hD : ∀ j z, P (diskAttachmentPuncturedDisk f j z))
    (p : diskAttachmentPunctured f) : P p := by
  have h : ∀ y : diskAttachment f, ∀ hy : y ∉ diskAttachmentCenters f, P ⟨y, hy⟩ := by
    refine diskAttachment_induction f (fun x hx => hX x) ?_
    intro j z hz
    have hn : (z : ℂ) ≠ 0 := by
      intro hzero
      exact hz ((diskAttachmentDisk_mem_centers_iff f j z).2 hzero)
    exact hD j ⟨(z : ℂ), z.property, hn⟩
  exact h p p.property

/-- Functions on the punctured attachment are determined by the restricted legs. -/
theorem diskAttachmentPunctured_ext {Z : Type w} (f : J → C(Circle, X))
    {a b : diskAttachmentPunctured f → Z}
    (hX : ∀ x, a (diskAttachmentPuncturedInclusion f x) =
      b (diskAttachmentPuncturedInclusion f x))
    (hD : ∀ j z, a (diskAttachmentPuncturedDisk f j z) =
      b (diskAttachmentPuncturedDisk f j z)) : a = b := by
  funext p
  exact diskAttachmentPunctured_induction f (P := fun w => a w = b w) hX hD p

/-- With no disks, the centre set is empty. -/
@[simp]
theorem diskAttachmentCenters_eq_empty (f : J → C(Circle, X)) [IsEmpty J] :
    diskAttachmentCenters f = ∅ := by
  ext p
  simp only [mem_diskAttachmentCenters, Set.mem_empty_iff_false]
  exact ⟨fun h => h.elim fun j _ => isEmptyElim j, False.elim⟩

end

private def puncturedDiskExtension {Z : Type w} (f : J → C(Circle, X))
    (g : X → Z) (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (j : J) (z : ↥(Metric.closedBall (0 : ℂ) 1)) : Z := by
  classical
  exact if hz : (z : ℂ) = 0 then g (f j 1)
    else d j ⟨(z : ℂ), z.property, hz⟩

private theorem puncturedDiskExtension_of_ne_zero {Z : Type w}
    (f : J → C(Circle, X)) (g : X → Z)
    (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (j : J) (z : ↥(Metric.closedBall (0 : ℂ) 1)) (hz : (z : ℂ) ≠ 0) :
    puncturedDiskExtension f g d j z = d j ⟨(z : ℂ), z.property, hz⟩ := by
  classical
  simp only [puncturedDiskExtension, dite_eq_right hz]

private theorem puncturedDiskExtension_boundary {Z : Type w}
    (f : J → C(Circle, X)) (g : X → Z)
    (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) (j : J) (z : Circle) :
    puncturedDiskExtension f g d j (diskBoundary z) = g (f j z) := by
  rw [puncturedDiskExtension_of_ne_zero f g d j _ (diskBoundary_ne_zero z)]
  exact h j z

private def puncturedAttachmentExtension {Z : Type w}
    (f : J → C(Circle, X)) (g : X → Z)
    (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) : diskAttachment f → Z := by
  exact diskAttachmentLift f g (puncturedDiskExtension f g d)
    (puncturedDiskExtension_boundary f g d h)

private theorem puncturedAttachmentExtension_inclusion {Z : Type w}
    (f : J → C(Circle, X)) (g : X → Z)
    (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) (x : X) :
    puncturedAttachmentExtension f g d h (diskAttachmentInclusion f x) = g x := by
  exact diskAttachmentLift_inclusion f g _ _ x

private theorem puncturedAttachmentExtension_disk {Z : Type w}
    (f : J → C(Circle, X)) (g : X → Z)
    (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z))
    (j : J) (z : ↥(Metric.closedBall (0 : ℂ) 1)) :
    puncturedAttachmentExtension f g d h (diskAttachmentDisk f j z) =
      puncturedDiskExtension f g d j z := by
  exact diskAttachmentLift_disk f g _ _ j z

public section

/-- Descent of compatible functions from the original space and the punctured disks.
No value or continuity at a removed centre is required. -/
def diskAttachmentPuncturedLift {Z : Type w} (f : J → C(Circle, X))
    (g : X → Z) (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) :
    diskAttachmentPunctured f → Z := by
  exact fun p => puncturedAttachmentExtension f g d h p

/-- Punctured descent agrees with its original-space function. -/
@[simp]
theorem diskAttachmentPuncturedLift_inclusion {Z : Type w} (f : J → C(Circle, X))
    (g : X → Z) (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) (x : X) :
    diskAttachmentPuncturedLift f g d h (diskAttachmentPuncturedInclusion f x) = g x := by
  exact puncturedAttachmentExtension_inclusion f g d h x

/-- Punctured descent agrees with each punctured-disk function. -/
@[simp]
theorem diskAttachmentPuncturedLift_disk {Z : Type w} (f : J → C(Circle, X))
    (g : X → Z) (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    diskAttachmentPuncturedLift f g d h (diskAttachmentPuncturedDisk f j z) = d j z := by
  change puncturedAttachmentExtension f g d h
    (diskAttachmentDisk f j ⟨(z : ℂ), z.property.1⟩) = d j z
  rw [puncturedAttachmentExtension_disk]
  exact puncturedDiskExtension_of_ne_zero f g d j ⟨(z : ℂ), z.property.1⟩
    (by simpa only [Set.mem_singleton_iff] using z.property.2)

/-- Compatible functions have a unique descent to the punctured attachment. -/
theorem diskAttachmentPuncturedLift_unique {Z : Type w} (f : J → C(Circle, X))
    (g : X → Z) (d : J → ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) → Z)
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z))
    (k : diskAttachmentPunctured f → Z)
    (hX : ∀ x, k (diskAttachmentPuncturedInclusion f x) = g x)
    (hD : ∀ j z, k (diskAttachmentPuncturedDisk f j z) = d j z) :
    k = diskAttachmentPuncturedLift f g d h := by
  apply diskAttachmentPunctured_ext f
  · intro x
    rw [diskAttachmentPuncturedLift_inclusion]
    exact hX x
  · intro j z
    rw [diskAttachmentPuncturedLift_disk]
    exact hD j z

/-- Punctured descent is continuous when all its presenting functions are continuous.
Only continuity away from the disk centres enters the proof. -/
theorem continuous_diskAttachmentPuncturedLift {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z))
    (d : J → C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}), Z))
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) :
    Continuous (diskAttachmentPuncturedLift f g (fun j => d j) h) := by
  have hc : ContinuousOn (puncturedAttachmentExtension f g (fun j => d j) h)
      ((diskAttachmentCenters f)ᶜ) := by
    apply (continuousOn_diskAttachment_iff_of_isOpen f _
      (isOpen_diskAttachmentPunctured f)).2
    constructor
    · simpa only [Function.comp_def, puncturedAttachmentExtension_inclusion]
        using (g.continuous.continuousOn : ContinuousOn g
          (diskAttachmentInclusion f ⁻¹' (diskAttachmentCenters f)ᶜ))
    · intro j
      apply continuousOn_iff_continuous_domRestrict.mpr
      let q : ↥(diskAttachmentDisk f j ⁻¹' (diskAttachmentCenters f)ᶜ) →
          ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) := fun z =>
        ⟨(z.val : ℂ), z.val.property, by
          intro hz
          exact z.property ((diskAttachmentDisk_mem_centers_iff f j z.val).2 hz)⟩
      have hq : Continuous q :=
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have heq :
          (fun z : ↥(diskAttachmentDisk f j ⁻¹' (diskAttachmentCenters f)ᶜ) =>
            puncturedAttachmentExtension f g (fun j => d j) h (diskAttachmentDisk f j z)) =
          (d j) ∘ q := by
        funext z
        rw [puncturedAttachmentExtension_disk]
        exact puncturedDiskExtension_of_ne_zero f g (fun j => d j) j z.val (q z).property.2
      change Continuous (fun z : ↥(diskAttachmentDisk f j ⁻¹' (diskAttachmentCenters f)ᶜ) =>
        puncturedAttachmentExtension f g (fun j => d j) h (diskAttachmentDisk f j z))
      rw [heq]
      exact (d j).continuous.comp hq
  exact continuousOn_iff_continuous_domRestrict.mp hc

/-- Descent of compatible continuous maps on the original space and punctured disks. -/
def diskAttachmentPuncturedDesc {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z))
    (d : J → C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}), Z))
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) :
    C(diskAttachmentPunctured f, Z) := by
  exact ⟨diskAttachmentPuncturedLift f g (fun j => d j) h,
    continuous_diskAttachmentPuncturedLift f g d h⟩

/-- Continuous punctured descent agrees with its original-space map. -/
@[simp]
theorem diskAttachmentPuncturedDesc_inclusion {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z))
    (d : J → C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}), Z))
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) (x : X) :
    diskAttachmentPuncturedDesc f g d h (diskAttachmentPuncturedInclusion f x) = g x := by
  exact diskAttachmentPuncturedLift_inclusion f g (fun j => d j) h x

/-- Continuous punctured descent agrees with each punctured-disk map. -/
@[simp]
theorem diskAttachmentPuncturedDesc_disk {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z))
    (d : J → C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}), Z))
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) :
    diskAttachmentPuncturedDesc f g d h (diskAttachmentPuncturedDisk f j z) = d j z := by
  exact diskAttachmentPuncturedLift_disk f g (fun j => d j) h j z

/-- A continuous map on the punctured attachment is determined by its presenting maps. -/
theorem diskAttachmentPuncturedDesc_unique {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z))
    (d : J → C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}), Z))
    (h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z))
    (k : C(diskAttachmentPunctured f, Z))
    (hX : ∀ x, k (diskAttachmentPuncturedInclusion f x) = g x)
    (hD : ∀ j z, k (diskAttachmentPuncturedDisk f j z) = d j z) :
    k = diskAttachmentPuncturedDesc f g d h := by
  ext p
  exact congrFun (diskAttachmentPuncturedLift_unique f g (fun j => d j) h k hX hD) p

/-- Continuity out of the punctured attachment can be checked on the original space
and the punctured characteristic disks, for an independently sized target. -/
theorem continuous_diskAttachmentPunctured_iff {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (k : diskAttachmentPunctured f → Z) :
    Continuous k ↔ Continuous (k ∘ diskAttachmentPuncturedInclusion f) ∧
      ∀ j, Continuous (k ∘ diskAttachmentPuncturedDisk f j) := by
  constructor
  · intro hk
    exact ⟨hk.comp (diskAttachmentPuncturedInclusion f).continuous,
      fun j => hk.comp (diskAttachmentPuncturedDisk f j).continuous⟩
  · rintro ⟨hX, hD⟩
    let g : C(X, Z) := ⟨k ∘ diskAttachmentPuncturedInclusion f, hX⟩
    let d : J → C(↥(Metric.closedBall (0 : ℂ) 1 \ {0}), Z) :=
      fun j => ⟨k ∘ diskAttachmentPuncturedDisk f j, hD j⟩
    have h : ∀ j z, d j (puncturedDiskBoundary z) = g (f j z) := by
      intro j z
      exact congrArg k (diskAttachmentPuncturedDisk_boundary f j z)
    have heq : k = ⇑(diskAttachmentPuncturedDesc f g d h) :=
      diskAttachmentPuncturedLift_unique f g (fun j => d j) h k
        (fun _ => rfl) (fun _ _ => rfl)
    rw [heq]
    exact (diskAttachmentPuncturedDesc f g d h).continuous

end

end TopCat
