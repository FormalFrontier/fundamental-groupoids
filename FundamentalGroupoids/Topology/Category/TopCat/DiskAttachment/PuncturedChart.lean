/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.PuncturedComponent
public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.PuncturedCircle
public import FundamentalGroupoids.Topology.Homotopy.ComplexPuncturedBall
public import FundamentalGroupoids.Topology.MetricSpace.PuncturedBall
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.NormNum

/-!
# Thickening a punctured attachment component by one disk

The set `TopCat.DiskAttachment.coreSet f x` is the underlying subset of the
punctured component `TopCat.diskAttachmentPuncturedComponent f x` in the disk
attachment. The ordinary subspace `TopCat.DiskAttachment.PuncturedChart f x j`
is its union with the image of the open interior of disk `j`.

If `f j 1 = x`, this union lies in the attachment path component of the image
of `x`. It is open relative to that path component; no ambient openness of a
path component is used. The maps from the punctured component and the open
disk are open embeddings and cover the chart. Their intersection is
homeomorphic to the punctured complex open unit ball and is path connected.
The disk piece is homeomorphic to the open unit ball and is contractible. The
chart is path connected, by path connectedness of the punctured component and an explicit
point in the intersection.

## Implementation notes

All sets and maps use the existing attachment and ordinary subspace topologies.
Only the open-disk characteristic map is used as an embedding. No injectivity
of the closed-disk characteristic map is required. These point-set results do
not assert simple connectedness or a fundamental-group universal property.
-/

@[expose] public section

universe u v w

namespace TopCat.DiskAttachment

open Set Metric

variable {X : Type u} [TopologicalSpace X] {J : Type v}

/-- The underlying subset of the punctured attachment component in the attachment. -/
def coreSet (f : J → C(Circle, X)) (x : X) : Set (diskAttachment f) :=
  {p | p ∉ diskAttachmentCenters f ∧ Joined (diskAttachmentInclusion f x) p}

@[simp]
theorem mem_coreSet (f : J → C(Circle, X)) (x : X) (p : diskAttachment f) :
    p ∈ coreSet f x ↔
      p ∉ diskAttachmentCenters f ∧ Joined (diskAttachmentInclusion f x) p := by
  rfl

/-- The core is the intersection of the punctured set and the attachment component. -/
theorem coreSet_eq (f : J → C(Circle, X)) (x : X) :
    coreSet f x = (diskAttachmentCenters f)ᶜ ∩ pathComponent (diskAttachmentInclusion f x) := by
  rfl

/-- Forget both subtype restrictions on the punctured component. -/
def coreMap (f : J → C(Circle, X)) (x : X) :
    C(diskAttachmentPuncturedComponent f x, diskAttachment f) := by
  exact ⟨fun c => c.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

@[simp]
theorem coreMap_apply (f : J → C(Circle, X)) (x : X)
    (c : diskAttachmentPuncturedComponent f x) :
    coreMap f x c = ((c : diskAttachmentPunctured f) : diskAttachment f) := by
  rfl

@[simp]
theorem range_coreMap (f : J → C(Circle, X)) (x : X) :
    Set.range (coreMap f x) = coreSet f x := by
  ext p
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.val.property, c.property⟩
  · rintro ⟨hn, hj⟩
    exact ⟨⟨⟨p, hn⟩, hj⟩, rfl⟩

/-- The nested component subtype has its ordinary subspace topology in the attachment. -/
theorem isEmbedding_coreMap (f : J → C(Circle, X)) (x : X) :
    Topology.IsEmbedding (coreMap f x) := by
  exact Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal

/-- Identify the punctured component with its underlying subset in the attachment. -/
noncomputable def coreHomeomorph (f : J → C(Circle, X)) (x : X) :
    diskAttachmentPuncturedComponent f x ≃ₜ ↥(coreSet f x) := by
  exact (isEmbedding_coreMap f x).toHomeomorph.trans
    (Homeomorph.setCongr (range_coreMap f x))

@[simp]
theorem coreHomeomorph_coe (f : J → C(Circle, X)) (x : X)
    (c : diskAttachmentPuncturedComponent f x) :
    (coreHomeomorph f x c : diskAttachment f) = coreMap f x c := by
  rfl

theorem coreHomeomorph_symm_coe (f : J → C(Circle, X)) (x : X)
    (p : ↥(coreSet f x)) :
    coreMap f x ((coreHomeomorph f x).symm p) = (p : diskAttachment f) := by
  simpa only [coreHomeomorph_coe] using
    congrArg Subtype.val ((coreHomeomorph f x).apply_symm_apply p)

/-- The inverse core coordinate has the same underlying attachment point. -/
@[simp]
theorem coreHomeomorph_symm_val (f : J → C(Circle, X)) (x : X)
    (p : ↥(coreSet f x)) :
    (((coreHomeomorph f x).symm p : diskAttachmentPunctured f) : diskAttachment f) =
      (p : diskAttachment f) := by
  simpa only [coreMap_apply] using coreHomeomorph_symm_coe f x p

/-- The core map sends the existing canonical component basepoint to the chosen image point. -/
theorem coreMap_basepoint (f : J → C(Circle, X)) (x : X) :
    coreMap f x (diskAttachmentPuncturedComponentInclusion f x
      ⟨x, mem_pathComponent_self x⟩) = diskAttachmentInclusion f x := by
  rfl

/-- The open interior image of a single characteristic disk. -/
def interiorSet (f : J → C(Circle, X)) (j : J) : Set (diskAttachment f) :=
  Set.range (diskAttachmentInterior f j)

@[simp]
theorem mem_interiorSet (f : J → C(Circle, X)) (j : J) (p : diskAttachment f) :
    p ∈ interiorSet f j ↔ ∃ z, diskAttachmentInterior f j z = p := by
  rfl

/-- Each disk interior image is open in the whole attachment. -/
theorem isOpen_interiorSet (f : J → C(Circle, X)) (j : J) :
    IsOpen (interiorSet f j) := by
  exact (isOpenEmbedding_diskAttachmentInterior f j).isOpen_range

/-- The interior image has precisely the topology of the complex open unit ball. -/
noncomputable def interiorHomeomorph (f : J → C(Circle, X)) (j : J) :
    ↥(Metric.ball (0 : ℂ) 1) ≃ₜ ↥(interiorSet f j) := by
  exact (isOpenEmbedding_diskAttachmentInterior f j).isEmbedding.toHomeomorph

@[simp]
theorem interiorHomeomorph_coe (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1)) :
    (interiorHomeomorph f j z : diskAttachment f) = diskAttachmentInterior f j z := by
  rfl

/-- The open disk image is contractible, with no condition on the attaching map. -/
theorem contractibleSpace_interiorSet (f : J → C(Circle, X)) (j : J) :
    ContractibleSpace ↥(interiorSet f j) := by
  let : ContractibleSpace ↥(Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  exact (interiorHomeomorph f j).symm.contractibleSpace

/-- A based characteristic disk lies in the chosen attachment path component,
including its centre and boundary. -/
@[simp]
theorem joined_disk (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (z : ↥(Metric.closedBall (0 : ℂ) 1)) :
    Joined (diskAttachmentInclusion f x) (diskAttachmentDisk f j z) := by
  have hpc : PathConnectedSpace ↥(Metric.closedBall (0 : ℂ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_closedBall (0 : ℂ) 1).isPathConnected ⟨0, by simp⟩)
  have h := (hpc.joined (diskBoundary 1) z).map (diskAttachmentDisk f j).continuous
  rw [diskAttachmentDisk_boundary, hj] at h
  exact h

/-- A based attaching map puts every point of its disk interior in the chosen component. -/
theorem joined_interior (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (z : ↥(Metric.ball (0 : ℂ) 1)) :
    Joined (diskAttachmentInclusion f x) (diskAttachmentInterior f j z) := by
  simpa only [diskAttachmentInterior_apply] using
    joined_disk f x j hj ⟨(z : ℂ), Metric.ball_subset_closedBall z.property⟩

/-- Each based disk interior lies in the attachment component, without any openness assumption. -/
theorem interiorSet_subset_pathComponent (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) :
    interiorSet f j ⊆ pathComponent (diskAttachmentInclusion f x) := by
  rintro p ⟨z, rfl⟩
  exact joined_interior f x j hj z

theorem interior_mem_centers_iff (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1)) :
    diskAttachmentInterior f j z ∈ diskAttachmentCenters f ↔ (z : ℂ) = 0 := by
  rw [diskAttachmentInterior_apply, diskAttachmentDisk_mem_centers_iff]

/-- In the chosen component, the core removes exactly the zero coordinate from an interior. -/
theorem interior_mem_coreSet_iff (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) (z : ↥(Metric.ball (0 : ℂ) 1)) :
    diskAttachmentInterior f j z ∈ coreSet f x ↔ (z : ℂ) ≠ 0 := by
  constructor
  · intro hp hz
    exact hp.1 ((interior_mem_centers_iff f j z).2 hz)
  · intro hz
    exact ⟨fun hp => hz ((interior_mem_centers_iff f j z).1 hp), joined_interior f x j hj z⟩

/-- The characteristic preimage of the core is the punctured open disk. -/
theorem interior_preimage_coreSet (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) :
    diskAttachmentInterior f j ⁻¹' coreSet f x =
      {z : ↥(Metric.ball (0 : ℂ) 1) | (z : ℂ) ≠ 0} := by
  ext z
  exact interior_mem_coreSet_iff f x j hj z

/-- Thicken the core by the whole open interior image of one disk. -/
def chartSet (f : J → C(Circle, X)) (x : X) (j : J) : Set (diskAttachment f) :=
  coreSet f x ∪ interiorSet f j

@[simp]
theorem mem_chartSet (f : J → C(Circle, X)) (x : X) (j : J) (p : diskAttachment f) :
    p ∈ chartSet f x j ↔ p ∈ coreSet f x ∨ p ∈ interiorSet f j := by
  rfl

/-- The ordinary subspace of the attachment underlying a thickened punctured chart. -/
abbrev PuncturedChart (f : J → C(Circle, X)) (x : X) (j : J) :=
  ↥(chartSet f x j)

/-- The chart lies in the chosen attachment path component for a based disk. -/
theorem chartSet_subset_pathComponent (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) :
    chartSet f x j ⊆ pathComponent (diskAttachmentInclusion f x) := by
  rintro p (hp | hp)
  · exact hp.2
  · exact interiorSet_subset_pathComponent f x j hj hp

/-- The core is open relative to the chosen attachment path component. -/
theorem isOpen_coreSet_relative (f : J → C(Circle, X)) (x : X) :
    IsOpen ((Subtype.val : ↥(pathComponent (diskAttachmentInclusion f x)) →
      diskAttachment f) ⁻¹' coreSet f x) := by
  have heq : (Subtype.val : ↥(pathComponent (diskAttachmentInclusion f x)) →
      diskAttachment f) ⁻¹' coreSet f x =
      Subtype.val ⁻¹' (diskAttachmentCenters f)ᶜ := by
    ext p
    constructor
    · exact And.left
    · intro hp
      exact ⟨hp, p.property⟩
  rw [heq]
  exact (isOpen_diskAttachmentPunctured f).preimage continuous_subtype_val

/-- Openness here is relative to the attachment path component, not to the attachment. -/
theorem isOpen_chartSet_relative (f : J → C(Circle, X)) (x : X) (j : J) :
    IsOpen ((Subtype.val : ↥(pathComponent (diskAttachmentInclusion f x)) →
      diskAttachment f) ⁻¹' chartSet f x j) := by
  exact (isOpen_coreSet_relative f x).union
    ((isOpen_interiorSet f j).preimage continuous_subtype_val)

/-- The inclusion of a based chart into the chosen attachment path component. -/
def chartComponentMap (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    C(PuncturedChart f x j, ↥(pathComponent (diskAttachmentInclusion f x))) := by
  exact ⟨fun p => ⟨p.val, chartSet_subset_pathComponent f x j hj p.property⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp]
theorem chartComponentMap_coe (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) (p : PuncturedChart f x j) :
    (chartComponentMap f x j hj p : diskAttachment f) = (p : diskAttachment f) := by
  rfl

@[simp]
theorem range_chartComponentMap (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) :
    Set.range (chartComponentMap f x j hj) =
      (Subtype.val : ↥(pathComponent (diskAttachmentInclusion f x)) →
        diskAttachment f) ⁻¹' chartSet f x j := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p.val, hp⟩, Subtype.ext rfl⟩

/-- The ordinary chart subspace is open embedded in the chosen path component. -/
theorem isOpenEmbedding_chartComponentMap (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) : Topology.IsOpenEmbedding (chartComponentMap f x j hj) := by
  refine ⟨?_, ?_⟩
  · apply Topology.IsEmbedding.of_comp (chartComponentMap f x j hj).continuous
      continuous_subtype_val
    exact Topology.IsEmbedding.subtypeVal
  · rw [range_chartComponentMap]
    exact isOpen_chartSet_relative f x j

/-- The inclusion of the punctured component into the thickened chart. -/
noncomputable def chartCore (f : J → C(Circle, X)) (x : X) (j : J) :
    C(diskAttachmentPuncturedComponent f x, PuncturedChart f x j) := by
  exact ⟨fun c => ⟨coreMap f x c, Or.inl ⟨c.val.property, c.property⟩⟩,
    (coreMap f x).continuous.subtype_mk _⟩

@[simp]
theorem chartCore_coe (f : J → C(Circle, X)) (x : X) (j : J)
    (c : diskAttachmentPuncturedComponent f x) :
    (chartCore f x j c : diskAttachment f) = coreMap f x c := by
  rfl

/-- Include the disk interior image itself, rather than its coordinates, into the chart. -/
def chartInterior (f : J → C(Circle, X)) (x : X) (j : J) :
    C(↥(interiorSet f j), PuncturedChart f x j) := by
  exact ⟨fun p => ⟨p.val, Or.inr p.property⟩, continuous_subtype_val.subtype_mk _⟩

@[simp]
theorem chartInterior_coe (f : J → C(Circle, X)) (x : X) (j : J)
    (p : ↥(interiorSet f j)) :
    (chartInterior f x j p : diskAttachment f) = (p : diskAttachment f) := by
  rfl

/-- The open-disk characteristic map with codomain restricted to the chart. -/
noncomputable def chartDisk (f : J → C(Circle, X)) (x : X) (j : J) :
    C(↥(Metric.ball (0 : ℂ) 1), PuncturedChart f x j) := by
  exact ⟨fun z => ⟨diskAttachmentInterior f j z, Or.inr ⟨z, rfl⟩⟩,
    (diskAttachmentInterior f j).continuous.subtype_mk _⟩

@[simp]
theorem chartDisk_coe (f : J → C(Circle, X)) (x : X) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1)) :
    (chartDisk f x j z : diskAttachment f) = diskAttachmentInterior f j z := by
  rfl

@[simp]
theorem chartInterior_interiorHomeomorph (f : J → C(Circle, X)) (x : X) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1)) :
    chartInterior f x j (interiorHomeomorph f j z) = chartDisk f x j z := by
  exact Subtype.ext rfl

/-- The core member of the binary cover, as a subset of the chart. -/
def coreCover (f : J → C(Circle, X)) (x : X) (j : J) : Set (PuncturedChart f x j) :=
  Subtype.val ⁻¹' coreSet f x

/-- The disk member of the binary cover, as a subset of the chart. -/
def diskCover (f : J → C(Circle, X)) (x : X) (j : J) : Set (PuncturedChart f x j) :=
  Subtype.val ⁻¹' interiorSet f j

@[simp]
theorem mem_coreCover (f : J → C(Circle, X)) (x : X) (j : J)
    (p : PuncturedChart f x j) : p ∈ coreCover f x j ↔ (p : diskAttachment f) ∈ coreSet f x := by
  rfl

@[simp]
theorem mem_diskCover (f : J → C(Circle, X)) (x : X) (j : J)
    (p : PuncturedChart f x j) :
    p ∈ diskCover f x j ↔ (p : diskAttachment f) ∈ interiorSet f j := by
  rfl

/-- The two subspaces cover every point of the chart. -/
theorem coreCover_union_diskCover (f : J → C(Circle, X)) (x : X) (j : J) :
    coreCover f x j ∪ diskCover f x j = Set.univ := by
  ext p
  exact iff_true_intro p.property

@[simp]
theorem range_chartCore (f : J → C(Circle, X)) (x : X) (j : J) :
    Set.range (chartCore f x j) = coreCover f x j := by
  ext p
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.val.property, c.property⟩
  · rintro ⟨hn, hp⟩
    exact ⟨⟨⟨p.val, hn⟩, hp⟩, Subtype.ext rfl⟩

@[simp]
theorem range_chartInterior (f : J → C(Circle, X)) (x : X) (j : J) :
    Set.range (chartInterior f x j) = diskCover f x j := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact q.property
  · intro hp
    exact ⟨⟨p.val, hp⟩, Subtype.ext rfl⟩

/-- The inclusions of the core and the disk image cover the chart. -/
theorem range_chartCore_union_range_chartInterior (f : J → C(Circle, X)) (x : X) (j : J) :
    Set.range (chartCore f x j) ∪ Set.range (chartInterior f x j) = Set.univ := by
  rw [range_chartCore, range_chartInterior, coreCover_union_diskCover]

@[simp]
theorem range_chartDisk (f : J → C(Circle, X)) (x : X) (j : J) :
    Set.range (chartDisk f x j) = diskCover f x j := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, Subtype.ext hz⟩

@[simp]
theorem chartCore_preimage_coreCover (f : J → C(Circle, X)) (x : X) (j : J) :
    chartCore f x j ⁻¹' coreCover f x j = Set.univ := by
  ext c
  exact iff_true_intro ⟨c.val.property, c.property⟩

@[simp]
theorem chartDisk_preimage_diskCover (f : J → C(Circle, X)) (x : X) (j : J) :
    chartDisk f x j ⁻¹' diskCover f x j = Set.univ := by
  ext z
  exact iff_true_intro ⟨z, rfl⟩

/-- The disk preimage of the other cover member removes exactly its centre. -/
theorem chartDisk_preimage_coreCover (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) :
    chartDisk f x j ⁻¹' coreCover f x j =
      {z : ↥(Metric.ball (0 : ℂ) 1) | (z : ℂ) ≠ 0} := by
  exact interior_preimage_coreSet f x j hj

/-- The core cover member is open using only relative component openness. -/
theorem isOpen_coreCover (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    IsOpen (coreCover f x j) := by
  exact (isOpen_coreSet_relative f x).preimage (chartComponentMap f x j hj).continuous

/-- The disk cover member is open because its image is open in the attachment. -/
theorem isOpen_diskCover (f : J → C(Circle, X)) (x : X) (j : J) :
    IsOpen (diskCover f x j) := by
  exact (isOpen_interiorSet f j).preimage continuous_subtype_val

/-- The inclusion of the disk image is an open embedding of ordinary subspaces. -/
theorem isOpenEmbedding_chartInterior (f : J → C(Circle, X)) (x : X) (j : J) :
    Topology.IsOpenEmbedding (chartInterior f x j) := by
  refine ⟨?_, ?_⟩
  · apply Topology.IsEmbedding.of_comp (chartInterior f x j).continuous continuous_subtype_val
    exact Topology.IsEmbedding.subtypeVal
  · rw [range_chartInterior]
    exact isOpen_diskCover f x j

/-- The punctured-component inclusion is an embedding for the ordinary subspace topologies. -/
theorem isEmbedding_chartCore (f : J → C(Circle, X)) (x : X) (j : J) :
    Topology.IsEmbedding (chartCore f x j) := by
  apply Topology.IsEmbedding.of_comp (chartCore f x j).continuous continuous_subtype_val
  exact isEmbedding_coreMap f x

/-- The disk inclusion inherits its embedding from the open-disk characteristic map. -/
theorem isEmbedding_chartDisk (f : J → C(Circle, X)) (x : X) (j : J) :
    Topology.IsEmbedding (chartDisk f x j) := by
  apply Topology.IsEmbedding.of_comp (chartDisk f x j).continuous continuous_subtype_val
  exact (isOpenEmbedding_diskAttachmentInterior f j).isEmbedding

/-- The punctured component is an open embedded member of the binary cover. -/
theorem isOpenEmbedding_chartCore (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) : Topology.IsOpenEmbedding (chartCore f x j) := by
  refine ⟨isEmbedding_chartCore f x j, ?_⟩
  rw [range_chartCore]
  exact isOpen_coreCover f x j hj

/-- The open disk is an open embedded member of the binary cover. -/
theorem isOpenEmbedding_chartDisk (f : J → C(Circle, X)) (x : X) (j : J) :
    Topology.IsOpenEmbedding (chartDisk f x j) := by
  refine ⟨isEmbedding_chartDisk f x j, ?_⟩
  rw [range_chartDisk]
  exact isOpen_diskCover f x j

/-- The core cover member has precisely the topology of the punctured component. -/
noncomputable def chartCoreHomeomorph (f : J → C(Circle, X)) (x : X) (j : J) :
    diskAttachmentPuncturedComponent f x ≃ₜ ↥(coreCover f x j) := by
  exact (isEmbedding_chartCore f x j).toHomeomorph.trans
    (Homeomorph.setCongr (range_chartCore f x j))

@[simp]
theorem chartCoreHomeomorph_coe (f : J → C(Circle, X)) (x : X) (j : J)
    (c : diskAttachmentPuncturedComponent f x) :
    (chartCoreHomeomorph f x j c : PuncturedChart f x j) = chartCore f x j c := by
  rfl

/-- The inverse core coordinate is characterized by the inclusion into the chart. -/
@[simp]
theorem chartCoreHomeomorph_symm_coe (f : J → C(Circle, X)) (x : X) (j : J)
    (p : ↥(coreCover f x j)) :
    chartCore f x j ((chartCoreHomeomorph f x j).symm p) =
      (p : PuncturedChart f x j) := by
  simpa only [chartCoreHomeomorph_coe] using
    congrArg Subtype.val ((chartCoreHomeomorph f x j).apply_symm_apply p)

/-- The disk cover member, with its subspace topology in the chart, is an open unit disk. -/
noncomputable def chartDiskHomeomorph (f : J → C(Circle, X)) (x : X) (j : J) :
    ↥(Metric.ball (0 : ℂ) 1) ≃ₜ ↥(diskCover f x j) := by
  exact (isEmbedding_chartDisk f x j).toHomeomorph.trans
    (Homeomorph.setCongr (range_chartDisk f x j))

@[simp]
theorem chartDiskHomeomorph_coe (f : J → C(Circle, X)) (x : X) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1)) :
    (chartDiskHomeomorph f x j z : PuncturedChart f x j) = chartDisk f x j z := by
  rfl

/-- The disk member of the chart cover is contractible. -/
theorem contractibleSpace_diskCover (f : J → C(Circle, X)) (x : X) (j : J) :
    ContractibleSpace ↥(diskCover f x j) := by
  let : ContractibleSpace ↥(Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, by simp⟩
  exact (chartDiskHomeomorph f x j).symm.contractibleSpace

/-- Equality of maps from a chart is tested on the two characteristic inclusions. -/
theorem chart_ext {Z : Sort w} (f : J → C(Circle, X)) (x : X) (j : J)
    {g k : PuncturedChart f x j → Z}
    (hc : ∀ c, g (chartCore f x j c) = k (chartCore f x j c))
    (hd : ∀ z, g (chartDisk f x j z) = k (chartDisk f x j z)) : g = k := by
  funext p
  have hp : p ∈ Set.range (chartCore f x j) ∪ Set.range (chartDisk f x j) := by
    rw [range_chartCore, range_chartDisk, coreCover_union_diskCover]
    exact Set.mem_univ p
  rcases hp with ⟨c, rfl⟩ | ⟨z, rfl⟩
  · exact hc c
  · exact hd z

/-- Equality may also be tested using the disk image itself instead of its coordinates. -/
theorem chart_ext_core_interior {Z : Sort w} (f : J → C(Circle, X)) (x : X) (j : J)
    {g k : PuncturedChart f x j → Z}
    (hc : ∀ c, g (chartCore f x j c) = k (chartCore f x j c))
    (hi : ∀ p, g (chartInterior f x j p) = k (chartInterior f x j p)) : g = k := by
  apply chart_ext f x j hc
  intro z
  simpa only [chartInterior_interiorHomeomorph] using hi (interiorHomeomorph f j z)

/-- Continuous maps from the chart are determined by their two restrictions. -/
theorem chart_hom_ext {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (x : X) (j : J)
    {g k : C(PuncturedChart f x j, Z)}
    (hc : ∀ c, g (chartCore f x j c) = k (chartCore f x j c))
    (hd : ∀ z, g (chartDisk f x j z) = k (chartDisk f x j z)) : g = k := by
  apply DFunLike.ext'
  exact chart_ext f x j hc hd

/-- Continuity out of a based chart is tested on its two open embedded pieces. -/
theorem continuous_chart_iff {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (g : PuncturedChart f x j → Z) :
    Continuous g ↔ Continuous (g ∘ chartCore f x j) ∧ Continuous (g ∘ chartDisk f x j) := by
  constructor
  · intro hg
    exact ⟨hg.comp (chartCore f x j).continuous, hg.comp (chartDisk f x j).continuous⟩
  · rintro ⟨hc, hd⟩
    rw [continuous_def]
    intro U hU
    have heq : g ⁻¹' U =
        chartCore f x j '' ((g ∘ chartCore f x j) ⁻¹' U) ∪
          chartDisk f x j '' ((g ∘ chartDisk f x j) ⁻¹' U) := by
      ext p
      constructor
      · intro hp
        have hcover : p ∈ Set.range (chartCore f x j) ∪ Set.range (chartDisk f x j) := by
          rw [range_chartCore, range_chartDisk, coreCover_union_diskCover]
          exact Set.mem_univ p
        rcases hcover with ⟨c, rfl⟩ | ⟨z, rfl⟩
        · exact Or.inl ⟨c, hp, rfl⟩
        · exact Or.inr ⟨z, hp, rfl⟩
      · rintro (⟨c, hc, rfl⟩ | ⟨z, hz, rfl⟩)
        · exact hc
        · exact hz
    rw [heq]
    exact ((isOpenEmbedding_chartCore f x j hj).isOpenMap _ (hU.preimage hc)).union
      ((isOpenEmbedding_chartDisk f x j).isOpenMap _ (hU.preimage hd))

/-- Continuity may equivalently be tested on the inclusions of the core and the disk image. -/
theorem continuous_chart_iff_core_interior {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (g : PuncturedChart f x j → Z) :
    Continuous g ↔ Continuous (g ∘ chartCore f x j) ∧
      Continuous (g ∘ chartInterior f x j) := by
  constructor
  · intro hg
    exact ⟨hg.comp (chartCore f x j).continuous, hg.comp (chartInterior f x j).continuous⟩
  · rintro ⟨hc, hd⟩
    apply (continuous_chart_iff f x j hj g).2
    refine ⟨hc, ?_⟩
    simpa only [Function.comp_def, chartInterior_interiorHomeomorph] using
      hd.comp (interiorHomeomorph f j).continuous

/-- Include the punctured complex open unit ball into the open unit ball. -/
noncomputable def puncturedBallInclusion :
    C(↥(Metric.ball (0 : ℂ) 1 \ {0}), ↥(Metric.ball (0 : ℂ) 1)) := by
  exact ContinuousMap.inclusion Set.sdiff_subset

@[simp]
theorem puncturedBallInclusion_coe (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    (puncturedBallInclusion z : ℂ) = (z : ℂ) := by
  rfl

/-- Removing the zero coordinate is an ordinary subspace restriction. -/
theorem isEmbedding_puncturedBallInclusion : Topology.IsEmbedding puncturedBallInclusion := by
  apply Topology.IsEmbedding.of_comp puncturedBallInclusion.continuous continuous_subtype_val
  exact Topology.IsEmbedding.subtypeVal

/-- The punctured interior characteristic map in the attachment. -/
noncomputable def puncturedInterior (f : J → C(Circle, X)) (j : J) :
    C(↥(Metric.ball (0 : ℂ) 1 \ {0}), diskAttachment f) := by
  exact (diskAttachmentInterior f j).comp puncturedBallInclusion

@[simp]
theorem puncturedInterior_apply (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    puncturedInterior f j z = diskAttachmentInterior f j (puncturedBallInclusion z) := by
  rfl

/-- Open- and closed-punctured coordinates with the same complex value give the same image. -/
theorem puncturedInterior_eq_puncturedDisk_of_coe (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1 \ {0}))
    (w : ↥(Metric.closedBall (0 : ℂ) 1 \ {0})) (hzw : (z : ℂ) = (w : ℂ)) :
    puncturedInterior f j z = (diskAttachmentPuncturedDisk f j w : diskAttachment f) := by
  rw [puncturedInterior_apply, diskAttachmentInterior_apply, diskAttachmentPuncturedDisk_coe]
  apply congrArg (diskAttachmentDisk f j)
  exact Subtype.ext hzw

/-- The intersection in the attachment is the image of the punctured open disk. -/
theorem range_puncturedInterior (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) :
    Set.range (puncturedInterior f j) = coreSet f x ∩ interiorSet f j := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(interior_mem_coreSet_iff f x j hj _).2 ?_, ⟨puncturedBallInclusion z, rfl⟩⟩
    simpa only [puncturedBallInclusion_coe, mem_singleton_iff] using z.property.2
  · rintro ⟨hc, z, hz⟩
    have hn : (z : ℂ) ≠ 0 := (interior_mem_coreSet_iff f x j hj z).1 (hz.symm ▸ hc)
    exact ⟨⟨(z : ℂ), z.property, by simpa only [mem_singleton_iff] using hn⟩, hz⟩

/-- A homeomorphism onto the core/interior intersection in the attachment. -/
noncomputable def interiorIntersectionHomeomorph (f : J → C(Circle, X)) (x : X)
    (j : J) (hj : f j 1 = x) :
    ↥(Metric.ball (0 : ℂ) 1 \ {0}) ≃ₜ ↥(coreSet f x ∩ interiorSet f j) := by
  exact ((isOpenEmbedding_diskAttachmentInterior f j).isEmbedding.comp
    isEmbedding_puncturedBallInclusion).toHomeomorph.trans
      (Homeomorph.setCongr (range_puncturedInterior f x j hj))

@[simp]
theorem interiorIntersectionHomeomorph_coe (f : J → C(Circle, X)) (x : X)
    (j : J) (hj : f j 1 = x) (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    (interiorIntersectionHomeomorph f x j hj z : diskAttachment f) =
      puncturedInterior f j z := by
  rfl

/-- The punctured disk map with codomain in the chart. -/
noncomputable def chartOverlap (f : J → C(Circle, X)) (x : X) (j : J) :
    C(↥(Metric.ball (0 : ℂ) 1 \ {0}), PuncturedChart f x j) := by
  exact (chartDisk f x j).comp puncturedBallInclusion

@[simp]
theorem chartOverlap_apply (f : J → C(Circle, X)) (x : X) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    chartOverlap f x j z = chartDisk f x j (puncturedBallInclusion z) := by
  rfl

theorem chartOverlap_coe (f : J → C(Circle, X)) (x : X) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    (chartOverlap f x j z : diskAttachment f) = puncturedInterior f j z := by
  rfl

/-- The punctured disk parametrizes exactly the intersection of the binary cover. -/
theorem range_chartOverlap (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    Set.range (chartOverlap f x j) = coreCover f x j ∩ diskCover f x j := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact (Set.ext_iff.mp (range_puncturedInterior f x j hj) _).mp ⟨z, rfl⟩
  · intro hp
    obtain ⟨z, hz⟩ := (Set.ext_iff.mp (range_puncturedInterior f x j hj) _).mpr hp
    exact ⟨z, Subtype.ext hz⟩

/-- The cover intersection is homeomorphic to the complex open unit ball minus zero. -/
noncomputable def overlapHomeomorph (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) :
    ↥(Metric.ball (0 : ℂ) 1 \ {0}) ≃ₜ ↥(coreCover f x j ∩ diskCover f x j) := by
  exact ((isEmbedding_chartDisk f x j).comp isEmbedding_puncturedBallInclusion).toHomeomorph.trans
    (Homeomorph.setCongr (range_chartOverlap f x j hj))

@[simp]
theorem overlapHomeomorph_apply (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) (z : ↥(Metric.ball (0 : ℂ) 1 \ {0})) :
    (overlapHomeomorph f x j hj z : PuncturedChart f x j) = chartOverlap f x j z := by
  rfl

/-- The inverse coordinate is characterized by the punctured interior map. -/
theorem overlapHomeomorph_symm_apply (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) (p : ↥(coreCover f x j ∩ diskCover f x j)) :
    chartOverlap f x j ((overlapHomeomorph f x j hj).symm p) =
      (p : PuncturedChart f x j) := by
  simpa only [overlapHomeomorph_apply] using
    congrArg Subtype.val ((overlapHomeomorph f x j hj).apply_symm_apply p)

/-- The inverse overlap coordinate recovers its chart point through the disk map. -/
@[simp]
theorem chartDisk_puncturedBallInclusion_overlapHomeomorph_symm
    (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) (p : ↥(coreCover f x j ∩ diskCover f x j)) :
    chartDisk f x j (puncturedBallInclusion ((overlapHomeomorph f x j hj).symm p)) =
      (p : PuncturedChart f x j) := by
  simpa only [chartOverlap_apply] using overlapHomeomorph_symm_apply f x j hj p

/-- The intersection of the core and disk cover members is path connected for a based disk. -/
theorem isPathConnected_overlap (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) :
    IsPathConnected (coreCover f x j ⊓ diskCover f x j : Set (PuncturedChart f x j)) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    simpa only [Complex.rank_real_complex] using Cardinal.one_lt_two
  let : PathConnectedSpace ↥(Metric.ball (0 : ℂ) 1 \ {0}) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_ball_diff_singleton_of_one_lt_rank hrank (0 : ℂ) zero_lt_one)
  let O : ↥(Metric.ball (0 : ℂ) 1 \ {0}) ≃ₜ
      ↥(coreCover f x j ∩ diskCover f x j) := overlapHomeomorph f x j hj
  let g : ↥(Metric.ball (0 : ℂ) 1 \ {0}) → PuncturedChart f x j :=
    fun z => (O z : PuncturedChart f x j)
  have hg : Continuous g := continuous_subtype_val.comp O.continuous
  have himage : g '' (Set.univ : Set ↥(Metric.ball (0 : ℂ) 1 \ {0})) =
      (coreCover f x j ⊓ diskCover f x j : Set (PuncturedChart f x j)) := by
    ext p
    constructor
    · rintro ⟨z, _, rfl⟩
      exact (O z).property
    · intro hp
      refine ⟨O.symm ⟨p, hp⟩, Set.mem_univ _, ?_⟩
      exact congrArg Subtype.val (O.apply_symm_apply ⟨p, hp⟩)
  rw [← himage]
  exact isPathConnected_univ.image hg

/-- The real coordinate one half in the punctured complex open unit ball. -/
noncomputable def halfCoordinate : ↥(Metric.ball (0 : ℂ) 1 \ {0}) := by
  refine ⟨((1 / 2 : ℝ) : ℂ), ?_, ?_⟩
  · norm_num [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  · norm_num

@[simp]
theorem halfCoordinate_coe : (halfCoordinate : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
  rfl

/-- Lift the half-coordinate point to the canonical punctured component. -/
noncomputable def coreHalfPoint (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    diskAttachmentPuncturedComponent f x := by
  have hp : puncturedInterior f j halfCoordinate ∈ coreSet f x :=
    ((Set.ext_iff.mp (range_puncturedInterior f x j hj) _).mp ⟨halfCoordinate, rfl⟩).1
  exact ⟨⟨puncturedInterior f j halfCoordinate, hp.1⟩, hp.2⟩

theorem coreMap_halfPoint (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    coreMap f x (coreHalfPoint f x j hj) = puncturedInterior f j halfCoordinate := by
  rfl

/-- The half-point lift has the punctured half-coordinate as its underlying attachment point. -/
@[simp]
theorem coreHalfPoint_coe (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    ((coreHalfPoint f x j hj : diskAttachmentPunctured f) : diskAttachment f) =
      puncturedInterior f j halfCoordinate := by
  simpa only [coreMap_apply] using coreMap_halfPoint f x j hj

/-- The half-point image agrees with any closed-punctured representative of coordinate one half. -/
theorem coreMap_halfPoint_eq_puncturedDisk (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) (w : ↥(Metric.closedBall (0 : ℂ) 1 \ {0}))
    (hw : (w : ℂ) = ((1 / 2 : ℝ) : ℂ)) :
    coreMap f x (coreHalfPoint f x j hj) =
      (diskAttachmentPuncturedDisk f j w : diskAttachment f) := by
  rw [coreMap_halfPoint]
  exact puncturedInterior_eq_puncturedDisk_of_coe f j halfCoordinate w
    (halfCoordinate_coe.trans hw.symm)

/-- Equality with the half-coordinate lift is tested on the underlying attachment point. -/
theorem coreHalfPoint_eq_iff (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (c : diskAttachmentPuncturedComponent f x) :
    coreHalfPoint f x j hj = c ↔ coreMap f x c = puncturedInterior f j halfCoordinate := by
  constructor
  · intro hc
    exact hc ▸ coreMap_halfPoint f x j hj
  · intro hc
    exact (isEmbedding_coreMap f x).injective
      ((coreMap_halfPoint f x j hj).trans hc.symm)

/-- A component point with closed-punctured half coordinate is the constructed half-point lift. -/
theorem coreHalfPoint_eq_of_puncturedDisk (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) (w : ↥(Metric.closedBall (0 : ℂ) 1 \ {0}))
    (hw : (w : ℂ) = ((1 / 2 : ℝ) : ℂ)) (c : diskAttachmentPuncturedComponent f x)
    (hc : coreMap f x c = (diskAttachmentPuncturedDisk f j w : diskAttachment f)) :
    coreHalfPoint f x j hj = c := by
  exact (isEmbedding_coreMap f x).injective
    ((coreMap_halfPoint_eq_puncturedDisk f x j hj w hw).trans hc.symm)

@[simp]
theorem chartCore_halfPoint (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    chartCore f x j (coreHalfPoint f x j hj) = chartOverlap f x j halfCoordinate := by
  exact Subtype.ext rfl

/-- The cover intersection contains the explicitly constructed half-coordinate point. -/
theorem overlap_nonempty (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    (coreCover f x j ∩ diskCover f x j).Nonempty := by
  exact ⟨chartOverlap f x j halfCoordinate,
    (Set.ext_iff.mp (range_chartOverlap f x j hj) _).mp ⟨halfCoordinate, rfl⟩⟩

/-- Path connectedness of the core as a subset of the attachment follows from
its component model. -/
theorem isPathConnected_coreSet (f : J → C(Circle, X)) (x : X) :
    IsPathConnected (coreSet f x) := by
  let : PathConnectedSpace (diskAttachmentPuncturedComponent f x) :=
    diskAttachmentPuncturedComponent_pathConnectedSpace f x
  rw [← range_coreMap f x]
  exact isPathConnected_range (coreMap f x).continuous

/-- The open interior image is path connected. -/
theorem isPathConnected_interiorSet (f : J → C(Circle, X)) (j : J) :
    IsPathConnected (interiorSet f j) := by
  let : PathConnectedSpace ↥(Metric.ball (0 : ℂ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_ball (0 : ℂ) 1).isPathConnected ⟨0, by simp⟩)
  exact isPathConnected_range (diskAttachmentInterior f j).continuous

/-- The thickened chart is path connected by its core, disk, and nonempty overlap. -/
theorem pathConnectedSpace_chart (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) : PathConnectedSpace (PuncturedChart f x j) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply (isPathConnected_coreSet f x).union (isPathConnected_interiorSet f j)
  exact ⟨puncturedInterior f j halfCoordinate,
    (Set.ext_iff.mp (range_puncturedInterior f x j hj) _).mp ⟨halfCoordinate, rfl⟩⟩

/-- The half-radius parametrization of the overlap is the component half-circle
followed by inclusion into the chart. -/
theorem chartOverlap_comp_halfCircle (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) :
    (chartOverlap f x j).comp
        (Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one) =
      (chartCore f x j).comp (diskAttachmentPuncturedComponentHalfCircle f x j hj) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  simp only [ContinuousMap.comp_apply, chartOverlap_coe, chartCore_coe, coreMap_apply,
    diskAttachmentPuncturedComponentHalfCircle_coe]
  apply puncturedInterior_eq_puncturedDisk_of_coe
  rw [Complex.circleToPuncturedBall_apply, puncturedDiskHalfCircle_coe]

/-- The overlap half-circle and the component half-circle have the same chart image. -/
theorem chartOverlap_halfCircle_apply (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) (z : Circle) :
    chartOverlap f x j
        (Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one z) =
      chartCore f x j (diskAttachmentPuncturedComponentHalfCircle f x j hj z) := by
  simpa only [ContinuousMap.comp_apply] using
    congrArg (fun g : C(Circle, PuncturedChart f x j) => g z)
      (chartOverlap_comp_halfCircle f x j hj)

/-- Following the overlap half-circle into the core side of the cover and then
using the inverse core homeomorphism gives the component half-circle as a whole map. -/
theorem chartCoreHomeomorph_symm_comp_overlap_halfCircle
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    (((isEmbedding_chartCore f x j).toHomeomorph.trans
          (Homeomorph.setCongr (range_chartCore f x j))).symm :
        C(↥(coreCover f x j), diskAttachmentPuncturedComponent f x)).comp
        ((ContinuousMap.inclusion
            (Set.inter_subset_left :
              coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j)).comp
          ((overlapHomeomorph f x j hj :
              C(↥(Metric.ball (0 : ℂ) 1 \ {0}),
                ↥(coreCover f x j ∩ diskCover f x j))).comp
            (Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one))) =
      diskAttachmentPuncturedComponentHalfCircle f x j hj := by
  apply ContinuousMap.ext
  intro z
  have h : (chartCoreHomeomorph f x j).symm
      (ContinuousMap.inclusion
        (Set.inter_subset_left :
          coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j)
        (overlapHomeomorph f x j hj
          (Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one z))) =
      diskAttachmentPuncturedComponentHalfCircle f x j hj z := by
    let p : ↥(coreCover f x j) :=
      ContinuousMap.inclusion
        (Set.inter_subset_left :
          coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j)
        (overlapHomeomorph f x j hj
          (Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one z))
    apply (isEmbedding_chartCore f x j).injective
    calc
      chartCore f x j ((chartCoreHomeomorph f x j).symm p) =
          (p : PuncturedChart f x j) := chartCoreHomeomorph_symm_coe f x j p
      _ = chartOverlap f x j
          (Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one z) :=
        overlapHomeomorph_apply f x j hj _
      _ = chartCore f x j (diskAttachmentPuncturedComponentHalfCircle f x j hj z) :=
        chartOverlap_halfCircle_apply f x j hj z
  simpa only [chartCoreHomeomorph, ContinuousMap.comp_apply, ContinuousMap.coe_coe] using h

end TopCat.DiskAttachment
