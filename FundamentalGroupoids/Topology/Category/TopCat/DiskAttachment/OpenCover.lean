/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.PuncturedChart
public import Mathlib.Topology.Category.TopCat.OpenNhds
public import Mathlib.Topology.Sets.OpenCover

/-!
# A common-core cover of an attachment component

For a based family of attaching circles, the punctured part of the attachment
component and its thickenings by individual open disks form an open cover of
that component, indexed by `Option J`. Every member contains the punctured
core, and distinct members intersect in precisely that core. All members and
all pairwise intersections are path connected.

The cover uses the existing component subspace, punctured component, and disk
charts. The range homeomorphisms preserve the inclusions into the attachment
and the point coming from the original space. The corresponding open
neighborhoods have the common-overlap input shape for fundamental-group
open-cover theorems. No simple connectedness of the core is asserted.
-/

@[expose] public section

universe u v

namespace TopCat.DiskAttachment

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X] {J : Type v}

/-- The point of the attachment component induced by the original-space point. -/
noncomputable def componentBasepoint (f : J → C(Circle, X)) (x : X) :
    ↥(pathComponent (diskAttachmentInclusion f x)) :=
  ⟨diskAttachmentInclusion f x, mem_pathComponent_self _⟩

@[simp]
theorem componentBasepoint_coe (f : J → C(Circle, X)) (x : X) :
    (componentBasepoint f x : diskAttachment f) = diskAttachmentInclusion f x := by
  rfl

/-- The inclusion of the punctured component into the attachment component. -/
noncomputable def componentCoreMap (f : J → C(Circle, X)) (x : X) :
    C(diskAttachmentPuncturedComponent f x,
      ↥(pathComponent (diskAttachmentInclusion f x))) := by
  exact ⟨fun c => ⟨coreMap f x c, c.property⟩,
    (coreMap f x).continuous.subtype_mk _⟩

@[simp]
theorem componentCoreMap_coe (f : J → C(Circle, X)) (x : X)
    (c : diskAttachmentPuncturedComponent f x) :
    (componentCoreMap f x c : diskAttachment f) = coreMap f x c := by
  rfl

@[simp]
theorem range_componentCoreMap (f : J → C(Circle, X)) (x : X) :
    Set.range (componentCoreMap f x) =
      (Subtype.val : ↥(pathComponent (diskAttachmentInclusion f x)) →
        diskAttachment f) ⁻¹' coreSet f x := by
  ext p
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.val.property, c.property⟩
  · rintro ⟨hn, hj⟩
    exact ⟨⟨⟨p.val, hn⟩, hj⟩, Subtype.ext rfl⟩

/-- The core inclusion is an embedding for the ordinary component topology. -/
theorem isEmbedding_componentCoreMap (f : J → C(Circle, X)) (x : X) :
    Topology.IsEmbedding (componentCoreMap f x) := by
  apply Topology.IsEmbedding.of_comp (componentCoreMap f x).continuous continuous_subtype_val
  exact isEmbedding_coreMap f x

/-- The core is open embedded in the attachment component. -/
theorem isOpenEmbedding_componentCoreMap (f : J → C(Circle, X)) (x : X) :
    Topology.IsOpenEmbedding (componentCoreMap f x) := by
  refine ⟨isEmbedding_componentCoreMap f x, ?_⟩
  rw [range_componentCoreMap]
  exact isOpen_coreSet_relative f x

@[simp]
theorem componentCoreMap_basepoint (f : J → C(Circle, X)) (x : X) :
    componentCoreMap f x (diskAttachmentPuncturedComponentInclusion f x
      ⟨x, mem_pathComponent_self x⟩) = componentBasepoint f x := by
  rfl

/-- The two core inclusions agree after including a single based chart. -/
@[simp]
theorem chartComponentMap_chartCore (f : J → C(Circle, X)) (x : X) (j : J)
    (hj : f j 1 = x) (c : diskAttachmentPuncturedComponent f x) :
    chartComponentMap f x j hj (chartCore f x j c) = componentCoreMap f x c := by
  rfl

/-- Distinct thickened charts meet in the punctured core. -/
theorem chartSet_inter_chartSet (f : J → C(Circle, X)) (x : X)
    {j k : J} (hjk : j ≠ k) :
    chartSet f x j ∩ chartSet f x k = coreSet f x := by
  ext p
  constructor
  · rintro ⟨hp | hp, hq | hq⟩
    · exact hp
    · exact hp
    · exact hq
    · exact False.elim
        ((Set.disjoint_left.mp (disjoint_range_diskAttachmentInterior f hjk)) hp hq)
  · intro hp
    exact ⟨Or.inl hp, Or.inl hp⟩

/-- The punctured core and all based thickened charts, as opens of the attachment
component. The `none` member is the core and the `some j` member is chart `j`. -/
def componentOpenCover (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x) :
    Option J → Opens ↥(pathComponent (diskAttachmentInclusion f x))
  | none => ⟨Set.range (componentCoreMap f x), by
      rw [range_componentCoreMap]
      exact isOpen_coreSet_relative f x⟩
  | some j => ⟨Set.range (chartComponentMap f x j (h j)), by
      rw [range_chartComponentMap]
      exact isOpen_chartSet_relative f x j⟩

@[simp]
theorem coe_componentOpenCover_none (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) :
    (componentOpenCover f x h none : Set ↥(pathComponent (diskAttachmentInclusion f x))) =
      Subtype.val ⁻¹' coreSet f x := by
  exact range_componentCoreMap f x

@[simp]
theorem coe_componentOpenCover_some (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j : J) :
    (componentOpenCover f x h (some j) :
      Set ↥(pathComponent (diskAttachmentInclusion f x))) =
      Subtype.val ⁻¹' chartSet f x j := by
  exact range_chartComponentMap f x j (h j)

@[simp]
theorem mem_componentOpenCover_none (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (p : ↥(pathComponent (diskAttachmentInclusion f x))) :
    p ∈ componentOpenCover f x h none ↔ (p : diskAttachment f) ∈ coreSet f x := by
  change p ∈ Set.range (componentCoreMap f x) ↔ _
  rw [range_componentCoreMap]
  rfl

/-- In the chosen component, belonging to the core means avoiding all disk centers. -/
theorem mem_componentOpenCover_none_iff (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (p : ↥(pathComponent (diskAttachmentInclusion f x))) :
    p ∈ componentOpenCover f x h none ↔
      (p : diskAttachment f) ∉ diskAttachmentCenters f := by
  rw [mem_componentOpenCover_none, mem_coreSet]
  exact ⟨And.left, fun hp => ⟨hp, p.property⟩⟩

@[simp]
theorem mem_componentOpenCover_some (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j : J)
    (p : ↥(pathComponent (diskAttachmentInclusion f x))) :
    p ∈ componentOpenCover f x h (some j) ↔
      (p : diskAttachment f) ∈ coreSet f x ∨ (p : diskAttachment f) ∈ interiorSet f j := by
  change p ∈ Set.range (chartComponentMap f x j (h j)) ↔ _
  rw [range_chartComponentMap]
  rfl

/-- Every chart of the cover contains the punctured core. -/
theorem componentOpenCover_none_le (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (i : Option J) :
    componentOpenCover f x h none ≤ componentOpenCover f x h i := by
  cases i with
  | none => exact le_rfl
  | some j =>
    intro p hp
    exact (mem_componentOpenCover_some f x h j p).2
      (Or.inl ((mem_componentOpenCover_none f x h p).1 hp))

/-- The same original-space point belongs to every member of the cover. -/
@[simp]
theorem componentBasepoint_mem_componentOpenCover (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (i : Option J) :
    componentBasepoint f x ∈ componentOpenCover f x h i := by
  apply componentOpenCover_none_le f x h i
  exact (mem_componentOpenCover_none f x h _).2
    ⟨diskAttachmentInclusion_not_mem_centers f x, mem_pathComponent_self _⟩

/-- Every point of the component is in the core or in one of the open disk interiors. -/
theorem exists_mem_componentOpenCover (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (p : ↥(pathComponent (diskAttachmentInclusion f x))) :
    ∃ i, p ∈ componentOpenCover f x h i := by
  classical
  by_cases hp : (p : diskAttachment f) ∈ diskAttachmentCenters f
  · obtain ⟨j, hj⟩ := (mem_diskAttachmentCenters f (p : diskAttachment f)).1 hp
    refine ⟨some j, (mem_componentOpenCover_some f x h j p).2 (Or.inr ?_)⟩
    exact ⟨⟨0, by simp⟩, (diskAttachmentCenter_eq_interior f j).symm.trans hj⟩
  · exact ⟨none, (mem_componentOpenCover_none_iff f x h p).2 hp⟩

/-- The component cover has supremum equal to the whole component. -/
theorem iSup_componentOpenCover (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) :
    (⨆ i, componentOpenCover f x h i) = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨i, hi⟩ := exists_mem_componentOpenCover f x h p
  exact (le_iSup (componentOpenCover f x h) i) hi

/-- The core and the thickened charts are an open cover of the attachment component. -/
theorem isOpenCover_componentOpenCover (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) :
    IsOpenCover (componentOpenCover f x h) :=
  IsOpenCover.mk (iSup_componentOpenCover f x h)

/-- With no disks, the sole member of the component cover is the whole component. -/
theorem componentOpenCover_none_eq_top [IsEmpty J] (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) : componentOpenCover f x h none = ⊤ := by
  apply top_unique
  intro p _
  obtain ⟨i, hi⟩ := exists_mem_componentOpenCover f x h p
  cases i with
  | none => exact hi
  | some j => exact isEmptyElim j

/-- Every member of the component cover is path connected. -/
theorem isPathConnected_componentOpenCover (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (i : Option J) :
    IsPathConnected (componentOpenCover f x h i :
      Set ↥(pathComponent (diskAttachmentInclusion f x))) := by
  cases i with
  | none =>
    let : PathConnectedSpace (diskAttachmentPuncturedComponent f x) :=
      diskAttachmentPuncturedComponent_pathConnectedSpace f x
    exact isPathConnected_range (componentCoreMap f x).continuous
  | some j =>
    let : PathConnectedSpace (PuncturedChart f x j) := pathConnectedSpace_chart f x j (h j)
    exact isPathConnected_range (chartComponentMap f x j (h j)).continuous

/-- Distinct members of the component cover intersect in the core. -/
theorem componentOpenCover_inf_of_ne (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (i k : Option J) (hik : i ≠ k) :
    componentOpenCover f x h i ⊓ componentOpenCover f x h k =
      componentOpenCover f x h none := by
  cases i with
  | none => exact inf_eq_left.mpr (componentOpenCover_none_le f x h k)
  | some j =>
    cases k with
    | none => exact inf_eq_right.mpr (componentOpenCover_none_le f x h (some j))
    | some k =>
      have hjk : j ≠ k := fun heq => hik (congrArg some heq)
      apply SetLike.ext
      intro p
      change (p ∈ componentOpenCover f x h (some j) ∧
        p ∈ componentOpenCover f x h (some k)) ↔ p ∈ componentOpenCover f x h none
      rw [mem_componentOpenCover_some, mem_componentOpenCover_some,
        mem_componentOpenCover_none]
      exact Set.ext_iff.mp (chartSet_inter_chartSet f x hjk) (p : diskAttachment f)

/-- All pairwise intersections are path connected, including diagonal intersections. -/
theorem isPathConnected_componentOpenCover_inf (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (i k : Option J) :
    IsPathConnected ((componentOpenCover f x h i ⊓ componentOpenCover f x h k) :
      Set ↥(pathComponent (diskAttachmentInclusion f x))) := by
  classical
  by_cases hik : i = k
  · subst k
    rw [inf_idem]
    exact isPathConnected_componentOpenCover f x h i
  · rw [congrFun (congrFun
      (Set.inf_eq_inter (α := ↥(pathComponent (diskAttachmentInclusion f x))))
      (componentOpenCover f x h i)) (componentOpenCover f x h k),
      ← Opens.coe_inf, componentOpenCover_inf_of_ne f x h i k hik]
    exact isPathConnected_componentOpenCover f x h none

/-- The punctured component is homeomorphic to the core member of the cover. -/
noncomputable def componentCoreHomeomorph (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) :
    diskAttachmentPuncturedComponent f x ≃ₜ ↥(componentOpenCover f x h none) :=
  (isEmbedding_componentCoreMap f x).toHomeomorph

@[simp]
theorem componentCoreHomeomorph_coe (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (c : diskAttachmentPuncturedComponent f x) :
    (componentCoreHomeomorph f x h c : ↥(pathComponent (diskAttachmentInclusion f x))) =
      componentCoreMap f x c := by
  exact (isEmbedding_componentCoreMap f x).toHomeomorph_apply_coe c

@[simp]
theorem componentCoreHomeomorph_symm_coe (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (p : ↥(componentOpenCover f x h none)) :
    componentCoreMap f x ((componentCoreHomeomorph f x h).symm p) =
      (p : ↥(pathComponent (diskAttachmentInclusion f x))) := by
  simpa only [componentCoreHomeomorph_coe] using
    congrArg Subtype.val ((componentCoreHomeomorph f x h).apply_symm_apply p)

@[simp]
theorem componentCoreHomeomorph_basepoint (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) :
    componentCoreHomeomorph f x h (diskAttachmentPuncturedComponentInclusion f x
      ⟨x, mem_pathComponent_self x⟩) =
      ⟨componentBasepoint f x, componentBasepoint_mem_componentOpenCover f x h none⟩ := by
  apply Subtype.ext
  rw [componentCoreHomeomorph_coe, componentCoreMap_basepoint]

/-- A thickened chart is homeomorphic to its member of the component cover. -/
noncomputable def componentChartHomeomorph (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j : J) :
    PuncturedChart f x j ≃ₜ ↥(componentOpenCover f x h (some j)) :=
  (isOpenEmbedding_chartComponentMap f x j (h j)).isEmbedding.toHomeomorph

@[simp]
theorem componentChartHomeomorph_coe (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j : J) (p : PuncturedChart f x j) :
    (componentChartHomeomorph f x h j p :
      ↥(pathComponent (diskAttachmentInclusion f x))) =
      chartComponentMap f x j (h j) p := by
  rfl

@[simp]
theorem componentChartHomeomorph_symm_coe (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j : J) (p : ↥(componentOpenCover f x h (some j))) :
    chartComponentMap f x j (h j) ((componentChartHomeomorph f x h j).symm p) =
      (p : ↥(pathComponent (diskAttachmentInclusion f x))) := by
  simpa only [componentChartHomeomorph_coe] using
    congrArg Subtype.val ((componentChartHomeomorph f x h j).apply_symm_apply p)

/-- The chart range homeomorphism preserves the core inclusion. -/
theorem componentChartHomeomorph_chartCore (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j : J) (c : diskAttachmentPuncturedComponent f x) :
    (componentChartHomeomorph f x h j (chartCore f x j c) :
      ↥(pathComponent (diskAttachmentInclusion f x))) = componentCoreMap f x c := by
  rfl

@[simp]
theorem componentChartHomeomorph_basepoint (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j : J) :
    componentChartHomeomorph f x h j (chartCore f x j
      (diskAttachmentPuncturedComponentInclusion f x ⟨x, mem_pathComponent_self x⟩)) =
      ⟨componentBasepoint f x,
        componentBasepoint_mem_componentOpenCover f x h (some j)⟩ := by
  apply Subtype.ext
  exact componentCoreMap_basepoint f x

/-- The range homeomorphisms identify the chart's core map with the inclusion
of the core member into the chart member of the cover. -/
theorem componentChartHomeomorph_comp_chartCore (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j : J) :
    (componentChartHomeomorph f x h j :
      C(PuncturedChart f x j, ↥(componentOpenCover f x h (some j)))).comp
        (chartCore f x j) =
      (ContinuousMap.inclusion (componentOpenCover_none_le f x h (some j))).comp
        (componentCoreHomeomorph f x h :
          C(diskAttachmentPuncturedComponent f x, ↥(componentOpenCover f x h none))) := by
  apply ContinuousMap.ext
  intro c
  apply Subtype.ext
  simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    ContinuousMap.inclusion, ContinuousMap.coe_mk, Set.coe_inclusion] using
    (componentChartHomeomorph_chartCore f x h j c).trans
      (componentCoreHomeomorph_coe f x h c).symm

/-- The component cover, regarded as neighborhoods of its common original-space point. -/
def componentOpenNhds (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x)
    (i : Option J) :
    OpenNhds (X := TopCat.of ↥(pathComponent (diskAttachmentInclusion f x)))
      (componentBasepoint f x) :=
  ⟨componentOpenCover f x h i, componentBasepoint_mem_componentOpenCover f x h i⟩

@[simp]
theorem componentOpenNhds_val (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (i : Option J) :
    (componentOpenNhds f x h i).1 = componentOpenCover f x h i := by
  rfl

/-- Each neighborhood of the cover contains its common core neighborhood. -/
theorem componentOpenNhds_none_le (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j : J) :
    componentOpenNhds f x h none ≤ componentOpenNhds f x h (some j) :=
  componentOpenCover_none_le f x h (some j)

/-- Distinct chart neighborhoods have the core neighborhood as intersection. -/
theorem componentOpenNhds_inf_of_ne (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (j k : J) (hjk : j ≠ k) :
    componentOpenNhds f x h (some j) ⊓ componentOpenNhds f x h (some k) =
      componentOpenNhds f x h none := by
  apply Subtype.ext
  exact componentOpenCover_inf_of_ne f x h (some j) (some k)
    (fun heq => hjk (Option.some.inj heq))

/-- The core and chart neighborhoods give the `Option J` open-cover witness used by
common-overlap fundamental-group gluing. -/
theorem isOpenCover_componentOpenNhds (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) :
    IsOpenCover (fun i : Option J =>
      (i.elim (componentOpenNhds f x h none)
        (fun j => componentOpenNhds f x h (some j))).1) := by
  have heq : (fun i : Option J =>
      (i.elim (componentOpenNhds f x h none)
        (fun j => componentOpenNhds f x h (some j))).1) = componentOpenCover f x h := by
    funext i
    cases i <;> rfl
  rw [heq]
  exact isOpenCover_componentOpenCover f x h

/-- Every neighborhood in the common-core cover is path connected. -/
theorem isPathConnected_componentOpenNhds (f : J → C(Circle, X)) (x : X)
    (h : ∀ j, f j 1 = x) (i : Option J) :
    IsPathConnected ((componentOpenNhds f x h i).1 :
      Set ↥(pathComponent (diskAttachmentInclusion f x))) :=
  isPathConnected_componentOpenCover f x h i

end TopCat.DiskAttachment
