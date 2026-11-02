/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.PuncturedRetraction
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.Connected
public import FundamentalGroupoids.Topology.Path
import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.OpenCoverDescent
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.CategoryTheory.Functor.Const

/-!
# Components of punctured disk attachments

Intersecting the complement of the disk centres with an attachment path component
again gives a path-connected space. The radial retraction and deformation restrict
to this intersection and the corresponding path component of the original space.
No openness or local connectivity of either component is needed.

The component comparison uses functors to the discrete category of components of
the fundamental groupoid of the original space. These functors descend over the
open cover by the punctured attachment and the open characteristic disks; no
topology on the set of component labels is used.
-/

open Topology CategoryTheory TopologicalSpace

universe u v

noncomputable section

namespace TopCat

variable {X : Type u} [TopologicalSpace X] {J : Type v}

private def componentCoverSet (f : J → C(Circle, X)) :
    Option J → Set (diskAttachment f)
  | none => (diskAttachmentCenters f)ᶜ
  | some j => Set.range (diskAttachmentInterior f j)

private theorem componentCoverSet_isOpen (f : J → C(Circle, X)) (a : Option J) :
    IsOpen (componentCoverSet f a) := by
  cases a with
  | none => exact isOpen_diskAttachmentPunctured f
  | some j => exact (isOpenEmbedding_diskAttachmentInterior f j).isOpen_range

private def componentCover (f : J → C(Circle, X)) :
    Option J → Opens (diskAttachment f) :=
  fun a => ⟨componentCoverSet f a, componentCoverSet_isOpen f a⟩

private theorem componentCover_covers (f : J → C(Circle, X)) :
    IsOpenCover (componentCover f) := by
  apply IsOpenCover.of_sets (componentCoverSet_isOpen f)
  ext y
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  classical
  by_cases hy : y ∈ diskAttachmentCenters f
  · rcases hy with ⟨j, rfl⟩
    exact ⟨some j, ⟨⟨0, by simp⟩, (diskAttachmentCenter_eq_interior f j).symm⟩⟩
  · exact ⟨none, hy⟩

private def componentLabels : FundamentalGroupoid X ⥤
    Discrete (CategoryTheory.ConnectedComponents (FundamentalGroupoid X)) :=
  CategoryTheory.ConnectedComponents.functorToDiscrete _ id

private def componentChartLabels (f : J → C(Circle, X)) (a : Option J) :
    FundamentalGroupoid (componentCover f a) ⥤
      Discrete (CategoryTheory.ConnectedComponents (FundamentalGroupoid X)) := by
  cases a with
  | none => exact FundamentalGroupoid.map (diskAttachmentPuncturedRetraction f) ⋙
      componentLabels
  | some j =>
    exact (CategoryTheory.Functor.const
      (FundamentalGroupoid (componentCover f (some j)))).obj
      (Discrete.mk (CategoryTheory.ConnectedComponents.mk (FundamentalGroupoid.mk (f j 1))))

private theorem retraction_label_of_mem_interior (f : J → C(Circle, X))
    (j : J) (w : diskAttachmentPunctured f)
    (hw : (w : diskAttachment f) ∈ Set.range (diskAttachmentInterior f j)) :
    CategoryTheory.ConnectedComponents.mk
        (FundamentalGroupoid.mk (diskAttachmentPuncturedRetraction f w)) =
      CategoryTheory.ConnectedComponents.mk (FundamentalGroupoid.mk (f j 1)) := by
  rcases hw with ⟨z, hz⟩
  have hd : diskAttachmentDisk f j
      ⟨(z : ℂ), Metric.ball_subset_closedBall z.property⟩ = (w : diskAttachment f) :=
    (diskAttachmentInterior_apply f j z).symm.trans hz
  have hn : (z : ℂ) ≠ 0 := by
    intro hzero
    apply w.property
    rw [← hd, diskAttachmentDisk_mem_centers_iff]
    exact hzero
  let q : ↥(Metric.closedBall (0 : ℂ) 1 \ {0}) :=
    ⟨(z : ℂ), Metric.ball_subset_closedBall z.property, hn⟩
  have hq : diskAttachmentPuncturedDisk f j q = w := Subtype.ext hd
  obtain ⟨b, _, hb⟩ := diskAttachmentPuncturedRetraction_disk_exists f j q
  apply (FundamentalGroupoid.connectedComponents_mk_eq_iff_joined X _ _).2
  rw [← hq, hb]
  exact (PathConnectedSpace.joined b 1).map (f j).continuous

private theorem componentChartLabels_compatible (f : J → C(Circle, X)) (a b : Option J) :
    (FundamentalGroupoid.openCoverDiagram (componentCover f)).map
        (Pairwise.Hom.left a b) ⋙ componentChartLabels f a =
      (FundamentalGroupoid.openCoverDiagram (componentCover f)).map
        (Pairwise.Hom.right a b) ⋙ componentChartLabels f b := by
  classical
  refine CategoryTheory.Functor.ext (h_obj := ?_) (h_map := ?_)
  · intro p
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j =>
        change Discrete.mk (CategoryTheory.ConnectedComponents.mk (FundamentalGroupoid.mk
          (diskAttachmentPuncturedRetraction f ⟨p.as.val, p.as.property.1⟩))) =
          Discrete.mk (CategoryTheory.ConnectedComponents.mk (FundamentalGroupoid.mk (f j 1)))
        exact congrArg Discrete.mk
          (retraction_label_of_mem_interior f j _ p.as.property.2)
    | some j =>
      cases b with
      | none =>
        change Discrete.mk
            (CategoryTheory.ConnectedComponents.mk (FundamentalGroupoid.mk (f j 1))) =
          Discrete.mk (CategoryTheory.ConnectedComponents.mk (FundamentalGroupoid.mk
            (diskAttachmentPuncturedRetraction f ⟨p.as.val, p.as.property.2⟩)))
        exact (congrArg Discrete.mk
          (retraction_label_of_mem_interior f j
            (⟨p.as.val, p.as.property.2⟩ : diskAttachmentPunctured f) p.as.property.1)).symm
      | some k =>
        by_cases hjk : j = k
        · subst k
          rfl
        · have hdis := disjoint_range_diskAttachmentInterior f hjk
          exact False.elim ((Set.disjoint_left.mp hdis) p.as.property.1 p.as.property.2)
  · intro p q g
    apply Subsingleton.elim

private def attachmentComponentLabels (f : J → C(Circle, X)) :
    FundamentalGroupoid (diskAttachment f) ⥤
      Discrete (CategoryTheory.ConnectedComponents (FundamentalGroupoid X)) := by
  exact FundamentalGroupoid.descOfIsOpenCover (componentCover_covers f)
    (componentChartLabels f) (componentChartLabels_compatible f)

private theorem attachmentComponentLabels_punctured (f : J → C(Circle, X))
    (w : diskAttachmentPunctured f) :
    ((attachmentComponentLabels f).obj (FundamentalGroupoid.mk (w : diskAttachment f))).as =
      CategoryTheory.ConnectedComponents.mk
        (FundamentalGroupoid.mk (diskAttachmentPuncturedRetraction f w)) := by
  have h := FundamentalGroupoid.descOfIsOpenCover_obj (componentCover_covers f)
    (componentChartLabels f) (componentChartLabels_compatible f) none
    (w : diskAttachment f) w.property
  exact congrArg Discrete.as h

@[expose] public section

/-- The intersection of the punctured attachment with the attachment component
of an original-space point. -/
def diskAttachmentPuncturedComponentSet (f : J → C(Circle, X)) (x : X) :
    Set (diskAttachmentPunctured f) :=
  {w | Joined (diskAttachmentInclusion f x) (w : diskAttachment f)}

/-- Membership is tested in the attachment, not in the punctured subspace. -/
@[simp]
theorem mem_diskAttachmentPuncturedComponentSet (f : J → C(Circle, X)) (x : X)
    (w : diskAttachmentPunctured f) :
    w ∈ diskAttachmentPuncturedComponentSet f x ↔
      Joined (diskAttachmentInclusion f x) (w : diskAttachment f) := by
  rfl

/-- The punctured part of an attachment path component, with the subspace topology. -/
abbrev diskAttachmentPuncturedComponent (f : J → C(Circle, X)) (x : X) :=
  ↥(diskAttachmentPuncturedComponentSet f x)

/-- The radial retraction takes the punctured part of an attachment component
into the corresponding component of the original space. -/
theorem diskAttachmentPuncturedRetraction_mem_pathComponent (f : J → C(Circle, X))
    (x : X) (w : diskAttachmentPuncturedComponent f x) :
    diskAttachmentPuncturedRetraction f w.val ∈ pathComponent x := by
  have h := Discrete.eq_of_hom ((attachmentComponentLabels f).map
    (show FundamentalGroupoid.mk (diskAttachmentInclusion f x) ⟶
        FundamentalGroupoid.mk (w.val : diskAttachment f) from
      Path.Homotopic.Quotient.mk w.property.somePath))
  change ((attachmentComponentLabels f).obj (FundamentalGroupoid.mk
      (diskAttachmentPuncturedInclusion f x : diskAttachment f))).as =
    ((attachmentComponentLabels f).obj
      (FundamentalGroupoid.mk (w.val : diskAttachment f))).as at h
  rw [attachmentComponentLabels_punctured, attachmentComponentLabels_punctured,
    diskAttachmentPuncturedRetraction_inclusion] at h
  exact (FundamentalGroupoid.connectedComponents_mk_eq_iff_joined X _ _).1 h

/-- Set-theoretic form of the component restriction of the radial retraction. -/
theorem diskAttachmentPuncturedRetraction_mapsTo_component (f : J → C(Circle, X))
    (x : X) : Set.MapsTo (diskAttachmentPuncturedRetraction f)
      (diskAttachmentPuncturedComponentSet f x) (pathComponent x) := by
  intro w hw
  exact diskAttachmentPuncturedRetraction_mem_pathComponent f x ⟨w, hw⟩

/-- Inclusion of the original-space component into the punctured attachment component. -/
def diskAttachmentPuncturedComponentInclusion (f : J → C(Circle, X)) (x : X) :
    C(↥(pathComponent x), diskAttachmentPuncturedComponent f x) := by
  exact ⟨fun a => ⟨diskAttachmentPuncturedInclusion f a.val,
      a.property.map (diskAttachmentInclusion f).continuous⟩,
    ((diskAttachmentPuncturedInclusion f).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The component inclusion is the original punctured inclusion on underlying points. -/
@[simp]
theorem diskAttachmentPuncturedComponentInclusion_coe (f : J → C(Circle, X)) (x : X)
    (a : ↥(pathComponent x)) :
    (diskAttachmentPuncturedComponentInclusion f x a : diskAttachmentPunctured f) =
      diskAttachmentPuncturedInclusion f a.val := by
  rfl

/-- Forgetting the component after inclusion agrees with inclusion after forgetting. -/
theorem diskAttachmentPuncturedComponentInclusion_comp_subtypeVal
    (f : J → C(Circle, X)) (x : X) :
    (ContinuousMap.subtypeVal (diskAttachmentPuncturedComponentSet f x)).comp
        (diskAttachmentPuncturedComponentInclusion f x) =
      (diskAttachmentPuncturedInclusion f).comp
        (ContinuousMap.subtypeVal (pathComponent x)) := by
  rfl

/-- The radial retraction restricted to the corresponding components. -/
def diskAttachmentPuncturedComponentRetraction (f : J → C(Circle, X)) (x : X) :
    C(diskAttachmentPuncturedComponent f x, ↥(pathComponent x)) := by
  exact ⟨fun w => ⟨diskAttachmentPuncturedRetraction f w.val,
      diskAttachmentPuncturedRetraction_mem_pathComponent f x w⟩,
    ((diskAttachmentPuncturedRetraction f).continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The restricted retraction has the same underlying original-space point. -/
@[simp]
theorem diskAttachmentPuncturedComponentRetraction_coe (f : J → C(Circle, X)) (x : X)
    (w : diskAttachmentPuncturedComponent f x) :
    (diskAttachmentPuncturedComponentRetraction f x w : X) =
      diskAttachmentPuncturedRetraction f w.val := by
  rfl

/-- Forgetting the component after retraction agrees with retraction after forgetting. -/
theorem diskAttachmentPuncturedComponentRetraction_comp_subtypeVal
    (f : J → C(Circle, X)) (x : X) :
    (ContinuousMap.subtypeVal (pathComponent x)).comp
        (diskAttachmentPuncturedComponentRetraction f x) =
      (diskAttachmentPuncturedRetraction f).comp
        (ContinuousMap.subtypeVal (diskAttachmentPuncturedComponentSet f x)) := by
  rfl

/-- Retraction after inclusion is the identity on the original-space component. -/
@[simp]
theorem diskAttachmentPuncturedComponentRetraction_comp_inclusion
    (f : J → C(Circle, X)) (x : X) :
    (diskAttachmentPuncturedComponentRetraction f x).comp
        (diskAttachmentPuncturedComponentInclusion f x) =
      ContinuousMap.id ↥(pathComponent x) := by
  apply ContinuousMap.ext
  intro a
  apply Subtype.ext
  exact diskAttachmentPuncturedRetraction_inclusion f a.val

/-- The common basepoint in the punctured part of its ambient attachment component. -/
def diskAttachmentPuncturedComponentBasepoint (f : J → C(Circle, X)) (x : X) :
    diskAttachmentPuncturedComponent f x := by
  exact ⟨diskAttachmentPuncturedInclusion f x, Joined.refl _⟩

/-- Forgetting the component recovers the punctured inclusion of the basepoint. -/
@[simp]
theorem diskAttachmentPuncturedComponentBasepoint_coe
    (f : J → C(Circle, X)) (x : X) :
    (diskAttachmentPuncturedComponentBasepoint f x : diskAttachmentPunctured f) =
      diskAttachmentPuncturedInclusion f x := by
  rfl

/-- Retraction sends the common basepoint to the basepoint of the original component. -/
@[simp]
theorem diskAttachmentPuncturedComponentRetraction_basepoint
    (f : J → C(Circle, X)) (x : X) :
    diskAttachmentPuncturedComponentRetraction f x
        (diskAttachmentPuncturedComponentBasepoint f x) =
      (⟨x, Joined.refl x⟩ : ↥(pathComponent x)) := by
  apply Subtype.ext
  rw [diskAttachmentPuncturedComponentRetraction_coe,
    diskAttachmentPuncturedComponentBasepoint_coe,
    diskAttachmentPuncturedRetraction_inclusion]

/-- On underlying original-space points, the restricted retraction preserves the basepoint. -/
theorem diskAttachmentPuncturedComponentRetraction_basepoint_coe
    (f : J → C(Circle, X)) (x : X) :
    (diskAttachmentPuncturedComponentRetraction f x
      (diskAttachmentPuncturedComponentBasepoint f x) : X) = x := by
  calc
    (diskAttachmentPuncturedComponentRetraction f x
        (diskAttachmentPuncturedComponentBasepoint f x) : X) =
        diskAttachmentPuncturedRetraction f
          (diskAttachmentPuncturedComponentBasepoint f x : diskAttachmentPunctured f) :=
      congrArg
        (fun g : C(diskAttachmentPuncturedComponent f x, X) =>
          g (diskAttachmentPuncturedComponentBasepoint f x))
        (diskAttachmentPuncturedComponentRetraction_comp_subtypeVal f x)
    _ = x := by
      rw [diskAttachmentPuncturedComponentBasepoint_coe,
        diskAttachmentPuncturedRetraction_inclusion]

/-- Every point of the original-space component supplies a point of the punctured component. -/
theorem diskAttachmentPuncturedComponent_nonempty (f : J → C(Circle, X)) (x : X) :
    Nonempty (diskAttachmentPuncturedComponent f x) := by
  exact ⟨diskAttachmentPuncturedComponentInclusion f x ⟨x, mem_pathComponent_self x⟩⟩

/-- The radial tracks stay in the attachment component of their initial point. -/
theorem diskAttachmentPuncturedDeformation_mem_component (f : J → C(Circle, X))
    (x : X) (t : unitInterval) (w : diskAttachmentPuncturedComponent f x) :
    diskAttachmentPuncturedDeformation f (t, w.val) ∈
      diskAttachmentPuncturedComponentSet f x := by
  have htrack : Joined w.val (diskAttachmentPuncturedDeformation f (t, w.val)) := by
    let p := (diskAttachmentPuncturedDeformation f).toHomotopy.evalAt w.val
    exact ⟨(p.truncateOfLE t.property.1).cast
      p.extend_zero.symm (p.extend_extends' t).symm⟩
  exact w.property.trans (htrack.map continuous_subtype_val)

/-- The radial deformation restricted to a punctured attachment component,
relative to the included original-space component. -/
def diskAttachmentPuncturedComponentDeformation (f : J → C(Circle, X)) (x : X) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id (diskAttachmentPuncturedComponent f x))
      ((diskAttachmentPuncturedComponentInclusion f x).comp
        (diskAttachmentPuncturedComponentRetraction f x))
      (Set.range (diskAttachmentPuncturedComponentInclusion f x)) := by
  refine
    { toFun := fun p => ⟨diskAttachmentPuncturedDeformation f (p.1, p.2.val),
        diskAttachmentPuncturedDeformation_mem_component f x p.1 p.2⟩
      continuous_toFun :=
        ((diskAttachmentPuncturedDeformation f).toHomotopy.toContinuousMap.continuous.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro w
    exact Subtype.ext (diskAttachmentPuncturedDeformation_zero f w.val)
  · intro w
    exact Subtype.ext (diskAttachmentPuncturedDeformation_one f w.val)
  · intro t w hw
    rcases hw with ⟨a, rfl⟩
    exact Subtype.ext (diskAttachmentPuncturedDeformation_inclusion f t a.val)

/-- The restricted deformation is the radial deformation with its component membership. -/
theorem diskAttachmentPuncturedComponentDeformation_apply (f : J → C(Circle, X)) (x : X)
    (t : unitInterval) (w : diskAttachmentPuncturedComponent f x) :
    diskAttachmentPuncturedComponentDeformation f x (t, w) =
      ⟨diskAttachmentPuncturedDeformation f (t, w.val),
        diskAttachmentPuncturedDeformation_mem_component f x t w⟩ := by
  rfl

/-- Forgetting the component restriction recovers the radial deformation. -/
@[simp]
theorem diskAttachmentPuncturedComponentDeformation_coe (f : J → C(Circle, X)) (x : X)
    (t : unitInterval) (w : diskAttachmentPuncturedComponent f x) :
    (diskAttachmentPuncturedComponentDeformation f x (t, w) : diskAttachmentPunctured f) =
      diskAttachmentPuncturedDeformation f (t, w.val) := by
  rfl

/-- The component deformation starts at the identity. -/
theorem diskAttachmentPuncturedComponentDeformation_zero (f : J → C(Circle, X)) (x : X)
    (w : diskAttachmentPuncturedComponent f x) :
    diskAttachmentPuncturedComponentDeformation f x (0, w) = w := by
  exact (diskAttachmentPuncturedComponentDeformation f x).toHomotopy.map_zero_left w

/-- The component deformation ends at inclusion after retraction. -/
theorem diskAttachmentPuncturedComponentDeformation_one (f : J → C(Circle, X)) (x : X)
    (w : diskAttachmentPuncturedComponent f x) :
    diskAttachmentPuncturedComponentDeformation f x (1, w) =
      diskAttachmentPuncturedComponentInclusion f x
        (diskAttachmentPuncturedComponentRetraction f x w) := by
  exact (diskAttachmentPuncturedComponentDeformation f x).toHomotopy.map_one_left w

/-- The component deformation fixes every included original-space component point. -/
@[simp]
theorem diskAttachmentPuncturedComponentDeformation_inclusion
    (f : J → C(Circle, X)) (x : X) (t : unitInterval) (a : ↥(pathComponent x)) :
    diskAttachmentPuncturedComponentDeformation f x
        (t, diskAttachmentPuncturedComponentInclusion f x a) =
      diskAttachmentPuncturedComponentInclusion f x a := by
  exact (diskAttachmentPuncturedComponentDeformation f x).prop' t _ ⟨a, rfl⟩

/-- The component deformation fixes the entire included range pointwise. -/
theorem diskAttachmentPuncturedComponentDeformation_fixed
    (f : J → C(Circle, X)) (x : X) (t : unitInterval)
    (w : diskAttachmentPuncturedComponent f x)
    (hw : w ∈ Set.range (diskAttachmentPuncturedComponentInclusion f x)) :
    diskAttachmentPuncturedComponentDeformation f x (t, w) = w := by
  exact (diskAttachmentPuncturedComponentDeformation f x).prop' t w hw

/-- The punctured part of an attachment component is path connected.
This is a theorem, not a global instance. -/
theorem diskAttachmentPuncturedComponent_pathConnectedSpace
    (f : J → C(Circle, X)) (x : X) :
    PathConnectedSpace (diskAttachmentPuncturedComponent f x) := by
  refine ⟨diskAttachmentPuncturedComponent_nonempty f x, ?_⟩
  intro a b
  have hX : PathConnectedSpace ↥(pathComponent x) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent
  have ha : Joined a (diskAttachmentPuncturedComponentInclusion f x
      (diskAttachmentPuncturedComponentRetraction f x a)) :=
    ⟨(diskAttachmentPuncturedComponentDeformation f x).toHomotopy.evalAt a⟩
  have hb : Joined b (diskAttachmentPuncturedComponentInclusion f x
      (diskAttachmentPuncturedComponentRetraction f x b)) :=
    ⟨(diskAttachmentPuncturedComponentDeformation f x).toHomotopy.evalAt b⟩
  exact ha.trans (((hX.joined _ _).map
    (diskAttachmentPuncturedComponentInclusion f x).continuous).trans hb.symm)

/-- The attachment-component intersection agrees with the punctured-space path
component, as a consequence of the restricted deformation. -/
theorem diskAttachmentPuncturedComponentSet_eq_pathComponent
    (f : J → C(Circle, X)) (x : X) :
    diskAttachmentPuncturedComponentSet f x =
      pathComponent (diskAttachmentPuncturedInclusion f x) := by
  ext w
  constructor
  · intro hw
    have h := (diskAttachmentPuncturedComponent_pathConnectedSpace f x).joined
      (diskAttachmentPuncturedComponentInclusion f x ⟨x, mem_pathComponent_self x⟩)
      ⟨w, hw⟩
    exact h.map continuous_subtype_val
  · intro hw
    exact hw.map continuous_subtype_val

/-- With no disks, inclusion after retraction is also the identity on the component. -/
@[simp]
theorem diskAttachmentPuncturedComponentInclusion_comp_retraction_of_isEmpty
    (f : J → C(Circle, X)) [IsEmpty J] (x : X) :
    (diskAttachmentPuncturedComponentInclusion f x).comp
        (diskAttachmentPuncturedComponentRetraction f x) =
      ContinuousMap.id (diskAttachmentPuncturedComponent f x) := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  change diskAttachmentPuncturedInclusion f (diskAttachmentPuncturedRetraction f w.val) = w.val
  refine diskAttachmentPunctured_induction f
    (P := fun a => diskAttachmentPuncturedInclusion f
      (diskAttachmentPuncturedRetraction f a) = a) ?_ ?_ w.val
  · intro a
    rw [diskAttachmentPuncturedRetraction_inclusion]
  · intro j
    exact isEmptyElim j

/-- In an empty disk family, the punctured attachment component is canonically
homeomorphic to the original-space component, without an openness assumption. -/
def diskAttachmentPuncturedComponentEmptyHomeomorph
    (f : J → C(Circle, X)) [IsEmpty J] (x : X) :
    diskAttachmentPuncturedComponent f x ≃ₜ ↥(pathComponent x) := by
  exact
    { toFun := diskAttachmentPuncturedComponentRetraction f x
      invFun := diskAttachmentPuncturedComponentInclusion f x
      left_inv := fun w => DFunLike.congr_fun
        (diskAttachmentPuncturedComponentInclusion_comp_retraction_of_isEmpty f x) w
      right_inv := fun a => DFunLike.congr_fun
        (diskAttachmentPuncturedComponentRetraction_comp_inclusion f x) a
      continuous_toFun := (diskAttachmentPuncturedComponentRetraction f x).continuous
      continuous_invFun := (diskAttachmentPuncturedComponentInclusion f x).continuous }

/-- The empty-family component homeomorphism is the restricted radial retraction. -/
@[simp]
theorem diskAttachmentPuncturedComponentEmptyHomeomorph_apply
    (f : J → C(Circle, X)) [IsEmpty J] (x : X)
    (w : diskAttachmentPuncturedComponent f x) :
    diskAttachmentPuncturedComponentEmptyHomeomorph f x w =
      diskAttachmentPuncturedComponentRetraction f x w := by
  rfl

/-- The inverse empty-family homeomorphism is the restricted inclusion. -/
@[simp]
theorem diskAttachmentPuncturedComponentEmptyHomeomorph_symm_apply
    (f : J → C(Circle, X)) [IsEmpty J] (x : X) (a : ↥(pathComponent x)) :
    (diskAttachmentPuncturedComponentEmptyHomeomorph f x).symm a =
      diskAttachmentPuncturedComponentInclusion f x a := by
  rfl

end

end TopCat
