/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Attaching a family of disks

`TopCat.diskAttachment f` attaches one closed complex unit disk along each map
in a family `f : ∀ j, C(Circle, X)`. The construction uses the quotient pushout
in types and its final topology in `TopCat`. The maps from `X` and from each
disk have their original domains, without universe lifts in the public API.

`TopCat.diskAttachmentDesc` and `TopCat.continuous_diskAttachment_iff` express
the universal property with a target in an independent universe. Continuity on
an open or closed subset can likewise be tested on the original space and each disk.
Empty families recover `X`, and attaching a single disk along the identity of its boundary
recovers the closed disk, with the indicated original inclusion maps.

The original-space inclusion is a closed embedding. Each characteristic map
restricts to an open embedding on the open unit disk; these images are mutually
disjoint and avoid the original space. The full closed-disk characteristic maps
need not be embeddings.

No connectedness or separation assumptions on `X` are required.
-/

open CategoryTheory CategoryTheory.Limits Topology

universe u v w

noncomputable section

namespace TopCat

public section

/-- The boundary inclusion of the complex unit circle into the closed unit disk. -/
def diskBoundary : C(Circle, ↥(Metric.closedBall (0 : ℂ) 1)) :=
  ContinuousMap.inclusion Metric.sphere_subset_closedBall

/-- The boundary inclusion preserves the underlying complex point. -/
@[simp]
theorem diskBoundary_coe (z : Circle) : (diskBoundary z : ℂ) = z := by
  rfl

/-- The circle is a closed subspace of the closed unit disk. -/
theorem isClosedEmbedding_diskBoundary : IsClosedEmbedding diskBoundary := by
  exact IsClosedEmbedding.inclusion Metric.sphere_subset_closedBall
    (Metric.isClosed_sphere.preimage continuous_subtype_val)

end

local notation "D" => {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) 1}

variable {X : Type u} [TopologicalSpace X] {J : Type v}

private def attachingMap (f : J → C(Circle, X)) :
    of (Σ _ : J, ULift.{u} Circle) ⟶ of (ULift.{v} X) :=
  ofHom ⟨fun p => ULift.up (f p.1 p.2.down), continuous_sigma fun j =>
    (Homeomorph.ulift.symm.continuous).comp
      ((f j).continuous.comp Homeomorph.ulift.continuous)⟩

private def boundaryMap :
    of (Σ _ : J, ULift.{u} Circle) ⟶ of (Σ _ : J, ULift.{u} D) :=
  ofHom ⟨fun p => ⟨p.1, ULift.up (diskBoundary p.2.down)⟩,
    continuous_sigma fun _ => continuous_sigmaMk.comp
      (Homeomorph.ulift.symm.continuous.comp
        (diskBoundary.continuous.comp Homeomorph.ulift.continuous))⟩

private def quotientCocone (f : J → C(Circle, X)) :
    Cocone (span (attachingMap f) (boundaryMap (J := J)) ⋙ forget TopCat) :=
  (Cocone.precompose
    (spanCompIso (forget TopCat) (attachingMap f) (boundaryMap (J := J))).hom).obj
    (Types.Pushout.cocone ((forget TopCat).map (attachingMap f))
      ((forget TopCat).map (boundaryMap (J := J))))

private def quotientCoconeIsColimit (f : J → C(Circle, X)) :
    IsColimit (quotientCocone f) :=
  (IsColimit.precomposeHomEquiv
    (spanCompIso (forget TopCat) (attachingMap f) (boundaryMap (J := J)))
    (Types.Pushout.cocone ((forget TopCat).map (attachingMap f))
      ((forget TopCat).map (boundaryMap (J := J))))).symm
    (Types.Pushout.isColimitCocone _ _)

private def attachmentCocone (f : J → C(Circle, X)) :
    PushoutCocone (attachingMap f) (boundaryMap (J := J)) :=
  coconeOfCoconeForget (quotientCocone f)

private def attachmentIsColimit (f : J → C(Circle, X)) :
    IsColimit (attachmentCocone f) :=
  isColimitCoconeOfForget (quotientCocone f) (quotientCoconeIsColimit f)

public section

/-- Attach a closed unit disk along each member of a family of circle maps.
The carrier is the pushout quotient and the topology is the final topology of
its two legs. The index and original-space universes are independent. -/
def diskAttachment (f : J → C(Circle, X)) : TopCat.{max u v} :=
  (attachmentCocone f).pt

/-- The original-space inclusion into a disk attachment. -/
def diskAttachmentInclusion (f : J → C(Circle, X)) : C(X, diskAttachment f) :=
  (attachmentCocone f).inl.hom.comp
    ⟨ULift.up, Homeomorph.ulift.symm.continuous⟩

/-- The characteristic map of one attached closed disk. -/
def diskAttachmentDisk (f : J → C(Circle, X)) (j : J) : C(D, diskAttachment f) :=
  (attachmentCocone f).inr.hom.comp
    ⟨fun z => ⟨j, ULift.up z⟩,
      continuous_sigmaMk.comp Homeomorph.ulift.symm.continuous⟩

/-- The attaching square, evaluated on the original circle. -/
@[simp]
theorem diskAttachmentDisk_boundary (f : J → C(Circle, X)) (j : J) (z : Circle) :
    diskAttachmentDisk f j (diskBoundary z) = diskAttachmentInclusion f (f j z) := by
  exact (ConcreteCategory.congr_hom (attachmentCocone f).condition
    ⟨j, ULift.up z⟩).symm

/-- The attaching square as an equality of continuous maps on the original circle. -/
theorem diskAttachment_boundary (f : J → C(Circle, X)) (j : J) :
    (diskAttachmentDisk f j).comp diskBoundary = (diskAttachmentInclusion f).comp (f j) := by
  ext z
  exact diskAttachmentDisk_boundary f j z

/-- The characteristic map restricted to the open unit disk. -/
def diskAttachmentInterior (f : J → C(Circle, X)) (j : J) :
    C(↥(Metric.ball (0 : ℂ) 1), diskAttachment f) :=
  (diskAttachmentDisk f j).comp (ContinuousMap.inclusion Metric.ball_subset_closedBall)

/-- The open-disk characteristic map is the closed-disk map on the same point. -/
@[simp]
theorem diskAttachmentInterior_apply (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1)) :
    diskAttachmentInterior f j z =
      diskAttachmentDisk f j ⟨(z : ℂ), Metric.ball_subset_closedBall z.property⟩ := by
  rfl

/-- Functions on an attachment are determined by their restrictions to the original
space and to every attached disk. No continuity or target-universe restriction is needed. -/
theorem diskAttachment_ext {Z : Type w} (f : J → C(Circle, X))
    {a b : diskAttachment f → Z}
    (hX : ∀ x, a (diskAttachmentInclusion f x) = b (diskAttachmentInclusion f x))
    (hD : ∀ j z, a (diskAttachmentDisk f j z) = b (diskAttachmentDisk f j z)) : a = b := by
  funext p
  refine Quot.inductionOn p ?_
  rintro (x | ⟨j, z⟩)
  · exact hX x.down
  · exact hD j z.down

/-- A predicate on a disk attachment holds everywhere if it holds on the original
space and on every attached disk. -/
theorem diskAttachment_induction (f : J → C(Circle, X)) {P : diskAttachment f → Prop}
    (hX : ∀ x, P (diskAttachmentInclusion f x))
    (hD : ∀ j z, P (diskAttachmentDisk f j z)) (p : diskAttachment f) : P p := by
  have h : P = fun _ => True := diskAttachment_ext f
    (fun x => propext ⟨fun _ => True.intro, fun _ => hX x⟩)
    (fun j z => propext ⟨fun _ => True.intro, fun _ => hD j z⟩)
  exact Eq.mpr (congrFun h p) True.intro

/-- Continuity out of an attachment is equivalent to continuity on its original
space and on every disk, for a target in an independent universe. -/
theorem continuous_diskAttachment_iff {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (a : diskAttachment f → Z) :
    Continuous a ↔ Continuous (a ∘ diskAttachmentInclusion f) ∧
      ∀ j, Continuous (a ∘ diskAttachmentDisk f j) := by
  constructor
  · intro ha
    exact ⟨ha.comp (diskAttachmentInclusion f).continuous,
      fun j => ha.comp (diskAttachmentDisk f j).continuous⟩
  · rintro ⟨hX, hD⟩
    apply (continuous_iff_of_isColimit (attachmentCocone f) (attachmentIsColimit f) a).2
    intro k
    cases k with
    | none =>
      change Continuous (fun p : Σ _ : J, ULift.{u} Circle =>
        a (diskAttachmentInclusion f (f p.1 p.2.down)))
      exact continuous_sigma fun j =>
        hX.comp ((f j).continuous.comp Homeomorph.ulift.continuous)
    | some k =>
      cases k with
      | left =>
        change Continuous (fun x : ULift.{v} X => a (diskAttachmentInclusion f x.down))
        exact hX.comp Homeomorph.ulift.continuous
      | right =>
        change Continuous (fun p : Σ _ : J, ULift.{u} D =>
          a (diskAttachmentDisk f p.1 p.2.down))
        exact continuous_sigma fun j => (hD j).comp Homeomorph.ulift.continuous

/-- A subset of a disk attachment is open exactly when its preimages in the original
space and in every attached disk are open. -/
theorem isOpen_diskAttachment_iff (f : J → C(Circle, X)) (S : Set (diskAttachment f)) :
    IsOpen S ↔ IsOpen (diskAttachmentInclusion f ⁻¹' S) ∧
      ∀ j, IsOpen (diskAttachmentDisk f j ⁻¹' S) := by
  constructor
  · intro hS
    exact ⟨hS.preimage (diskAttachmentInclusion f).continuous,
      fun j => hS.preimage (diskAttachmentDisk f j).continuous⟩
  · rintro ⟨hX, hD⟩
    apply (isOpen_iff_of_isColimit (attachmentCocone f) (attachmentIsColimit f) S).2
    intro k
    cases k with
    | none =>
      change IsOpen ((fun p : Σ _ : J, ULift.{u} Circle =>
        diskAttachmentInclusion f (f p.1 p.2.down)) ⁻¹' S)
      apply isOpen_sigma_iff.2
      intro j
      exact hX.preimage ((f j).continuous.comp Homeomorph.ulift.continuous)
    | some k =>
      cases k with
      | left =>
        change IsOpen ((fun x : ULift.{v} X => diskAttachmentInclusion f x.down) ⁻¹' S)
        exact hX.preimage Homeomorph.ulift.continuous
      | right =>
        change IsOpen ((fun p : Σ _ : J, ULift.{u} D =>
          diskAttachmentDisk f p.1 p.2.down) ⁻¹' S)
        apply isOpen_sigma_iff.2
        intro j
        exact (hD j).preimage Homeomorph.ulift.continuous

/-- A subset of a disk attachment is closed exactly when its preimages in the original
space and in every attached disk are closed. -/
theorem isClosed_diskAttachment_iff (f : J → C(Circle, X)) (S : Set (diskAttachment f)) :
    IsClosed S ↔ IsClosed (diskAttachmentInclusion f ⁻¹' S) ∧
      ∀ j, IsClosed (diskAttachmentDisk f j ⁻¹' S) := by
  simpa only [Set.preimage_compl, isOpen_compl_iff] using
    (isOpen_diskAttachment_iff f Sᶜ)

/-- Continuity on an open subset of a disk attachment is equivalent to continuity
on its preimages in the original space and every attached disk. The target universe
is independent, and no continuity outside the subset is required. -/
theorem continuousOn_diskAttachment_iff_of_isOpen {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : diskAttachment f → Z) {S : Set (diskAttachment f)}
    (hS : IsOpen S) :
    ContinuousOn g S ↔ ContinuousOn (g ∘ diskAttachmentInclusion f)
      (diskAttachmentInclusion f ⁻¹' S) ∧
      ∀ j, ContinuousOn (g ∘ diskAttachmentDisk f j) (diskAttachmentDisk f j ⁻¹' S) := by
  constructor
  · intro hg
    exact ⟨hg.comp (diskAttachmentInclusion f).continuous.continuousOn (fun _ hx => hx),
      fun j => hg.comp (diskAttachmentDisk f j).continuous.continuousOn (fun _ hx => hx)⟩
  · rintro ⟨hX, hD⟩
    apply (continuousOn_open_iff hS).2
    intro V hV
    apply (isOpen_diskAttachment_iff f (S ∩ g ⁻¹' V)).2
    constructor
    · simpa only [Set.preimage_inter, Set.preimage_comp] using
        hX.isOpen_inter_preimage
          (hS.preimage (diskAttachmentInclusion f).continuous) hV
    · intro j
      simpa only [Set.preimage_inter, Set.preimage_comp] using
        (hD j).isOpen_inter_preimage
          (hS.preimage (diskAttachmentDisk f j).continuous) hV

/-- Continuity on a closed subset of a disk attachment is equivalent to continuity
on its preimages in the original space and every attached disk. The target universe
is independent, and no continuity outside the subset is required. -/
theorem continuousOn_diskAttachment_iff_of_isClosed {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : diskAttachment f → Z) {S : Set (diskAttachment f)}
    (hS : IsClosed S) :
    ContinuousOn g S ↔ ContinuousOn (g ∘ diskAttachmentInclusion f)
      (diskAttachmentInclusion f ⁻¹' S) ∧
      ∀ j, ContinuousOn (g ∘ diskAttachmentDisk f j) (diskAttachmentDisk f j ⁻¹' S) := by
  constructor
  · intro hg
    exact ⟨hg.comp (diskAttachmentInclusion f).continuous.continuousOn (fun _ hx => hx),
      fun j => hg.comp (diskAttachmentDisk f j).continuous.continuousOn (fun _ hx => hx)⟩
  · rintro ⟨hX, hD⟩
    apply continuousOn_iff_isClosed.2
    intro V hV
    refine ⟨g ⁻¹' V ∩ S, ?_, ?_⟩
    · rw [Set.inter_comm]
      apply (isClosed_diskAttachment_iff f (S ∩ g ⁻¹' V)).2
      constructor
      · simpa only [Set.preimage_inter, Set.preimage_comp] using
          hX.preimage_isClosed_of_isClosed
            (hS.preimage (diskAttachmentInclusion f).continuous) hV
      · intro j
        simpa only [Set.preimage_inter, Set.preimage_comp] using
          (hD j).preimage_isClosed_of_isClosed
            (hS.preimage (diskAttachmentDisk f j).continuous) hV
    · rw [Set.inter_assoc, Set.inter_self]

end

private def attachmentDescFun {Z : Type w} (f : J → C(Circle, X))
    (g : X → Z) (d : J → D → Z)
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) : diskAttachment f → Z :=
  Quot.lift (Sum.elim (fun x : ULift.{v} X => g x.down)
    (fun p : Σ _ : J, ULift.{u} D => d p.1 p.2.down)) (by
      rintro _ _ ⟨p⟩
      exact (h p.1 p.2.down).symm)

private theorem attachmentDescFun_inclusion {Z : Type w} (f : J → C(Circle, X))
    (g : X → Z) (d : J → D → Z)
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) (x : X) :
    attachmentDescFun f g d h (diskAttachmentInclusion f x) = g x := by
  rfl

private theorem attachmentDescFun_disk {Z : Type w} (f : J → C(Circle, X))
    (g : X → Z) (d : J → D → Z)
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) (j : J) (z : D) :
    attachmentDescFun f g d h (diskAttachmentDisk f j z) = d j z := by
  rfl

public section

/-- Descent of coherent continuous maps from the original space and the disks.
The target universe is independent of both source and index universes. -/
def diskAttachmentDesc {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z)) (d : J → C(D, Z))
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) : C(diskAttachment f, Z) where
  toFun := attachmentDescFun f g (fun j => d j) h
  continuous_toFun := (continuous_diskAttachment_iff f _).2 ⟨g.continuous,
    fun j => (d j).continuous⟩

/-- Descent computes to the supplied map on the original space. -/
@[simp]
theorem diskAttachmentDesc_inclusion {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z)) (d : J → C(D, Z))
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) (x : X) :
    diskAttachmentDesc f g d h (diskAttachmentInclusion f x) = g x := by
  rfl

/-- Descent computes to the supplied map on each disk. -/
@[simp]
theorem diskAttachmentDesc_disk {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z)) (d : J → C(D, Z))
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) (j : J) (z : D) :
    diskAttachmentDesc f g d h (diskAttachmentDisk f j z) = d j z := by
  rfl

/-- Descent restricts to the supplied continuous map on the original space. -/
@[simp]
theorem diskAttachmentDesc_comp_inclusion {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z)) (d : J → C(D, Z))
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) :
    (diskAttachmentDesc f g d h).comp (diskAttachmentInclusion f) = g := by
  ext x
  exact diskAttachmentDesc_inclusion f g d h x

/-- Descent restricts to the supplied continuous map on each disk. -/
@[simp]
theorem diskAttachmentDesc_comp_disk {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z)) (d : J → C(D, Z))
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) (j : J) :
    (diskAttachmentDesc f g d h).comp (diskAttachmentDisk f j) = d j := by
  ext z
  exact diskAttachmentDesc_disk f g d h j z

/-- Continuous maps out of an attachment are determined by their restrictions. -/
@[ext]
theorem diskAttachment_hom_ext {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) {a b : C(diskAttachment f, Z)}
    (hX : a.comp (diskAttachmentInclusion f) = b.comp (diskAttachmentInclusion f))
    (hD : ∀ j, a.comp (diskAttachmentDisk f j) = b.comp (diskAttachmentDisk f j)) : a = b := by
  apply ContinuousMap.ext
  exact congrFun (diskAttachment_ext f
    (fun x => DFunLike.congr_fun hX x) (fun j z => DFunLike.congr_fun (hD j) z))

/-- The descended continuous map is the unique map with the prescribed restrictions. -/
theorem diskAttachmentDesc_unique {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z)) (d : J → C(D, Z))
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) (a : C(diskAttachment f, Z))
    (hX : a.comp (diskAttachmentInclusion f) = g)
    (hD : ∀ j, a.comp (diskAttachmentDisk f j) = d j) :
    a = diskAttachmentDesc f g d h := by
  apply diskAttachment_hom_ext f
  · ext x
    exact (DFunLike.congr_fun hX x).trans (diskAttachmentDesc_inclusion f g d h x).symm
  · intro j
    ext z
    exact (DFunLike.congr_fun (hD j) z).trans (diskAttachmentDesc_disk f g d h j z).symm

/-- The continuous-map universal property of a disk attachment, with an
independently universe-polymorphic target. -/
theorem diskAttachment_existsUnique {Z : Type w} [TopologicalSpace Z]
    (f : J → C(Circle, X)) (g : C(X, Z)) (d : J → C(D, Z))
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) :
    ∃! a : C(diskAttachment f, Z),
      a.comp (diskAttachmentInclusion f) = g ∧ ∀ j, a.comp (diskAttachmentDisk f j) = d j := by
  refine ⟨diskAttachmentDesc f g d h,
    ⟨diskAttachmentDesc_comp_inclusion f g d h, diskAttachmentDesc_comp_disk f g d h⟩, ?_⟩
  intro a ha
  exact diskAttachmentDesc_unique f g d h a ha.1 ha.2

end

-- Boundary labels use preimages under the boundary inclusion, rather than
-- identifying the circle's membership predicate with a metric-sphere predicate.
private def attachmentDiskLabel (f : J → C(Circle, X)) (j : J) (z : D) :
    X ⊕ (Σ _ : J, D) := by
  classical
  exact if hz : z ∈ Set.range diskBoundary then
    Sum.inl (f j (Classical.choose hz)) else Sum.inr (⟨j, z⟩ : Σ _ : J, D)

private theorem attachmentDiskLabel_boundary (f : J → C(Circle, X))
    (j : J) (b : Circle) :
    attachmentDiskLabel f j (diskBoundary b) = Sum.inl (f j b) := by
  classical
  have hb : diskBoundary b ∈ Set.range diskBoundary := ⟨b, rfl⟩
  rw [attachmentDiskLabel, dite_eq_left hb]
  exact congrArg (fun c : Circle => (Sum.inl (f j c) : X ⊕ (Σ _ : J, D)))
    (isClosedEmbedding_diskBoundary.injective (Classical.choose_spec hb))

-- This set-theoretic label distinguishes original points and disk interiors.
-- Boundary points receive their attaching-map value; no continuity is asserted.
private def attachmentLabel (f : J → C(Circle, X)) :
    diskAttachment f → X ⊕ (Σ _ : J, D) :=
  attachmentDescFun f Sum.inl (attachmentDiskLabel f) (attachmentDiskLabel_boundary f)

private theorem attachmentLabel_inclusion (f : J → C(Circle, X)) (x : X) :
    attachmentLabel f (diskAttachmentInclusion f x) = Sum.inl x := by
  exact attachmentDescFun_inclusion f Sum.inl (attachmentDiskLabel f)
    (attachmentDiskLabel_boundary f) x

private theorem attachmentLabel_disk (f : J → C(Circle, X)) (j : J) (z : D) :
    attachmentLabel f (diskAttachmentDisk f j z) = attachmentDiskLabel f j z := by
  exact attachmentDescFun_disk f Sum.inl (attachmentDiskLabel f)
    (attachmentDiskLabel_boundary f) j z

private theorem attachmentLabel_disk_of_mem_range (f : J → C(Circle, X))
    (j : J) (z : D) (hz : z ∈ Set.range diskBoundary) :
    attachmentLabel f (diskAttachmentDisk f j z) =
      Sum.inl (f j (Classical.choose hz)) := by
  classical
  rw [attachmentLabel_disk, attachmentDiskLabel, dite_eq_left hz]

private theorem attachmentLabel_disk_of_not_mem_range (f : J → C(Circle, X))
    (j : J) (z : D) (hz : z ∉ Set.range diskBoundary) :
    attachmentLabel f (diskAttachmentDisk f j z) = Sum.inr ⟨j, z⟩ := by
  classical
  rw [attachmentLabel_disk, attachmentDiskLabel, dite_eq_right hz]

private theorem not_mem_range_diskBoundary_of_mem_ball {z : D}
    (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) : z ∉ Set.range diskBoundary := by
  rintro ⟨b, rfl⟩
  have hlt := mem_ball_zero_iff.1 hz
  rw [diskBoundary_coe, Circle.norm_coe] at hlt
  exact (lt_irrefl (1 : ℝ)) hlt

private theorem attachmentLabel_interior (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1)) :
    attachmentLabel f (diskAttachmentInterior f j z) =
      Sum.inr ⟨j, ⟨(z : ℂ), Metric.ball_subset_closedBall z.property⟩⟩ := by
  rw [diskAttachmentInterior_apply, attachmentLabel_disk_of_not_mem_range f j _
    (not_mem_range_diskBoundary_of_mem_ball z.property)]

public section

/-- Attaching disks does not identify distinct points of the original space. -/
theorem diskAttachmentInclusion_injective (f : J → C(Circle, X)) :
    Function.Injective (diskAttachmentInclusion f) := by
  intro x y h
  have h' := congrArg (attachmentLabel f) h
  simp only [attachmentLabel_inclusion] at h'
  exact Sum.inl.inj h'

/-- A disk point lies at an original point exactly when it is a boundary point
with that attaching-map value. -/
theorem diskAttachmentDisk_eq_inclusion_iff (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.closedBall (0 : ℂ) 1)) (x : X) :
    diskAttachmentDisk f j z = diskAttachmentInclusion f x ↔
      ∃ b : Circle, diskBoundary b = z ∧ f j b = x := by
  classical
  constructor
  · intro h
    have h' := congrArg (attachmentLabel f) h
    by_cases hz : z ∈ Set.range diskBoundary
    · rw [attachmentLabel_disk_of_mem_range f j z hz, attachmentLabel_inclusion] at h'
      exact ⟨Classical.choose hz, Classical.choose_spec hz, Sum.inl.inj h'⟩
    · rw [attachmentLabel_disk_of_not_mem_range f j z hz, attachmentLabel_inclusion] at h'
      cases h'
  · rintro ⟨b, hb, hbx⟩
    rw [← hb, diskAttachmentDisk_boundary, hbx]

/-- The preimage in a disk of an image from the original space is precisely
its attaching-map preimage in the boundary. -/
theorem diskAttachmentDisk_preimage_inclusion_image (f : J → C(Circle, X))
    (j : J) (S : Set X) :
    diskAttachmentDisk f j ⁻¹' (diskAttachmentInclusion f '' S) =
      diskBoundary '' (f j ⁻¹' S) := by
  ext z
  constructor
  · rintro ⟨x, hx, hxz⟩
    obtain ⟨b, hb, hbx⟩ := (diskAttachmentDisk_eq_inclusion_iff f j z x).1 hxz.symm
    refine ⟨b, ?_, hb⟩
    change f j b ∈ S
    rw [hbx]
    exact hx
  · rintro ⟨b, hb, rfl⟩
    exact ⟨f j b, hb, (diskAttachmentDisk_boundary f j b).symm⟩

/-- The original space is a closed embedded subspace of its disk attachment,
without any separation or local connectedness assumptions. -/
theorem isClosedEmbedding_diskAttachmentInclusion (f : J → C(Circle, X)) :
    IsClosedEmbedding (diskAttachmentInclusion f) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (diskAttachmentInclusion f).continuous (diskAttachmentInclusion_injective f) ?_
  intro S hS
  apply (isClosed_diskAttachment_iff f _).2
  constructor
  · rw [Set.preimage_image_eq _ (diskAttachmentInclusion_injective f)]
    exact hS
  · intro j
    rw [diskAttachmentDisk_preimage_inclusion_image]
    exact isClosedEmbedding_diskBoundary.isClosedMap _ (hS.preimage (f j).continuous)

/-- An open-disk point never lies in the original space. -/
theorem diskAttachmentInterior_ne_inclusion (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1)) (x : X) :
    diskAttachmentInterior f j z ≠ diskAttachmentInclusion f x := by
  intro h
  have h' := congrArg (attachmentLabel f) h
  simp only [attachmentLabel_interior, attachmentLabel_inclusion] at h'
  cases h'

/-- Equality with an open-disk point forces equality of disk indices and
of the underlying complex points, even when the other point is in a closed disk. -/
theorem diskAttachmentInterior_eq_disk_iff (f : J → C(Circle, X)) (j : J)
    (z : ↥(Metric.ball (0 : ℂ) 1)) (k : J)
    (w : ↥(Metric.closedBall (0 : ℂ) 1)) :
    diskAttachmentInterior f j z = diskAttachmentDisk f k w ↔
      j = k ∧ (z : ℂ) = (w : ℂ) := by
  classical
  constructor
  · intro h
    have h' := congrArg (attachmentLabel f) h
    rw [attachmentLabel_interior] at h'
    by_cases hw : w ∈ Set.range diskBoundary
    · rw [attachmentLabel_disk_of_mem_range f k w hw] at h'
      cases h'
    · rw [attachmentLabel_disk_of_not_mem_range f k w hw] at h'
      have hp := Sum.inr.inj h'
      exact ⟨congrArg Sigma.fst hp, congrArg (fun p : Σ _ : J, D => (p.2 : ℂ)) hp⟩
  · rintro ⟨hjk, hzw⟩
    rw [hjk, diskAttachmentInterior_apply]
    exact congrArg (diskAttachmentDisk f k) (Subtype.ext hzw)

/-- Each open-disk characteristic map is injective. -/
theorem diskAttachmentInterior_injective (f : J → C(Circle, X)) (j : J) :
    Function.Injective (diskAttachmentInterior f j) := by
  intro z w h
  have h' := h.trans (diskAttachmentInterior_apply f j w)
  exact Subtype.ext ((diskAttachmentInterior_eq_disk_iff f j z j _).1 h').2

/-- Each attached open disk is an open embedded subspace of the attachment. -/
theorem isOpenEmbedding_diskAttachmentInterior (f : J → C(Circle, X)) (j : J) :
    IsOpenEmbedding (diskAttachmentInterior f j) := by
  classical
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (diskAttachmentInterior f j).continuous (diskAttachmentInterior_injective f j) ?_
  intro S hS
  apply (isOpen_diskAttachment_iff f _).2
  constructor
  · have hpre : diskAttachmentInclusion f ⁻¹' (diskAttachmentInterior f j '' S) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨z, _, hzx⟩
      exact diskAttachmentInterior_ne_inclusion f j z x hzx
    rw [hpre]
    exact isOpen_empty
  · intro k
    by_cases hjk : j = k
    · subst k
      let i : ↥(Metric.ball (0 : ℂ) 1) → D := Set.inclusion Metric.ball_subset_closedBall
      have hi : IsOpenEmbedding i := IsOpenEmbedding.inclusion
        Metric.ball_subset_closedBall (Metric.isOpen_ball.preimage continuous_subtype_val)
      have hpre : diskAttachmentDisk f j ⁻¹' (diskAttachmentInterior f j '' S) = i '' S := by
        ext w
        constructor
        · rintro ⟨z, hz, hzw⟩
          exact ⟨z, hz, Subtype.ext ((diskAttachmentInterior_eq_disk_iff f j z j w).1 hzw).2⟩
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z, hz, diskAttachmentInterior_apply f j z⟩
      rw [hpre]
      exact hi.isOpenMap S hS
    · have hpre : diskAttachmentDisk f k ⁻¹' (diskAttachmentInterior f j '' S) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro w ⟨z, _, hzw⟩
        exact hjk ((diskAttachmentInterior_eq_disk_iff f j z k w).1 hzw).1
      rw [hpre]
      exact isOpen_empty

/-- The image of an attached open disk avoids the original space. -/
theorem disjoint_range_diskAttachmentInterior_inclusion (f : J → C(Circle, X)) (j : J) :
    Disjoint (Set.range (diskAttachmentInterior f j))
      (Set.range (diskAttachmentInclusion f)) := by
  rw [Set.disjoint_left]
  rintro p ⟨z, rfl⟩ ⟨x, hx⟩
  exact diskAttachmentInterior_ne_inclusion f j z x hx.symm

/-- The images of distinct attached open disks are disjoint. -/
theorem disjoint_range_diskAttachmentInterior (f : J → C(Circle, X))
    {j k : J} (hjk : j ≠ k) :
    Disjoint (Set.range (diskAttachmentInterior f j))
      (Set.range (diskAttachmentInterior f k)) := by
  rw [Set.disjoint_left]
  rintro p ⟨z, rfl⟩ ⟨w, hw⟩
  have h := hw.symm.trans (diskAttachmentInterior_apply f k w)
  exact hjk ((diskAttachmentInterior_eq_disk_iff f j z k _).1 h).1

end

private theorem boundaryMap_isIso [IsEmpty J] :
    IsIso (boundaryMap (J := J) :
      of (Σ _ : J, ULift.{u} Circle) ⟶ of (Σ _ : J, ULift.{u} D)) := by
  let e : of (Σ _ : J, ULift.{u} Circle) ≅ of (Σ _ : J, ULift.{u} D) :=
    isoOfHomeo Homeomorph.empty
  have he : boundaryMap (J := J) = e.hom :=
    TopCat.ext fun p => isEmptyElim p.1
  rw [he]
  infer_instance

private noncomputable def emptyCollapse [IsEmpty J] (f : J → C(Circle, X)) :
    diskAttachment f ≅ of (ULift.{v} X) := by
  letI : IsIso (boundaryMap (J := J) :
      of (Σ _ : J, ULift.{u} Circle) ⟶ of (Σ _ : J, ULift.{u} D)) := boundaryMap_isIso
  exact (attachmentIsColimit f).coconePointUniqueUpToIso
    (pushoutCoconeOfRightIsoIsLimit (attachingMap f) (boundaryMap (J := J)))

private theorem emptyCollapse_inclusion [IsEmpty J] (f : J → C(Circle, X)) (x : X) :
    (emptyCollapse f).inv (ULift.up x) = diskAttachmentInclusion f x := by
  let : IsIso (boundaryMap (J := J) :
      of (Σ _ : J, ULift.{u} Circle) ⟶ of (Σ _ : J, ULift.{u} D)) := boundaryMap_isIso
  have h : 𝟙 (of (ULift.{v} X)) ≫ (emptyCollapse f).inv = (attachmentCocone f).inl := by
    exact IsColimit.comp_coconePointUniqueUpToIso_inv
      (C := TopCat.{max u v})
      (F := span (attachingMap f) (boundaryMap (J := J)))
      (attachmentIsColimit f)
      (pushoutCoconeOfRightIsoIsLimit (attachingMap f) (boundaryMap (J := J)))
      WalkingSpan.left
  exact ConcreteCategory.congr_hom (C := TopCat.{max u v}) h (ULift.up x : ULift.{v} X)

public section

/-- With no attached disks, the original inclusion is a homeomorphism.
This holds for arbitrary, possibly disconnected or empty, original spaces. -/
noncomputable def diskAttachmentEmptyHomeomorph [IsEmpty J]
    (f : J → C(Circle, X)) : X ≃ₜ diskAttachment f :=
  Homeomorph.ulift.symm.trans (homeoOfIso (emptyCollapse f)).symm

/-- The empty-family homeomorphism is the original inclusion. -/
@[simp]
theorem diskAttachmentEmptyHomeomorph_apply [IsEmpty J]
    (f : J → C(Circle, X)) (x : X) :
    diskAttachmentEmptyHomeomorph f x = diskAttachmentInclusion f x :=
  emptyCollapse_inclusion f x

/-- The inverse empty-family homeomorphism retracts the original inclusion. -/
@[simp]
theorem diskAttachmentEmptyHomeomorph_symm_inclusion [IsEmpty J]
    (f : J → C(Circle, X)) (x : X) :
    (diskAttachmentEmptyHomeomorph f).symm (diskAttachmentInclusion f x) = x := by
  rw [← diskAttachmentEmptyHomeomorph_apply]
  exact (diskAttachmentEmptyHomeomorph f).symm_apply_apply x

end

private def singletonLiftHomeomorph (T : Type*) [TopologicalSpace T] :
    (Σ _ : PUnit, ULift.{0} T) ≃ₜ T where
  toFun p := p.2.down
  invFun z := ⟨PUnit.unit, ULift.up z⟩
  left_inv := by rintro ⟨⟨⟩, ⟨z⟩⟩; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_sigma fun _ => Homeomorph.ulift.continuous
  continuous_invFun := continuous_sigmaMk.comp Homeomorph.ulift.symm.continuous

private theorem identityAttachingMap_isIso :
    IsIso (attachingMap (fun _ : PUnit => ContinuousMap.id Circle) :
      of (Σ _ : PUnit, ULift.{0} Circle) ⟶ of (ULift.{0} Circle)) := by
  let e : of (Σ _ : PUnit, ULift.{0} Circle) ≅ of (ULift.{0} Circle) :=
    isoOfHomeo ((singletonLiftHomeomorph Circle).trans Homeomorph.ulift.symm)
  have he : attachingMap (fun _ : PUnit => ContinuousMap.id Circle) = e.hom :=
    TopCat.ext fun _ => rfl
  rw [he]
  infer_instance

private noncomputable def identityCollapse :
    diskAttachment (fun _ : PUnit => ContinuousMap.id Circle) ≅
      of (Σ _ : PUnit, ULift.{0} D) := by
  letI : IsIso (attachingMap (fun _ : PUnit => ContinuousMap.id Circle) :
      of (Σ _ : PUnit, ULift.{0} Circle) ⟶ of (ULift.{0} Circle)) := identityAttachingMap_isIso
  exact (attachmentIsColimit (fun _ : PUnit => ContinuousMap.id Circle)).coconePointUniqueUpToIso
    (pushoutCoconeOfLeftIsoIsLimit
      (attachingMap (fun _ : PUnit => ContinuousMap.id Circle)) (boundaryMap (J := PUnit)))

private theorem identityCollapse_disk (z : D) :
    identityCollapse.hom (diskAttachmentDisk (fun _ : PUnit => ContinuousMap.id Circle)
      PUnit.unit z) = ⟨PUnit.unit, ULift.up z⟩ := by
  let : IsIso (attachingMap (fun _ : PUnit => ContinuousMap.id Circle) :
      of (Σ _ : PUnit, ULift.{0} Circle) ⟶ of (ULift.{0} Circle)) := identityAttachingMap_isIso
  have h : (attachmentCocone (fun _ : PUnit => ContinuousMap.id Circle)).inr ≫
      identityCollapse.hom = 𝟙 (of (Σ _ : PUnit, ULift.{0} D)) := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (C := TopCat.{0})
      (F := span (attachingMap (fun _ : PUnit => ContinuousMap.id Circle))
        (boundaryMap (J := PUnit)))
      (attachmentIsColimit (fun _ : PUnit => ContinuousMap.id Circle))
      (pushoutCoconeOfLeftIsoIsLimit
        (attachingMap (fun _ : PUnit => ContinuousMap.id Circle)) (boundaryMap (J := PUnit)))
      WalkingSpan.right
  exact ConcreteCategory.congr_hom (C := TopCat.{0}) h
    (⟨PUnit.unit, ULift.up z⟩ : Σ _ : PUnit, ULift.{0} D)

public section

/-- Attaching one disk to the circle along its identity gives the closed unit disk. -/
noncomputable def diskAttachmentIdentityHomeomorph :
    diskAttachment (fun _ : PUnit => ContinuousMap.id Circle) ≃ₜ D :=
  (homeoOfIso identityCollapse).trans (singletonLiftHomeomorph D)

/-- The identity-attachment homeomorphism is the identity on the attached disk. -/
@[simp]
theorem diskAttachmentIdentityHomeomorph_disk (z : D) :
    diskAttachmentIdentityHomeomorph
      (diskAttachmentDisk (fun _ : PUnit => ContinuousMap.id Circle) PUnit.unit z) = z := by
  exact congrArg (fun p => p.2.down) (identityCollapse_disk z)

/-- The identity-attachment homeomorphism restricts to the boundary inclusion on the circle. -/
@[simp]
theorem diskAttachmentIdentityHomeomorph_inclusion (z : Circle) :
    diskAttachmentIdentityHomeomorph
      (diskAttachmentInclusion (fun _ : PUnit => ContinuousMap.id Circle) z) = diskBoundary z := by
  exact (congrArg diskAttachmentIdentityHomeomorph
    (diskAttachmentDisk_boundary (fun _ : PUnit => ContinuousMap.id Circle)
      PUnit.unit z)).symm.trans (diskAttachmentIdentityHomeomorph_disk (diskBoundary z))

/-- The inverse identity-attachment homeomorphism is the characteristic disk map. -/
@[simp]
theorem diskAttachmentIdentityHomeomorph_symm (z : D) :
    diskAttachmentIdentityHomeomorph.symm z =
      diskAttachmentDisk (fun _ : PUnit => ContinuousMap.id Circle) PUnit.unit z := by
  apply diskAttachmentIdentityHomeomorph.injective
  rw [diskAttachmentIdentityHomeomorph.apply_symm_apply,
    diskAttachmentIdentityHomeomorph_disk]

end

end TopCat
