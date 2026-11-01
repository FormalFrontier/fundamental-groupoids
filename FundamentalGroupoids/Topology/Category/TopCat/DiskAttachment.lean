/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Attaching a family of disks

`TopCat.diskAttachment f` attaches one closed complex unit disk along each map
in a family `f : ∀ j, C(Circle, X)`. The construction uses the quotient pushout
in types and its final topology in `TopCat`. The maps from `X` and from each
disk have their original domains, without universe lifts in the public API.

`TopCat.diskAttachmentDesc` and `TopCat.continuous_diskAttachment_iff` express
the universal property with a target in an independent universe. Empty families
recover `X`, and attaching a single disk along the identity of its boundary
recovers the closed disk, with the indicated original inclusion maps.

No connectedness or separation assumptions on `X` are required.
-/

open CategoryTheory CategoryTheory.Limits

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

end

private def attachmentDescFun {Z : Type w} (f : J → C(Circle, X))
    (g : X → Z) (d : J → D → Z)
    (h : ∀ j z, d j (diskBoundary z) = g (f j z)) : diskAttachment f → Z :=
  Quot.lift (Sum.elim (fun x : ULift.{v} X => g x.down)
    (fun p : Σ _ : J, ULift.{u} D => d p.1 p.2.down)) (by
      rintro _ _ ⟨p⟩
      exact (h p.1 p.2.down).symm)

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
