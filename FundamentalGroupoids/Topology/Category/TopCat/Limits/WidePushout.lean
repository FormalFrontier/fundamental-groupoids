/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.ULift
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Quotient presentations of topological wide pushouts

For continuous maps `f i : B ⟶ X i`, the quotient of `B ⊕ Σ i, X i` identifying
`b` with `(i, f i b)` is Mathlib's existing `Types.Pushout`, applied to the maps
`(i, b) ↦ b` and `(i, b) ↦ (i, f i b)`. No additional space model is introduced.
`TopCat.widePushoutHomeomorph` compares this quotient, with its quotient topology,
with the categorical wide pushout, preserving the head and every factor.

The index and space universes are independent, with the diagram in their maximum.
`TopCat.uliftFunctor` transports smaller spaces into that ambient universe.
The target of `TopCat.widePushoutDesc` has an independent universe.

When `B` is a point, the relation identifies the head with all the selected
points, leaving the other classes singleton. The head remains present when the
index is empty. Empty and singleton diagrams are treated without separation,
compactness, cofibration or homotopy assumptions.

## Implementation notes

The inverse comparison is categorical descent of the continuous quotient
inclusions. Quotient induction and the head and factor equations show that the
two comparisons are inverse. No fundamental-group calculation or contraction
is asserted.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, for the point-wedge setting.
* Mathlib's `CategoryTheory.Limits.Types.Pushout`, by Joël Riou, supplies the
  quotient model; its wide pushouts and topological colimit constructions supply
  the categorical model and final-topology API.
* The inclusion and descent interface of `SphereTopology.Homotopy.CircleBouquet`
  motivates the characteristic API; no circle-group result is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v z

namespace CategoryTheory.Limits.Types

/-- The pushout type has the quotient topology from the disjoint sum. -/
instance instTopologicalSpacePushout {S A B : Type u}
    [TopologicalSpace A] [TopologicalSpace B]
    (f : S ⟶ A) (g : S ⟶ B) : TopologicalSpace (Pushout f g) :=
  inferInstanceAs (TopologicalSpace (Quot (Pushout.Rel f g)))

end CategoryTheory.Limits.Types

namespace TopCat

variable {I : Type v} {B : TopCat.{max u v}} {X : I → TopCat.{max u v}}
  (f : ∀ i, B ⟶ X i)

/-- The continuous map from the head-plus-factors quotient to the wide pushout. -/
def widePushoutQuotientMap :
    C(Types.Pushout
      (↾Prod.snd : (I × B) ⟶ (B : Type (max u v)))
      (↾fun p : I × B ↦ (⟨p.1, f p.1 p.2⟩ : Σ i, X i)),
      (widePushout B X f : TopCat.{max u v})) where
  toFun := Quot.lift
    (Sum.elim (WidePushout.head f) (fun p ↦ WidePushout.ι f p.1 p.2)) (by
      rintro _ _ ⟨⟨i, b⟩⟩
      exact (congrArg (fun h : B ⟶ (widePushout B X f : TopCat.{max u v}) ↦ h b)
        (WidePushout.arrow_ι f i)).symm)
  continuous_toFun := continuous_quot_lift _
    ((WidePushout.head f).hom.continuous.sumElim
      (continuous_sigma fun i ↦ (WidePushout.ι f i).hom.continuous))

/-- The quotient comparison preserves the entire head map. -/
@[simp] theorem widePushoutQuotientMap_inl (b : B) :
    widePushoutQuotientMap f (Quot.mk _ (Sum.inl b)) = WidePushout.head f b := rfl

/-- The quotient comparison preserves every factor map. -/
@[simp] theorem widePushoutQuotientMap_inr (i : I) (x : X i) :
    widePushoutQuotientMap f (Quot.mk _ (Sum.inr ⟨i, x⟩)) = WidePushout.ι f i x := rfl

/-- The head-plus-factors quotient, with its quotient topology, presents the
categorical wide pushout of arbitrary continuous maps with common domain. -/
theorem isHomeomorph_widePushoutQuotientMap :
    IsHomeomorph (widePushoutQuotientMap f) := by
  let Q := Types.Pushout
    (↾Prod.snd : (I × B) ⟶ (B : Type (max u v)))
    (↾fun p : I × B ↦ (⟨p.1, f p.1 p.2⟩ : Σ i, X i))
  let a : B ⟶ TopCat.of Q := TopCat.ofHom
    ⟨fun b ↦ Quot.mk _ (Sum.inl b), continuous_quot_mk.comp continuous_inl⟩
  let c : ∀ i, X i ⟶ TopCat.of Q := fun i ↦ TopCat.ofHom
    ⟨fun x ↦ Quot.mk _ (Sum.inr ⟨i, x⟩),
      continuous_quot_mk.comp (continuous_inr.comp continuous_sigmaMk)⟩
  have w : ∀ i, f i ≫ c i = a := by
    intro i
    apply TopCat.ext
    intro b
    exact (Quot.sound (Types.Pushout.Rel.inl_inr (f := ↾Prod.snd)
      (g := ↾fun p : I × B ↦ (⟨p.1, f p.1 p.2⟩ : Σ i, X i)) (i, b))).symm
  let g := WidePushout.desc a c w
  have hB (b : B) : g (WidePushout.head f b) = Quot.mk _ (Sum.inl b) :=
    congrArg (fun k : B ⟶ TopCat.of Q ↦ k b) (WidePushout.head_desc f a c w)
  have hX (i : I) (x : X i) : g (WidePushout.ι f i x) = Quot.mk _ (Sum.inr ⟨i, x⟩) :=
    congrArg (fun k : X i ⟶ TopCat.of Q ↦ k x) (WidePushout.ι_desc f a c w i)
  refine isHomeomorph_iff_exists_inverse.2
    ⟨(widePushoutQuotientMap f).continuous, g, ?_, ?_, g.hom.continuous⟩
  · intro q
    refine Quot.inductionOn q ?_
    rintro (b | ⟨i, x⟩)
    · exact hB b
    · exact hX i x
  · intro y
    obtain ⟨_ | i, x, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan B X f) y
    · change widePushoutQuotientMap f (g (WidePushout.head f x)) = WidePushout.head f x
      rw [hB]
      rfl
    · change widePushoutQuotientMap f (g (WidePushout.ι f i x)) = WidePushout.ι f i x
      rw [hX]
      rfl

/-- The homeomorphism from the head-plus-factors quotient to the wide pushout. -/
def widePushoutHomeomorph :
    Types.Pushout
      (↾Prod.snd : (I × B) ⟶ (B : Type (max u v)))
      (↾fun p : I × B ↦ (⟨p.1, f p.1 p.2⟩ : Σ i, X i)) ≃ₜ
      (widePushout B X f : TopCat.{max u v}) :=
  (isHomeomorph_widePushoutQuotientMap f).homeomorph (widePushoutQuotientMap f)

/-- The homeomorphism has the prescribed quotient comparison as its forward map. -/
@[simp] theorem widePushoutHomeomorph_apply
    (q : Types.Pushout
      (↾Prod.snd : (I × B) ⟶ (B : Type (max u v)))
      (↾fun p : I × B ↦ (⟨p.1, f p.1 p.2⟩ : Σ i, X i))) :
    widePushoutHomeomorph f q = widePushoutQuotientMap f q := rfl

/-- The inverse homeomorphism preserves the head. -/
@[simp] theorem widePushoutHomeomorph_symm_head (b : B) :
    (widePushoutHomeomorph f).symm (WidePushout.head f b) = Types.Pushout.inl _ _ b := by
  apply (widePushoutHomeomorph f).injective
  simp only [Homeomorph.apply_symm_apply]
  rfl

/-- The inverse homeomorphism preserves every factor. -/
@[simp] theorem widePushoutHomeomorph_symm_ι (i : I) (x : X i) :
    (widePushoutHomeomorph f).symm (WidePushout.ι f i x) =
      Types.Pushout.inr _ _ ⟨i, x⟩ := by
  apply (widePushoutHomeomorph f).injective
  simp only [Homeomorph.apply_symm_apply]
  rfl

/-- Continuity out of a wide pushout can be checked on its head and every factor.
The target universe is independent of the diagram universe. -/
theorem continuous_widePushout_iff {Y : Type z} [TopologicalSpace Y]
    (g : ↑(widePushout B X f : TopCat.{max u v}) → Y) :
    Continuous g ↔ Continuous (g ∘ WidePushout.head f) ∧
      ∀ i, Continuous (g ∘ WidePushout.ι f i) := by
  refine (continuous_iff_of_isColimit
    (colimit.cocone (WidePushoutShape.wideSpan B X f)) (colimit.isColimit _) g).trans ?_
  constructor
  · intro h
    exact ⟨h none, fun i ↦ h (some i)⟩
  · rintro ⟨hB, hX⟩ (_ | i)
    · exact hB
    · exact hX i

/-- Functions out of a wide pushout are determined by the head and all factors,
including when the index is empty. No topology on the target is needed. -/
@[ext (iff := false)] theorem widePushout_funext {Y : Sort z}
    {g h : ↑(widePushout B X f : TopCat.{max u v}) → Y}
    (hB : ∀ b, g (WidePushout.head f b) = h (WidePushout.head f b))
    (hX : ∀ i x, g (WidePushout.ι f i x) = h (WidePushout.ι f i x)) : g = h := by
  funext y
  obtain ⟨_ | i, x, rfl⟩ :=
    Concrete.colimit_exists_rep (WidePushoutShape.wideSpan B X f) y
  · exact hB x
  · exact hX i x

/-- Descend compatible continuous maps to a target in an independent universe. -/
def widePushoutDesc {Y : Type z} [TopologicalSpace Y]
    (g : C(B, Y)) (h : ∀ i, C(X i, Y)) (w : ∀ i b, h i (f i b) = g b) :
    C((widePushout B X f : TopCat.{max u v}), Y) :=
  let k : C(Types.Pushout
      (↾Prod.snd : (I × B) ⟶ (B : Type (max u v)))
      (↾fun p : I × B ↦ (⟨p.1, f p.1 p.2⟩ : Σ i, X i)), Y) :=
    { toFun := Quot.lift (Sum.elim g (fun p ↦ h p.1 p.2)) (by
        rintro _ _ ⟨⟨i, b⟩⟩
        exact (w i b).symm)
      continuous_toFun := continuous_quot_lift _
        (g.continuous.sumElim (continuous_sigma fun i ↦ (h i).continuous)) }
  k.comp ((widePushoutHomeomorph f).symm : C((widePushout B X f : TopCat.{max u v}), _))

/-- Descent restricts to the prescribed map on the head. -/
@[simp] theorem widePushoutDesc_head {Y : Type z} [TopologicalSpace Y]
    (g : C(B, Y)) (h : ∀ i, C(X i, Y)) (w : ∀ i b, h i (f i b) = g b) (b : B) :
    widePushoutDesc f g h w (WidePushout.head f b) = g b := by
  simp [widePushoutDesc]
  rfl

/-- Descent restricts to the prescribed map on every factor. -/
@[simp] theorem widePushoutDesc_ι {Y : Type z} [TopologicalSpace Y]
    (g : C(B, Y)) (h : ∀ i, C(X i, Y)) (w : ∀ i b, h i (f i b) = g b)
    (i : I) (x : X i) :
    widePushoutDesc f g h w (WidePushout.ι f i x) = h i x := by
  simp [widePushoutDesc]
  rfl

/-- The head and factor equations uniquely characterize descent. -/
theorem widePushoutDesc_unique {Y : Type z} [TopologicalSpace Y]
    (g : C(B, Y)) (h : ∀ i, C(X i, Y)) (w : ∀ i b, h i (f i b) = g b)
    (k : C((widePushout B X f : TopCat.{max u v}), Y))
    (hB : ∀ b, k (WidePushout.head f b) = g b)
    (hX : ∀ i x, k (WidePushout.ι f i x) = h i x) : k = widePushoutDesc f g h w := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨_ | i, x, rfl⟩ :=
    Concrete.colimit_exists_rep (WidePushoutShape.wideSpan B X f) y
  · rw [hB, widePushoutDesc_head]
  · rw [hX, widePushoutDesc_ι]

/-- In the diagram universe, continuous descent agrees with categorical descent. -/
theorem widePushoutDesc_eq_desc {Y : TopCat.{max u v}}
    (g : B ⟶ Y) (h : ∀ i, X i ⟶ Y) (w : ∀ i, f i ≫ h i = g) :
    widePushoutDesc f g.hom (fun i ↦ (h i).hom)
      (fun i b ↦ congrArg (fun k : B ⟶ Y ↦ k b) (w i)) =
        (WidePushout.desc g h w).hom := by
  symm
  apply widePushoutDesc_unique
  · intro b
    exact congrArg (fun k : B ⟶ Y ↦ k b) (WidePushout.head_desc f g h w)
  · intro i x
    exact congrArg (fun k : X i ⟶ Y ↦ k x) (WidePushout.ι_desc f g h w i)

/-- An empty wide pushout is its head, via the head map itself. -/
theorem isHomeomorph_widePushout_head [IsEmpty I] : IsHomeomorph (WidePushout.head f) := by
  let g := widePushoutDesc f (ContinuousMap.id B) (fun i ↦ isEmptyElim i)
    (fun i ↦ isEmptyElim i)
  refine isHomeomorph_iff_exists_inverse.2 ⟨(WidePushout.head f).hom.continuous,
    g, ?_, ?_, g.continuous⟩
  · intro b
    simp [g]
  · intro y
    obtain ⟨_ | i, x, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan B X f) y
    · simp [g]
    · exact False.elim (isEmptyElim i)

/-- A singleton wide pushout is its factor, via that factor's inclusion itself. -/
theorem isHomeomorph_widePushout_ι [Subsingleton I] (i : I) :
    IsHomeomorph (WidePushout.ι f i) := by
  let h : ∀ j, C(X j, X i) := fun j ↦ by
    obtain rfl : j = i := Subsingleton.elim j i
    exact ContinuousMap.id _
  have w : ∀ j b, h j (f j b) = f i b := by
    intro j b
    obtain rfl : j = i := Subsingleton.elim j i
    rfl
  let g := widePushoutDesc f (f i).hom h w
  refine isHomeomorph_iff_exists_inverse.2 ⟨(WidePushout.ι f i).hom.continuous,
    g, ?_, ?_, g.continuous⟩
  · intro x
    simp [g, h]
  · intro y
    obtain ⟨_ | j, x, rfl⟩ :=
      Concrete.colimit_exists_rep (WidePushoutShape.wideSpan B X f) y
    · change WidePushout.ι f i
        (widePushoutDesc f (f i).hom h w (WidePushout.head f x)) = WidePushout.head f x
      rw [widePushoutDesc_head]
      exact congrArg (fun k : B ⟶ (widePushout B X f : TopCat.{max u v}) ↦ k x)
        (WidePushout.arrow_ι f i)
    · obtain rfl : j = i := Subsingleton.elim j i
      simp [g, h]

/-- Compatible maps from pointed factors descend uniquely, with the common point
and every inclusion prescribed. This also includes the empty family. -/
theorem existsUnique_widePushout_point {Y : Type z} [TopologicalSpace Y]
    (x : ∀ i, X i) (y : Y) (h : ∀ i, C(X i, Y)) (w : ∀ i, h i (x i) = y) :
    ∃! k : C((widePushout (TopCat.of PUnit.{max u v + 1}) X
        (fun i ↦ TopCat.const (x i)) : TopCat.{max u v}), Y),
      k (WidePushout.head (fun i ↦ TopCat.const (x i)) PUnit.unit) = y ∧
        ∀ i t, k (WidePushout.ι (fun i ↦ TopCat.const (x i)) i t) = h i t := by
  let a : ∀ i, TopCat.of PUnit.{max u v + 1} ⟶ X i := fun i ↦ TopCat.const (x i)
  let g := widePushoutDesc a (ContinuousMap.const _ y) h (fun i _ ↦ w i)
  refine ⟨g, ⟨?_, ?_⟩, ?_⟩
  · exact widePushoutDesc_head a (ContinuousMap.const _ y) h (fun i _ ↦ w i) PUnit.unit
  · intro i t
    exact widePushoutDesc_ι a (ContinuousMap.const _ y) h (fun i _ ↦ w i) i t
  · intro k hk
    apply widePushoutDesc_unique
    · intro b
      cases b
      exact hk.1
    · exact hk.2

end TopCat
