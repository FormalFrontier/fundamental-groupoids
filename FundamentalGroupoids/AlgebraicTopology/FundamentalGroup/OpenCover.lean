/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Sets.Opens
public import FundamentalGroupoids.FundamentalGroup
import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.OpenCoverDescent
import Mathlib.CategoryTheory.SingleObj

/-!
# Fundamental groups of two path-connected open subsets

For two open subsets covering a space, a point in their intersection determines an
inclusion square of fundamental groups. Path connectedness of the two subsets and
their intersection gives the based van Kampen universal property. The homomorphism
form permits a target group in a universe independent of the space; the categorical
form is a pushout square in `GrpCat`.

The inclusion cocone commutes without connectedness or coverage assumptions. The
auxiliary path choices are made first in the intersection, normalized in the path
homotopy quotient, and extended to both charts using those same intersection paths.
This is the finite compatible-choice step in the passage from strict fundamental-
groupoid descent to the based-group theorem. No global path-connectedness hypothesis
or local path-connectedness hypothesis is added.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §7, printed
  pp. 17–19: the groupoid colimit theorem and the based-group colimit theorem.
  The two-open inclusion span is a specialization of the common-basepoint,
  intersection-closed cover formulation; global path connectedness follows from
  the two local hypotheses, the common point, and coverage.
* Mathlib's fundamental groupoids and path homotopies, by Shing Tak Lam, and
  fundamental groups, by Mark Lavrentyev; its continuous subtype inclusions,
  path-connectedness, bundled groups, and pushout cocones.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X]

-- Composition with a subtype inclusion is quotient functoriality.
private theorem map_inclusion_subtypeVal {s t : Set X} (hst : s ⊆ t)
    {a b : s} (q : Path.Homotopic.Quotient a b) :
    (q.map (ContinuousMap.inclusion hst)).map (ContinuousMap.subtypeVal t) =
      q.map (ContinuousMap.subtypeVal s) :=
  (Path.Homotopic.Quotient.map_comp (p := q)
    (f := ContinuousMap.inclusion hst) (g := ContinuousMap.subtypeVal t)).symm

private theorem hom_inclusion_subtypeVal {s t : Set X} (hst : s ⊆ t) (p : s) :
    (map (ContinuousMap.subtypeVal t) ((ContinuousMap.inclusion hst) p)).comp
        (map (ContinuousMap.inclusion hst) p) =
      map (ContinuousMap.subtypeVal s) p := by
  exact (map_comp (ContinuousMap.subtypeVal t) (ContinuousMap.inclusion hst) p).symm

private theorem ofHom_inclusion_subtypeVal {s t : Set X} (hst : s ⊆ t) (p : s) :
    GrpCat.ofHom (map (ContinuousMap.inclusion hst) p) ≫
        GrpCat.ofHom (map (ContinuousMap.subtypeVal t) ((ContinuousMap.inclusion hst) p)) =
      GrpCat.ofHom (map (ContinuousMap.subtypeVal s) p) := by
  apply GrpCat.hom_ext
  exact hom_inclusion_subtypeVal hst p

private theorem inclusion_square (U V : Opens X) (p : ↑(U ⊓ V)) :
    GrpCat.ofHom (map (ContinuousMap.inclusion
        (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X)) Set.inter_subset_left) p) ≫
      GrpCat.ofHom (map (ContinuousMap.subtypeVal (U : Set X))
        (⟨p.1, p.2.1⟩ : U)) =
    GrpCat.ofHom (map (ContinuousMap.inclusion
        (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X)) Set.inter_subset_right) p) ≫
      GrpCat.ofHom (map (ContinuousMap.subtypeVal (V : Set X))
        (⟨p.1, p.2.2⟩ : V)) :=
  (ofHom_inclusion_subtypeVal (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X))
    Set.inter_subset_left p).trans
      (ofHom_inclusion_subtypeVal (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X))
        Set.inter_subset_right p).symm

-- This cocone uses only the inclusions and the common point.
private def inclusionPushoutCocone (U V : Opens X) (p : ↑(U ⊓ V)) :
    PushoutCocone
      (GrpCat.ofHom (map (ContinuousMap.inclusion
        (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X)) Set.inter_subset_left) p))
      (GrpCat.ofHom (map (ContinuousMap.inclusion
        (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X)) Set.inter_subset_right) p)) :=
  PushoutCocone.mk
    (GrpCat.ofHom (map (ContinuousMap.subtypeVal (U : Set X))
      (⟨p.1, p.2.1⟩ : U)))
    (GrpCat.ofHom (map (ContinuousMap.subtypeVal (V : Set X))
      (⟨p.1, p.2.2⟩ : V)))
    (inclusion_square U V p)

private theorem inclusionPushoutCocone_pt (U V : Opens X) (p : ↑(U ⊓ V)) :
    (inclusionPushoutCocone U V p).pt = GrpCat.of (FundamentalGroup X p.1) := rfl

private theorem inclusionPushoutCocone_inl (U V : Opens X) (p : ↑(U ⊓ V)) :
    (inclusionPushoutCocone U V p).inl =
      GrpCat.ofHom (map (ContinuousMap.subtypeVal (U : Set X))
        (⟨p.1, p.2.1⟩ : U)) := rfl

private theorem inclusionPushoutCocone_inr (U V : Opens X) (p : ↑(U ⊓ V)) :
    (inclusionPushoutCocone U V p).inr =
      GrpCat.ofHom (map (ContinuousMap.subtypeVal (V : Set X))
        (⟨p.1, p.2.2⟩ : V)) := rfl

private theorem inclusionPushoutCocone_zero_comp (U V : Opens X) (p : ↑(U ⊓ V)) :
    (inclusionPushoutCocone U V p).ι.app WalkingSpan.zero =
      GrpCat.ofHom (map (ContinuousMap.inclusion
          (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X)) Set.inter_subset_left) p) ≫
        (inclusionPushoutCocone U V p).inl :=
  PushoutCocone.condition_zero _

private theorem inclusionPushoutCocone_zero (U V : Opens X) (p : ↑(U ⊓ V)) :
    (inclusionPushoutCocone U V p).ι.app WalkingSpan.zero =
      GrpCat.ofHom (map (ContinuousMap.subtypeVal (↑(U ⊓ V) : Set X)) p) := by
  rw [inclusionPushoutCocone_zero_comp, inclusionPushoutCocone_inl]
  exact ofHom_inclusion_subtypeVal Set.inter_subset_left p

-- Choose once on the intersection, then normalize by cancelling the chosen loop.
private def intersectionChoicePath (U V : Opens X)
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p x : ↑(U ⊓ V)) : Path p x := by
  letI : PathConnectedSpace ↑(U ⊓ V) := isPathConnected_iff_pathConnectedSpace.mp hI
  exact PathConnectedSpace.somePath p x

private def intersectionPath (U V : Opens X)
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p x : ↑(U ⊓ V)) : Path p x :=
  (intersectionChoicePath U V hI p p).symm.trans (intersectionChoicePath U V hI p x)

private def intersectionArrow (U V : Opens X)
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p x : ↑(U ⊓ V)) :
    FundamentalGroupoid.mk p ⟶ FundamentalGroupoid.mk x :=
  Path.Homotopic.Quotient.mk (intersectionPath U V hI p x)

private theorem intersectionArrow_unit (U V : Opens X)
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) :
    intersectionArrow U V hI p p = 𝟙 (FundamentalGroupoid.mk p) := by
  change Path.Homotopic.Quotient.mk
      ((intersectionChoicePath U V hI p p).symm.trans (intersectionChoicePath U V hI p p)) =
    Path.Homotopic.Quotient.mk (Path.refl p)
  exact Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.symm_trans _)

-- On the overlap both chart paths are images of the same intersection path.
private def leftPath (U V : Opens X) (hU : IsPathConnected (U : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) (x : U) :
    Path (⟨p.1, p.2.1⟩ : U) x := by
  classical
  letI : PathConnectedSpace U := isPathConnected_iff_pathConnectedSpace.mp hU
  exact if hx : x.1 ∈ V then
    (intersectionPath U V hI p ⟨x.1, x.2, hx⟩).map
      (ContinuousMap.inclusion (s := (↑(U ⊓ V) : Set X))
        (t := (U : Set X)) Set.inter_subset_left).continuous
  else
    PathConnectedSpace.somePath _ _

private def rightPath (U V : Opens X) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) (x : V) :
    Path (⟨p.1, p.2.2⟩ : V) x := by
  classical
  letI : PathConnectedSpace V := isPathConnected_iff_pathConnectedSpace.mp hV
  exact if hx : x.1 ∈ U then
    (intersectionPath U V hI p ⟨x.1, hx, x.2⟩).map
      (ContinuousMap.inclusion (s := (↑(U ⊓ V) : Set X))
        (t := (V : Set X)) Set.inter_subset_right).continuous
  else
    PathConnectedSpace.somePath _ _

private def leftArrow (U V : Opens X) (hU : IsPathConnected (U : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) (x : U) :
    FundamentalGroupoid.mk (⟨p.1, p.2.1⟩ : U) ⟶ FundamentalGroupoid.mk x :=
  Path.Homotopic.Quotient.mk (leftPath U V hU hI p x)

private def rightArrow (U V : Opens X) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) (x : V) :
    FundamentalGroupoid.mk (⟨p.1, p.2.2⟩ : V) ⟶ FundamentalGroupoid.mk x :=
  Path.Homotopic.Quotient.mk (rightPath U V hV hI p x)

private theorem leftArrow_on_intersection (U V : Opens X)
    (hU : IsPathConnected (U : Set X)) (hI : IsPathConnected (↑(U ⊓ V) : Set X))
    (p x : ↑(U ⊓ V)) :
    leftArrow U V hU hI p (⟨x.1, x.2.1⟩ : U) =
      (FundamentalGroupoid.map (ContinuousMap.inclusion
        (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X)) Set.inter_subset_left)).map
          (intersectionArrow U V hI p x) := by
  classical
  change Path.Homotopic.Quotient.mk (leftPath U V hU hI p ⟨x.1, x.2.1⟩) =
    Path.Homotopic.Quotient.mk ((intersectionPath U V hI p x).map
      (ContinuousMap.inclusion (s := (↑(U ⊓ V) : Set X))
        (t := (U : Set X)) Set.inter_subset_left).continuous)
  dsimp only [leftPath]
  exact congrArg Path.Homotopic.Quotient.mk (dite_eq_left x.2.2)

private theorem rightArrow_on_intersection (U V : Opens X)
    (hV : IsPathConnected (V : Set X)) (hI : IsPathConnected (↑(U ⊓ V) : Set X))
    (p x : ↑(U ⊓ V)) :
    rightArrow U V hV hI p (⟨x.1, x.2.2⟩ : V) =
      (FundamentalGroupoid.map (ContinuousMap.inclusion
        (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X)) Set.inter_subset_right)).map
          (intersectionArrow U V hI p x) := by
  classical
  change Path.Homotopic.Quotient.mk (rightPath U V hV hI p ⟨x.1, x.2.2⟩) =
    Path.Homotopic.Quotient.mk ((intersectionPath U V hI p x).map
      (ContinuousMap.inclusion (s := (↑(U ⊓ V) : Set X))
        (t := (V : Set X)) Set.inter_subset_right).continuous)
  dsimp only [rightPath]
  exact congrArg Path.Homotopic.Quotient.mk (dite_eq_left x.2.1)

private theorem leftArrow_unit (U V : Opens X)
    (hU : IsPathConnected (U : Set X)) (hI : IsPathConnected (↑(U ⊓ V) : Set X))
    (p : ↑(U ⊓ V)) :
    leftArrow U V hU hI p (⟨p.1, p.2.1⟩ : U) =
      𝟙 (FundamentalGroupoid.mk (⟨p.1, p.2.1⟩ : U)) := by
  rw [leftArrow_on_intersection U V hU hI p p, intersectionArrow_unit U V hI p]
  rfl

private theorem rightArrow_unit (U V : Opens X)
    (hV : IsPathConnected (V : Set X)) (hI : IsPathConnected (↑(U ⊓ V) : Set X))
    (p : ↑(U ⊓ V)) :
    rightArrow U V hV hI p (⟨p.1, p.2.2⟩ : V) =
      𝟙 (FundamentalGroupoid.mk (⟨p.1, p.2.2⟩ : V)) := by
  rw [rightArrow_on_intersection U V hV hI p p, intersectionArrow_unit U V hI p]
  rfl

private theorem chartArrows_compatible (U V : Opens X)
    (hU : IsPathConnected (U : Set X)) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p x : ↑(U ⊓ V)) :
    (FundamentalGroupoid.map (ContinuousMap.subtypeVal (U : Set X))).map
        (leftArrow U V hU hI p (⟨x.1, x.2.1⟩ : U)) =
      (FundamentalGroupoid.map (ContinuousMap.subtypeVal (V : Set X))).map
        (rightArrow U V hV hI p (⟨x.1, x.2.2⟩ : V)) := by
  rw [leftArrow_on_intersection U V hU hI p x, rightArrow_on_intersection U V hV hI p x]
  change ((intersectionArrow U V hI p x).map (ContinuousMap.inclusion
      (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X)) Set.inter_subset_left)).map
        (ContinuousMap.subtypeVal (U : Set X)) =
    ((intersectionArrow U V hI p x).map (ContinuousMap.inclusion
      (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X)) Set.inter_subset_right)).map
        (ContinuousMap.subtypeVal (V : Set X))
  exact (map_inclusion_subtypeVal (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X))
    Set.inter_subset_left (intersectionArrow U V hI p x)).trans
      (map_inclusion_subtypeVal (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X))
        Set.inter_subset_right (intersectionArrow U V hI p x)).symm

-- A frame sends each arrow to its loop at the chosen vertex. The reversed
-- multiplication of endomorphisms is exactly the composition in `SingleObj`.
-- Regard the loop as an arrow of C before regarding it as a SingleObj arrow.
private def frameFunctor {C : Type*} [Groupoid C] (p : C)
    (c : ∀ x : C, p ⟶ x) : C ⥤ SingleObj (End p) where
  obj _ := SingleObj.star (End p)
  map {x y} f := show p ⟶ p from c x ≫ f ≫ CategoryTheory.inv (c y)
  map_id x := by
    change c x ≫ 𝟙 x ≫ inv (c x) = 𝟙 p
    simp
  map_comp {x y z} f g := by
    change c x ≫ (f ≫ g) ≫ inv (c z) =
      (c x ≫ f ≫ inv (c y)) ≫ (c y ≫ g ≫ inv (c z))
    simp [Category.assoc]

private def frameHomFunctor {C : Type*} [Groupoid C] (p : C)
    (c : ∀ x : C, p ⟶ x) {G : Type v} [Group G] (φ : End p →* G) :
    C ⥤ SingleObj G :=
  frameFunctor p c ⋙ SingleObj.mapHom (End p) G φ

private theorem frameHomFunctor_map {C : Type*} [Groupoid C] (p : C)
    (c : ∀ x : C, p ⟶ x) {G : Type v} [Group G] (φ : End p →* G)
    {x y : C} (f : x ⟶ y) :
    (frameHomFunctor p c φ).map f =
      φ (show p ⟶ p from c x ≫ f ≫ CategoryTheory.inv (c y)) := rfl

-- Equality transports in a one-object category are identity arrows, even when
-- the object selected by descent is not definitionally the displayed star.
private theorem singleObj_eqToHom {G : Type v} [Group G]
    {a b : SingleObj G} (h : a = b) : (eqToHom h : a ⟶ b) = (1 : G) := by
  subst b
  rfl

private theorem singleObjFunctor_ext {C : Type*} [Category C]
    {G : Type v} [Group G] {F H : C ⥤ SingleObj G}
    (h : ∀ {x y : C} (f : x ⟶ y), (F.map f : G) = H.map f) : F = H := by
  refine CategoryTheory.Functor.ext (F := F) (G := H)
    (fun x : C => Subsingleton.elim (F.obj x) (H.obj x)) ?_
  intro x y f
  simpa only [singleObj_eqToHom, SingleObj.comp_as_mul, one_mul, mul_one] using h f

-- Extract a homomorphism using the independent-universe correspondence
-- between homomorphisms and one-object functors.
private def vertexHom {C : Type*} [Category C] (p : C)
    {G : Type v} [Group G] (F : C ⥤ SingleObj G) : End p →* G :=
  (SingleObj.mapHom (End p) G).symm
    (SingleObj.functor (MonoidHom.id (End p)) ⋙ F)

private theorem vertexHom_apply {C : Type*} [Category C] (p : C)
    {G : Type v} [Group G] (F : C ⥤ SingleObj G) (f : End p) :
    vertexHom p F f = F.map f := rfl

private theorem vertexHom_comp {C D : Type*} [Category C] [Category D]
    (K : C ⥤ D) (p : C) {G : Type v} [Group G] (F : D ⥤ SingleObj G) :
    (vertexHom (K.obj p) F).comp (K.mapEnd p) = vertexHom p (K ⋙ F) := by
  apply MonoidHom.ext
  intro f
  rfl

private theorem vertexHom_frameHomFunctor {C : Type*} [Groupoid C] (p : C)
    (c : ∀ x : C, p ⟶ x) (hc : c p = 𝟙 p)
    {G : Type v} [Group G] (φ : End p →* G) :
    vertexHom p (frameHomFunctor p c φ) = φ := by
  apply MonoidHom.ext
  intro f
  rw [vertexHom_apply, frameHomFunctor_map, hc]
  simp

-- Compatible frames make restriction strict; agreement merely up to unrelated
-- vertex equivalences would leave unwanted conjugations at the basepoint.
private theorem frameHomFunctor_restrict {C D : Type*} [Groupoid C] [Groupoid D]
    (K : C ⥤ D) (p : C) (c : ∀ x : C, p ⟶ x)
    (d : ∀ y : D, K.obj p ⟶ y)
    (hd : ∀ x : C, d (K.obj x) = K.map (c x))
    {G : Type v} [Group G] (φ : End p →* G) (ψ : End (K.obj p) →* G)
    (hφ : ψ.comp (K.mapEnd p) = φ) :
    K ⋙ frameHomFunctor (K.obj p) d ψ = frameHomFunctor p c φ := by
  apply singleObjFunctor_ext
  intro x y f
  simp only [CategoryTheory.Functor.comp_map, frameHomFunctor_map]
  rw [hd x, hd y, ← K.map_inv, ← K.map_comp, ← K.map_comp]
  exact DFunLike.congr_fun hφ
    (show p ⟶ p from c x ≫ f ≫ CategoryTheory.inv (c y))

private theorem mem_left_or_right (U V : Opens X) (hcover : U ⊔ V = ⊤) (x : X) :
    x ∈ U ∨ x ∈ V := by
  have hx : x ∈ U ⊔ V := by rw [hcover]; trivial
  exact hx

-- The two local frames have the same image on the overlap, so membership cases
-- glue them to a single normalized global frame, without a new hypothesis on X.
private def globalArrow (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X)) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) (x : X) :
    FundamentalGroupoid.mk p.1 ⟶ FundamentalGroupoid.mk x := by
  classical
  exact if hx : x ∈ U then
    (FundamentalGroupoid.map (ContinuousMap.subtypeVal (U : Set X))).map
      (leftArrow U V hU hI p ⟨x, hx⟩)
  else
    (FundamentalGroupoid.map (ContinuousMap.subtypeVal (V : Set X))).map
      (rightArrow U V hV hI p ⟨x, (mem_left_or_right U V hcover x).resolve_left hx⟩)

private theorem globalArrow_left (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X)) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) (x : U) :
    globalArrow U V hcover hU hV hI p x.1 =
      (FundamentalGroupoid.map (ContinuousMap.subtypeVal (U : Set X))).map
        (leftArrow U V hU hI p x) := by
  classical
  dsimp only [globalArrow]
  exact dite_eq_left x.2

private theorem globalArrow_right (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X)) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) (x : V) :
    globalArrow U V hcover hU hV hI p x.1 =
      (FundamentalGroupoid.map (ContinuousMap.subtypeVal (V : Set X))).map
        (rightArrow U V hV hI p x) := by
  classical
  by_cases hx : x.1 ∈ U
  · have hleft : globalArrow U V hcover hU hV hI p x.1 =
        (FundamentalGroupoid.map (ContinuousMap.subtypeVal (U : Set X))).map
          (leftArrow U V hU hI p ⟨x.1, hx⟩) := by
      dsimp only [globalArrow]
      exact dite_eq_left hx
    exact hleft.trans (chartArrows_compatible U V hU hV hI p ⟨x.1, hx, x.2⟩)
  · dsimp only [globalArrow]
    exact dite_eq_right hx

private theorem globalArrow_unit (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X)) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) :
    globalArrow U V hcover hU hV hI p p.1 = 𝟙 (FundamentalGroupoid.mk p.1) := by
  rw [globalArrow_left U V hcover hU hV hI p (⟨p.1, p.2.1⟩ : U),
    leftArrow_unit U V hU hI p]
  exact (FundamentalGroupoid.map (ContinuousMap.subtypeVal (U : Set X))).map_id _

/-- Compatible homomorphisms from the fundamental groups of two path-connected opens
extend uniquely to the fundamental group of their union, when the opens cover the
space and their intersection is path connected. The target group universe is independent
of the space universe.

This is the two-open specialization of the based-group colimit theorem in
J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §7, printed pp. 17–19. -/
theorem existsUnique_hom_of_isOpenCover
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X)) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) :
    ∀ (G : Type v) [Group G]
      (φU : FundamentalGroup U (⟨p.1, p.2.1⟩ : U) →* G)
      (φV : FundamentalGroup V (⟨p.1, p.2.2⟩ : V) →* G),
      φU.comp (map (ContinuousMap.inclusion
          (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X)) Set.inter_subset_left) p) =
        φV.comp (map (ContinuousMap.inclusion
          (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X)) Set.inter_subset_right) p) →
      ∃! φ : FundamentalGroup X p.1 →* G,
        φ.comp (map (ContinuousMap.subtypeVal (U : Set X)) (⟨p.1, p.2.1⟩ : U)) = φU ∧
        φ.comp (map (ContinuousMap.subtypeVal (V : Set X)) (⟨p.1, p.2.2⟩ : V)) = φV := by
  classical
  intro G _ φU φV hcompat
  let pU : U := ⟨p.1, p.2.1⟩
  let pV : V := ⟨p.1, p.2.2⟩
  let kU : C(↑(U ⊓ V), U) := ContinuousMap.inclusion Set.inter_subset_left
  let kV : C(↑(U ⊓ V), V) := ContinuousMap.inclusion Set.inter_subset_right
  let jU := ContinuousMap.subtypeVal (U : Set X)
  let jV := ContinuousMap.subtypeVal (V : Set X)
  let cI := fun x : FundamentalGroupoid ↑(U ⊓ V) => intersectionArrow U V hI p x.as
  let cU := fun x : FundamentalGroupoid U => leftArrow U V hU hI p x.as
  let cV := fun x : FundamentalGroupoid V => rightArrow U V hV hI p x.as
  let TI := frameHomFunctor (FundamentalGroupoid.mk p) cI (φU.comp (map kU p))
  let TU := frameHomFunctor (FundamentalGroupoid.mk pU) cU φU
  let TV := frameHomFunctor (FundamentalGroupoid.mk pV) cV φV
  have hUI : FundamentalGroupoid.map kU ⋙ TU = TI :=
    frameHomFunctor_restrict (FundamentalGroupoid.map kU) (FundamentalGroupoid.mk p)
      cI cU (fun x => leftArrow_on_intersection U V hU hI p x.as)
      (φU.comp (map kU p)) φU rfl
  have hVI : FundamentalGroupoid.map kV ⋙ TV = TI :=
    frameHomFunctor_restrict (FundamentalGroupoid.map kV) (FundamentalGroupoid.mk p)
      cI cV (fun x => rightArrow_on_intersection U V hV hI p x.as)
      (φU.comp (map kU p)) φV hcompat.symm
  let W : Bool → Opens X := fun | false => U | true => V
  have hW : IsOpenCover W := by
    change (⨆ b, W b) = ⊤
    apply top_unique
    rw [← hcover]
    exact sup_le (le_iSup W false) (le_iSup W true)
  let F : ∀ b, FundamentalGroupoid (W b) ⥤ SingleObj G :=
    fun | false => TU | true => TV
  have hF : ∀ i j,
      (FundamentalGroupoid.openCoverDiagram W).map (Pairwise.Hom.left i j) ⋙ F i =
        (FundamentalGroupoid.openCoverDiagram W).map (Pairwise.Hom.right i j) ⋙ F j := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact hUI.trans hVI.symm
    · -- Reverse ordered overlaps use the same intersection, with swapped proofs.
      let swap : C(↑(V ⊓ U), ↑(U ⊓ V)) :=
        ContinuousMap.inclusion (fun _ hx => ⟨hx.2, hx.1⟩)
      -- These composites equal the native intersection inclusions as continuous maps.
      have hswapV : kV.comp swap =
          ((Opens.toTopCat (TopCat.of X)).map (Opens.infLELeft V U)).hom := by
        apply ContinuousMap.ext
        intro x
        rfl
      have hswapU : kU.comp swap =
          ((Opens.toTopCat (TopCat.of X)).map (Opens.infLERight V U)).hom := by
        apply ContinuousMap.ext
        intro x
        rfl
      have h := congrArg (fun T => FundamentalGroupoid.map swap ⋙ T)
        (hVI.trans hUI.symm)
      have hcomp : FundamentalGroupoid.map (kV.comp swap) ⋙ TV =
          FundamentalGroupoid.map (kU.comp swap) ⋙ TU := by
        simpa only [← CategoryTheory.Functor.assoc, ← FundamentalGroupoid.map_comp] using h
      rw [hswapV, hswapU] at hcomp
      exact hcomp
    · rfl
  let D := FundamentalGroupoid.descOfIsOpenCover hW F hF
  let φ : FundamentalGroup X p.1 →* G := vertexHom (FundamentalGroupoid.mk p.1) D
  have hφU : φ.comp (map jU pU) = φU := by
    calc
      φ.comp (map jU pU) = vertexHom (FundamentalGroupoid.mk pU)
          (FundamentalGroupoid.map jU ⋙ D) :=
        vertexHom_comp (FundamentalGroupoid.map jU) (FundamentalGroupoid.mk pU) D
      _ = vertexHom (FundamentalGroupoid.mk pU) TU :=
        congrArg (vertexHom (FundamentalGroupoid.mk pU))
          (FundamentalGroupoid.inclusion_comp_descOfIsOpenCover hW F hF false)
      _ = φU := vertexHom_frameHomFunctor (FundamentalGroupoid.mk pU) cU
        (leftArrow_unit U V hU hI p) φU
  have hφV : φ.comp (map jV pV) = φV := by
    calc
      φ.comp (map jV pV) = vertexHom (FundamentalGroupoid.mk pV)
          (FundamentalGroupoid.map jV ⋙ D) :=
        vertexHom_comp (FundamentalGroupoid.map jV) (FundamentalGroupoid.mk pV) D
      _ = vertexHom (FundamentalGroupoid.mk pV) TV :=
        congrArg (vertexHom (FundamentalGroupoid.mk pV))
          (FundamentalGroupoid.inclusion_comp_descOfIsOpenCover hW F hF true)
      _ = φV := vertexHom_frameHomFunctor (FundamentalGroupoid.mk pV) cV
        (rightArrow_unit U V hV hI p) φV
  refine ⟨φ, ⟨hφU, hφV⟩, ?_⟩
  intro ψ hψ
  let cX := fun x : FundamentalGroupoid X => globalArrow U V hcover hU hV hI p x.as
  let K := frameHomFunctor (FundamentalGroupoid.mk p.1) cX ψ
  have hK : ∀ b, FundamentalGroupoid.map (ContinuousMap.subtypeVal (W b : Set X)) ⋙ K =
      F b := by
    intro b
    cases b
    · exact frameHomFunctor_restrict (FundamentalGroupoid.map jU)
        (FundamentalGroupoid.mk pU) cU cX
        (fun x => globalArrow_left U V hcover hU hV hI p x.as) φU ψ hψ.1
    · exact frameHomFunctor_restrict (FundamentalGroupoid.map jV)
        (FundamentalGroupoid.mk pV) cV cX
        (fun x => globalArrow_right U V hcover hU hV hI p x.as) φV ψ hψ.2
  calc
    ψ = vertexHom (FundamentalGroupoid.mk p.1) K :=
      (vertexHom_frameHomFunctor (FundamentalGroupoid.mk p.1) cX
        (globalArrow_unit U V hcover hU hV hI p) ψ).symm
    _ = vertexHom (FundamentalGroupoid.mk p.1) D :=
      congrArg (vertexHom (FundamentalGroupoid.mk p.1))
        (FundamentalGroupoid.descOfIsOpenCover_unique hW F hF K hK)
    _ = φ := rfl

/-- The inclusion square of fundamental groups of a two-open cover is a pushout in
`GrpCat`, provided both opens and their intersection are path connected and a common
basepoint is chosen. This is the categorical form of
`FundamentalGroup.existsUnique_hom_of_isOpenCover` in the space universe.

This is the two-open specialization of the based-group colimit theorem in
J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §7, printed pp. 17–19. -/
theorem isPushout_of_isOpenCover
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X)) (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) (p : ↑(U ⊓ V)) :
    IsPushout (C := GrpCat.{u})
      (GrpCat.ofHom (map (ContinuousMap.inclusion
        (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X)) Set.inter_subset_left) p))
      (GrpCat.ofHom (map (ContinuousMap.inclusion
        (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X)) Set.inter_subset_right) p))
      (GrpCat.ofHom (map (ContinuousMap.subtypeVal (U : Set X)) (⟨p.1, p.2.1⟩ : U)))
      (GrpCat.ofHom (map (ContinuousMap.subtypeVal (V : Set X)) (⟨p.1, p.2.2⟩ : V))) := by
  classical
  have hc : IsColimit (inclusionPushoutCocone U V p) := by
    refine PushoutCocone.isColimitAux' _ ?_
    intro s
    have hcompat :
        s.inl.hom.comp (map (ContinuousMap.inclusion
            (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X)) Set.inter_subset_left) p) =
          s.inr.hom.comp (map (ContinuousMap.inclusion
            (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X)) Set.inter_subset_right) p) := by
      simpa only [GrpCat.hom_comp, GrpCat.hom_ofHom] using
        congrArg GrpCat.Hom.hom s.condition
    have h := existsUnique_hom_of_isOpenCover U V hcover hU hV hI p
      (s.pt : Type u) s.inl.hom s.inr.hom hcompat
    let φ := Classical.choose h
    have hφ := (Classical.choose_spec h).1
    have hφ_unique := (Classical.choose_spec h).2
    refine ⟨GrpCat.ofHom φ, ?_, ?_, ?_⟩
    · rw [inclusionPushoutCocone_inl]
      apply GrpCat.hom_ext
      change φ.comp (map (ContinuousMap.subtypeVal (U : Set X))
        (⟨p.1, p.2.1⟩ : U)) = s.inl.hom
      exact hφ.1
    · rw [inclusionPushoutCocone_inr]
      apply GrpCat.hom_ext
      change φ.comp (map (ContinuousMap.subtypeVal (V : Set X))
        (⟨p.1, p.2.2⟩ : V)) = s.inr.hom
      exact hφ.2
    · intro m hmU hmV
      rw [inclusionPushoutCocone_inl] at hmU
      rw [inclusionPushoutCocone_inr] at hmV
      apply GrpCat.hom_ext
      apply hφ_unique m.hom
      constructor
      · have hmU' := congrArg GrpCat.Hom.hom hmU
        change m.hom.comp (map (ContinuousMap.subtypeVal (U : Set X))
          (⟨p.1, p.2.1⟩ : U)) = s.inl.hom at hmU'
        exact hmU'
      · have hmV' := congrArg GrpCat.Hom.hom hmV
        change m.hom.comp (map (ContinuousMap.subtypeVal (V : Set X))
          (⟨p.1, p.2.2⟩ : V)) = s.inr.hom at hmV'
        exact hmV'
  exact
    { w := inclusion_square U V p
      isColimit' := ⟨hc⟩ }

end FundamentalGroup
