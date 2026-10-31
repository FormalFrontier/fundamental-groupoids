/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Order.SupClosed
public import FundamentalGroupoids.FundamentalGroup
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenNhds
import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.OpenCoverDescent
import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.Connected
import Mathlib.CategoryTheory.SingleObj

/-!
# Fundamental groups of path-connected open covers

For two open subsets covering a space, a point in their intersection determines an
inclusion square of fundamental groups. Path connectedness of the two subsets and
their intersection gives the based van Kampen universal property. The homomorphism
form permits a target group in a universe independent of the space; the categorical
form is a pushout square in `GrpCat`. For simply connected opens with path-connected
intersection, the corresponding simple-connectivity criterion has no ambient
path-connectedness assumption.

The inclusion cocone commutes without connectedness or coverage assumptions. The
auxiliary path choices are made first in the intersection, normalized in the path
homotopy quotient, and extended to both charts using those same intersection paths.
This is the finite compatible-choice step in the passage from strict fundamental-
groupoid descent to the based-group theorem. No global path-connectedness hypothesis
or local path-connectedness hypothesis is added.

Intersection-closed families of open neighborhoods give inclusion-indexed cocones of
fundamental groups. The indexing presentation may repeat an open set: the induced
category retains all inclusion arrows between the presented neighborhoods. Binary
intersection closure, expressed by `InfClosed`, also gives closure under every
nonempty finite intersection, without requiring the whole space to be a member.
The homomorphism form quantifies a target-group universe independent of both the
space and the indexing type.

A family of path-connected neighborhoods with a common path-connected overlap needs
only compatibility from that overlap to each member. Adjoining the overlap as an
`Option`-indexed member reduces this universal property to the intersection-closed
one. The family may be empty or repeat an open neighborhood; inclusions between
members require no additional compatibility hypotheses.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §7, printed
  pp. 17–19: the groupoid colimit theorem and the based-group colimit theorem.
  The two-open inclusion span is a specialization of the common-basepoint,
  intersection-closed cover formulation; global path connectedness follows from
  the two local hypotheses, the common point, and coverage. Chapter 2, §8,
  printed p. 20 motivates the simple-connectivity consequence.
* Mathlib's fundamental groupoids and path homotopies, by Shing Tak Lam, and
  fundamental groups, by Mark Lavrentyev; its continuous subtype inclusions,
  path-connectedness, bundled groups, and pushout cocones. Its simple-connectivity
  API, by Praneeth Kolichala and contributors, supplies the canonical class and
  subsingleton local fundamental groups.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

/-- A nonempty directed union of open simply connected subsets is simply connected.

Compactness of loop images reduces each loop to one member. The null-loop
characterization is Mathlib's
`isSimplyConnected_iff_exists_homotopy_refl_forall_mem`. -/
theorem IsSimplyConnected.iUnion_of_directed
    {X : Type u} [TopologicalSpace X] {ι : Type w} [Nonempty ι]
    {U : ι → Set X} (hU : ∀ i, IsSimplyConnected (U i))
    (hopen : ∀ i, IsOpen (U i)) (hdir : Directed (· ⊆ ·) U) :
    IsSimplyConnected (⋃ i, U i) := by
  classical
  refine isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mpr ⟨?_, ?_⟩
  · refine isPathConnected_iff.mpr ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := (hU (Classical.arbitrary ι)).nonempty
      exact ⟨x, Set.mem_iUnion.mpr ⟨_, hx⟩⟩
    · intro x hx y hy
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hy
      obtain ⟨k, hik, hjk⟩ := hdir i j
      exact ((hU k).isPathConnected.joinedIn x (hik hxi) y (hjk hyj)).mono
        (fun z hz => Set.mem_iUnion.mpr ⟨k, hz⟩)
  · intro x gamma hgamma
    have hrange : Set.range gamma ⊆ ⋃ i, U i := by
      rintro z ⟨t, rfl⟩
      exact hgamma t
    obtain ⟨i, hi⟩ := (isCompact_range gamma.continuous).elim_directed_cover
      U hopen hrange hdir
    obtain ⟨F, hF⟩ :=
      (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp (hU i)).2 x gamma
        (fun t => hi ⟨t, rfl⟩)
    exact ⟨F, fun t => Set.mem_iUnion.mpr ⟨i, hF t⟩⟩

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

/-- A space covered by two simply connected open subsets with path-connected intersection
is simply connected. The intersection hypothesis includes nonemptiness; ambient path
connectedness follows from the local hypotheses and coverage. No local path connectedness
or separation assumption is required, and the intersection need not be simply connected.

This is a consequence of the based van Kampen theorem discussed in J. P. May,
*A Concise Course in Algebraic Topology*, Chapter 2, §8, printed p. 20, stated here
without Chapter 3's standing local path-connectedness assumption. -/
theorem simplyConnectedSpace_of_isOpenCover
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsSimplyConnected (U : Set X)) (hV : IsSimplyConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X)) : SimplyConnectedSpace X := by
  have hunion : (U : Set X) ∪ (V : Set X) = Set.univ :=
    congrArg (fun W : Opens X => (W : Set X)) hcover
  let : PathConnectedSpace X := pathConnectedSpace_iff_univ.mpr
    (hunion ▸ hU.isPathConnected.union hV.isPathConnected hI.nonempty)
  let : SimplyConnectedSpace U := hU.simplyConnectedSpace
  let : SimplyConnectedSpace V := hV.simplyConnectedSpace
  obtain ⟨x, hx⟩ := hI.nonempty
  let p : ↑(U ⊓ V) := ⟨x, hx⟩
  let pU : U := ⟨p.1, p.2.1⟩
  let pV : V := ⟨p.1, p.2.2⟩
  let G := FundamentalGroup X p.1
  -- Uniqueness compares the identity and trivial endomorphisms: both restrict
  -- to the trivial homomorphism on each simply connected open.
  obtain ⟨φ, _, huniq⟩ := existsUnique_hom_of_isOpenCover U V hcover
    hU.isPathConnected hV.isPathConnected hI p G
    (1 : FundamentalGroup U pU →* G) (1 : FundamentalGroup V pV →* G)
    (by exact (MonoidHom.one_comp _).trans (MonoidHom.one_comp _).symm)
  have hid : MonoidHom.id G = (1 : G →* G) := by
    refine (huniq (MonoidHom.id G) ?_).trans (huniq 1 ?_).symm
    · constructor
      · apply MonoidHom.ext
        intro g
        change map (ContinuousMap.subtypeVal (U : Set X)) pU g = 1
        rw [Subsingleton.elim g 1, map_one]
      · apply MonoidHom.ext
        intro g
        change map (ContinuousMap.subtypeVal (V : Set X)) pV g = 1
        rw [Subsingleton.elim g 1, map_one]
    · exact ⟨MonoidHom.one_comp _, MonoidHom.one_comp _⟩
  have htrivial (g : G) : g = 1 := DFunLike.congr_fun hid g
  exact (simplyConnectedSpace_iff p.1).mpr
    ⟨inferInstance, ⟨fun a b => (htrivial a).trans (htrivial b).symm⟩⟩

-- Apply the two-open criterion in the union, where the relative opens cover.
private theorem isSimplyConnected_sup (A B : Opens X)
    (hA : IsSimplyConnected (A : Set X)) (hB : IsSimplyConnected (B : Set X))
    (hI : IsPathConnected (↑(A ⊓ B) : Set X)) :
    IsSimplyConnected (↑(A ⊔ B) : Set X) := by
  let W : Set X := ↑(A ⊔ B)
  let q : C(W, X) := ContinuousMap.subtypeVal W
  let A' : Opens W := Opens.comap q A
  let B' : Opens W := Opens.comap q B
  have hcover : A' ⊔ B' = ⊤ := by
    apply Opens.ext
    change ((↑) : W → X) ⁻¹' W = Set.univ
    exact Subtype.coe_preimage_self W
  have hq : Topology.IsEmbedding (q : W → X) := Topology.IsEmbedding.subtypeVal
  have hrel (C : Opens X) (hC : C ≤ A ⊔ B)
      (hSC : IsSimplyConnected (C : Set X)) :
      IsSimplyConnected (↑(Opens.comap q C) : Set W) := by
    apply hq.isSimplyConnected_image.mp
    change IsSimplyConnected (((↑) : W → X) '' (((↑) : W → X) ⁻¹' (C : Set X)))
    rw [Subtype.image_preimage_val, Set.inter_eq_right.mpr hC]
    exact hSC
  have hI' : IsPathConnected (↑(A' ⊓ B') : Set W) := by
    change IsPathConnected (((↑) : W → X) ⁻¹' (↑(A ⊓ B) : Set X))
    exact hI.preimage_coe (fun _ hx => Or.inl hx.1)
  exact simplyConnectedSpace_of_isOpenCover A' B' hcover
    (hrel A le_sup_left hA) (hrel B le_sup_right hB) hI'

/-- A space covered by simply connected open subsets with a common point and
path-connected pairwise intersections is simply connected. The family may be infinite,
and no connectedness condition on triple intersections is required. No local
path-connectedness or separation assumption is needed.

This follows from the two-open van Kampen theorem and compactness of loop images;
see J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §§7–8,
printed pp. 17–20. -/
theorem simplyConnectedSpace_of_isOpenCover_of_commonPoint
    {ι : Type w} (U : ι → Opens X) (hcover : IsOpenCover U)
    (p : X) (hp : ∀ i, p ∈ U i)
    (hU : ∀ i, IsSimplyConnected (U i : Set X))
    (hI : ∀ i j, IsPathConnected (↑(U i ⊓ U j) : Set X)) : SimplyConnectedSpace X := by
  classical
  obtain ⟨i₀, _⟩ := hcover.exists_mem p
  let W (s : Finset ι) : Opens X := U i₀ ⊔ s.sup U
  have hW_empty : W ∅ = U i₀ := by simp [W]
  have hW_insert (s : Finset ι) (i : ι) : W (insert i s) = W s ⊔ U i := by
    simp only [W, Finset.sup_insert, sup_left_comm, sup_comm]
  have hpW (s : Finset ι) : p ∈ W s := Or.inl (hp i₀)
  -- Each overlap is a finite union of pairwise overlaps, all containing p.
  have hWI : ∀ (s : Finset ι) (j : ι),
      IsPathConnected (↑(W s ⊓ U j) : Set X) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro j
      simpa only [hW_empty] using hI i₀ j
    | @insert i s _hi ih =>
      intro j
      rw [hW_insert, inf_sup_right, Opens.coe_sup]
      exact (ih j).union (hI i j) ⟨p, ⟨hpW s, hp j⟩, ⟨hp i, hp j⟩⟩
  have hWSC : ∀ s : Finset ι, IsSimplyConnected (W s : Set X) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa only [hW_empty] using hU i₀
    | @insert i s _hi ih =>
      rw [hW_insert]
      exact isSimplyConnected_sup (W s) (U i) ih (hU i) (hWI s i)
  have hmono : Monotone W := by
    intro s t hst
    exact sup_le_sup le_rfl (Finset.sup_mono hst)
  have hdir : Directed (· ⊆ ·) (fun s : Finset ι => (W s : Set X)) := by
    intro s t
    exact ⟨s ∪ t, hmono Finset.subset_union_left, hmono Finset.subset_union_right⟩
  have hunion : (⋃ s : Finset ι, (W s : Set X)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := hcover.exists_mem x
    refine Set.mem_iUnion.mpr ⟨{i}, ?_⟩
    change x ∈ U i₀ ⊔ ({i} : Finset ι).sup U
    rw [Finset.sup_singleton]
    exact Or.inr hi
  have hSC := IsSimplyConnected.iUnion_of_directed hWSC (fun s => (W s).isOpen) hdir
  rw [hunion] at hSC
  exact (Homeomorph.Set.univ X).toHomotopyEquiv.simplyConnectedSpace_iff.mp
    hSC.simplyConnectedSpace

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

-- Normalizing a frame by its value at the vertex avoids any equality test on objects.
private def normalizedFrame {C : Type*} [Groupoid C] [IsPreconnected C]
    (p : C) (y : C) : p ⟶ y :=
  inv (Classical.choice (inferInstance : Nonempty (p ⟶ p))) ≫
    Classical.choice (inferInstance : Nonempty (p ⟶ y))

private theorem normalizedFrame_unit {C : Type*} [Groupoid C] [IsPreconnected C]
    (p : C) : normalizedFrame p p = 𝟙 p := by
  simp [normalizedFrame]

-- Read back an arrow through the canonical endomorphism equivalence before
-- simplifying, so that scalar calculations use the supplied monoid structure.
private theorem singleObj_toEnd_symm_apply {M : Type*} [Monoid M] (m : M) :
    (SingleObj.toEnd M).symm m = m := by
  simpa only [SingleObj.toEnd_def] using (SingleObj.toEnd M).symm_apply_apply m

-- Equality of vertex homomorphisms is equality of the corresponding one-object
-- functors, whose transport has identity component at the vertex.
private def vertexNatTrans {C : Type*} [Category C] (p : C)
    {G : Type w} [Group G] (F H : C ⥤ SingleObj G)
    (h : vertexHom p F = vertexHom p H) :
    SingleObj.functor (MonoidHom.id (End p)) ⋙ F ⟶
      SingleObj.functor (MonoidHom.id (End p)) ⋙ H :=
  eqToHom ((SingleObj.mapHom (End p) G).symm.injective h)

private theorem vertexNatTrans_app {C : Type*} [Category C] (p : C)
    {G : Type w} [Group G] (F H : C ⥤ SingleObj G)
    (h : vertexHom p F = vertexHom p H) (a : SingleObj (End p)) :
    @Eq G ((vertexNatTrans p F H h).app a) (1 : G) := by
  simp only [vertexNatTrans, eqToHom_app, singleObj_eqToHom]

-- Full precomposition extends the vertex transformation; faithful precomposition
-- makes the extension unique. In particular no compatible choices of frames are inputs.
private def vertexIso {C : Type*} [Groupoid C] [IsPreconnected C] (p : C)
    {G : Type w} [Group G] (F H : C ⥤ SingleObj G)
    (h : vertexHom p F = vertexHom p H) : F ≅ H := by
  let J := SingleObj.functor (C := C) (X := p) (MonoidHom.id (End p))
  let P := (Functor.whiskeringLeft (SingleObj (End p)) C (SingleObj G)).obj J
  let t := vertexNatTrans p F H h
  letI : IsIso t := NatIso.isIso_of_isIso_app t
  exact P.preimageIso (asIso t)

private theorem vertexIso_base {C : Type*} [Groupoid C] [IsPreconnected C] (p : C)
    {G : Type w} [Group G] (F H : C ⥤ SingleObj G)
    (h : vertexHom p F = vertexHom p H) :
    ((vertexIso p F H h).hom.app p : G) = 1 := by
  let J := SingleObj.functor (C := C) (X := p) (MonoidHom.id (End p))
  let P := (Functor.whiskeringLeft (SingleObj (End p)) C (SingleObj G)).obj J
  have hJ : J.obj (SingleObj.star (End p)) = p :=
    SingleObj.functor_obj (X := p) (MonoidHom.id (End p)) _
  apply (SingleObj.toEnd G).symm.injective
  have ht :
      @Eq G ((P.preimage (vertexNatTrans p F H h)).app (J.obj (SingleObj.star (End p))))
        ((vertexNatTrans p F H h).app (SingleObj.star (End p))) := by
    have ht := congrArg
      (fun t => (SingleObj.toEnd G).symm (t.app (SingleObj.star (End p))))
      (P.map_preimage (vertexNatTrans p F H h))
    simpa only [P, Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app,
      singleObj_toEnd_symm_apply] using ht
  rw [hJ, vertexNatTrans_app] at ht
  simpa only [vertexIso, Functor.preimageIso_hom, asIso_hom,
    singleObj_toEnd_symm_apply] using ht

-- This component formula is also a convenient way to use uniqueness after
-- restriction: a path in a smaller connected neighborhood computes every comparison.
private theorem normalizedNatTrans_app {C : Type*} [Category C] (p : C)
    {G : Type w} [Group G] {F H : C ⥤ SingleObj G} (α : F ⟶ H)
    (hα : (α.app p : G) = 1) {y : C} (q : p ⟶ y) :
    @Eq G (α.app y)
      (@Mul.mul G inferInstance (H.map q) (@Inv.inv G inferInstance (F.map q))) := by
  have h := congrArg (SingleObj.toEnd G).symm (α.naturality q)
  have hp := congrArg (SingleObj.toEnd G).symm hα
  simp only [singleObj_toEnd_symm_apply, SingleObj.comp_as_mul] at h
  simp only [singleObj_toEnd_symm_apply] at hp
  rw [hp, mul_one] at h
  exact (@eq_mul_inv_iff_mul_eq G inferInstance (α.app y) (H.map q) (F.map q)).2 h

private theorem groupoid_map_obj {Y : Type*} [TopologicalSpace Y]
    (f : C(X, Y)) (a : FundamentalGroupoid X) :
    (FundamentalGroupoid.map f).obj a = FundamentalGroupoid.mk (f a.as) := by
  apply FundamentalGroupoid.ext
  exact FundamentalGroupoid.map_obj_as f a

-- These isomorphisms merely view elements as arrows of the existing SingleObj groupoid.
private def singleObjIso {G : Type w} [Group G] {a b : SingleObj G} (g : G) : a ≅ b :=
  asIso (g : a ⟶ b)

private theorem singleObj_copyObj_map {C : Type*} [Category C]
    {G : Type w} [Group G] (F : C ⥤ SingleObj G) (obj : C → SingleObj G)
    (e : C → G) {a b : C} (f : a ⟶ b) :
    @Eq G ((F.copyObj obj (fun y => singleObjIso (e y))).map f)
      (e b * F.map f * (e a)⁻¹) := by
  have h := congrArg (SingleObj.toEnd G).symm
    ((F.isoCopyObj obj (fun y => singleObjIso (e y))).hom.naturality f)
  simp only [singleObj_toEnd_symm_apply, Functor.isoCopyObj_hom_app, singleObjIso,
    asIso_hom, SingleObj.comp_as_mul] at h
  exact (@eq_mul_inv_iff_mul_eq G inferInstance
    ((F.copyObj obj (fun y => singleObjIso (e y))).map f) (e b * F.map f) (e a)).2 h.symm

private theorem vertexHom_copyObj {C : Type*} [Category C] (p : C)
    {G : Type w} [Group G] (F : C ⥤ SingleObj G) (obj : C → SingleObj G)
    (e : C → G) (he : e p = 1) :
    vertexHom p (F.copyObj obj (fun y => singleObjIso (e y))) = vertexHom p F := by
  apply MonoidHom.ext
  intro f
  simp only [vertexHom_apply, singleObj_copyObj_map, he, inv_one, one_mul, mul_one]

-- An intersection represented elsewhere in the family gives agreement on the
-- intersection itself, not just on a chosen presentation of it.
private theorem homs_agree_on_inf (x : X)
    (A B C : OpenNhds (X := TopCat.of X) x) (hCA : C ≤ A) (hCB : C ≤ B)
    (hC : C = A ⊓ B)
    {G : Type w} [Group G]
    (fA : FundamentalGroup A.1 ⟨x, A.2⟩ →* G)
    (fB : FundamentalGroup B.1 ⟨x, B.2⟩ →* G)
    (fC : FundamentalGroup C.1 ⟨x, C.2⟩ →* G)
    (hA : fA.comp (((openNhdsFunctor x).map (homOfLE hCA)).hom) = fC)
    (hB : fB.comp (((openNhdsFunctor x).map (homOfLE hCB)).hom) = fC) :
    fA.comp (map (ContinuousMap.inclusion
        (s := (↑(A.1 ⊓ B.1) : Set X)) (t := (A.1 : Set X)) Set.inter_subset_left)
        ⟨x, A.2, B.2⟩) =
      fB.comp (map (ContinuousMap.inclusion
        (s := (↑(A.1 ⊓ B.1) : Set X)) (t := (B.1 : Set X)) Set.inter_subset_right)
        ⟨x, A.2, B.2⟩) := by
  subst C
  exact hA.trans hB.symm

section IndexedCover

variable {ι : Type v}

private theorem indexedCover_nonempty
    (x : X) (U : ι → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1)) : Nonempty ι := by
  obtain ⟨i, _⟩ := hcover.exists_mem x
  exact ⟨i⟩

private theorem indexedCover_pathConnectedSpace
    (x : X) (U : ι → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X)) : PathConnectedSpace X := by
  apply pathConnectedSpace_iff_univ.mpr
  refine ⟨x, Set.mem_univ x, ?_⟩
  intro y _
  obtain ⟨i, hi⟩ := hcover.exists_mem y
  exact ((hpc i).joinedIn x (U i).2 y hi).mono (Set.subset_univ _)

private theorem indexedCover_inf_pathConnected
    (x : X) (U : ι → OpenNhds (X := TopCat.of X) x)
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) (i j : ι) :
    IsPathConnected (↑((U i).1 ⊓ (U j).1) : Set X) := by
  obtain ⟨k, hk⟩ := hclosed (Set.mem_range_self i) (Set.mem_range_self j)
  have hk' : (U k).1 = (U i).1 ⊓ (U j).1 := congrArg Subtype.val hk
  rw [← hk']
  exact hpc k

private theorem indexedCover_inf_inf_pathConnected
    (x : X) (U : ι → OpenNhds (X := TopCat.of X) x)
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) (i j k : ι) :
    IsPathConnected (↑(((U i).1 ⊓ (U j).1) ⊓ (U k).1) : Set X) := by
  obtain ⟨l, hl⟩ := hclosed (Set.mem_range_self i) (Set.mem_range_self j)
  have hl' : (U l).1 = (U i).1 ⊓ (U j).1 := congrArg Subtype.val hl
  rw [← hl']
  exact indexedCover_inf_pathConnected x U hpc hclosed l k

/-- The homomorphism universal property for an intersection-closed open cover at a common point.

The neighborhoods are path connected and cover the space. Closure under binary intersections
is equivalent here to closure under nonempty finite intersections; neither index finiteness nor
membership of the whole space is required. Compatibility is imposed along every inclusion of
presented neighborhoods, including inclusions between repeated presentations of the same open.
The target group may lie in a universe independent of the space and the index type.

See May, *A Concise Course in Algebraic Topology*, Chapter 2, §7. -/
theorem existsUnique_hom_of_isOpenCover_of_infClosed
    (x : X) (U : ι → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U))
    (G : Type w) [Group G]
    (φ : ∀ i, FundamentalGroup (U i).1 ⟨x, (U i).2⟩ →* G)
    (hφ : ∀ (i j : ι) (hij : U i ≤ U j),
      (φ j).comp (((openNhdsFunctor x).map (homOfLE hij)).hom) = φ i) :
    ∃! ψ : FundamentalGroup X x →* G,
      ∀ i, ψ.comp (((openNhdsCocone x).ι.app (U i)).hom) = φ i := by
  classical
  let V : ι → Opens X := fun i => (U i).1
  let p (i : ι) : V i := ⟨x, (U i).2⟩
  let : PathConnectedSpace X := indexedCover_pathConnectedSpace x U hcover hpc
  let (i : ι) : PathConnectedSpace (V i) :=
    isPathConnected_iff_pathConnectedSpace.mp (hpc i)
  let T (i : ι) : FundamentalGroupoid (V i) ⥤ SingleObj G :=
    frameHomFunctor (FundamentalGroupoid.mk (p i))
      (normalizedFrame (FundamentalGroupoid.mk (p i))) (φ i)
  have hT (i : ι) : vertexHom (FundamentalGroupoid.mk (p i)) (T i) = φ i :=
    vertexHom_frameHomFunctor _ _ (normalizedFrame_unit _) _
  let l (i j : ι) : C(↑(V i ⊓ V j), V i) :=
    ContinuousMap.inclusion Set.inter_subset_left
  let r (i j : ι) : C(↑(V i ⊓ V j), V j) :=
    ContinuousMap.inclusion Set.inter_subset_right
  let b (i j : ι) : ↑(V i ⊓ V j) := ⟨x, (U i).2, (U j).2⟩
  have hpair (i j : ι) :
      (φ i).comp (map (l i j) (b i j)) = (φ j).comp (map (r i j) (b i j)) := by
    obtain ⟨k, hk⟩ := hclosed (Set.mem_range_self i) (Set.mem_range_self j)
    have hki : U k ≤ U i := by rw [hk]; exact inf_le_left
    have hkj : U k ≤ U j := by rw [hk]; exact inf_le_right
    exact homs_agree_on_inf x (U i) (U j) (U k) hki hkj hk
      (φ i) (φ j) (φ k) (hφ k i hki) (hφ k j hkj)
  have hvertex (i j : ι) :
      vertexHom (FundamentalGroupoid.mk (b i j)) (FundamentalGroupoid.map (l i j) ⋙ T i) =
        vertexHom (FundamentalGroupoid.mk (b i j))
          (FundamentalGroupoid.map (r i j) ⋙ T j) := by
    calc
      _ = (vertexHom (FundamentalGroupoid.mk (p i)) (T i)).comp
          (map (l i j) (b i j)) := (vertexHom_comp _ _ _).symm
      _ = (vertexHom (FundamentalGroupoid.mk (p j)) (T j)).comp
          (map (r i j) (b i j)) := by rw [hT i, hT j]; exact hpair i j
      _ = _ := vertexHom_comp _ _ _
  let α (i j : ι) : FundamentalGroupoid.map (l i j) ⋙ T i ≅
      FundamentalGroupoid.map (r i j) ⋙ T j := by
    letI : PathConnectedSpace ↑(V i ⊓ V j) :=
      isPathConnected_iff_pathConnectedSpace.mp
        (indexedCover_inf_pathConnected x U hpc hclosed i j)
    exact vertexIso (FundamentalGroupoid.mk (b i j)) _ _ (hvertex i j)
  have hα (i j : ι) : ((α i j).hom.app (FundamentalGroupoid.mk (b i j)) : G) = 1 := by
    let : PathConnectedSpace ↑(V i ⊓ V j) :=
      isPathConnected_iff_pathConnectedSpace.mp
        (indexedCover_inf_pathConnected x U hpc hclosed i j)
    exact vertexIso_base _ _ _ (hvertex i j)
  -- A single path in the triple intersection computes all three comparisons.
  -- Their normalized components consequently satisfy the cocycle equation.
  have hcocycle (i j k : ι) (y : X) (hi : y ∈ V i) (hj : y ∈ V j) (hk : y ∈ V k) :
      ((α j k).hom.app (FundamentalGroupoid.mk ⟨y, hj, hk⟩) : G) *
          (α i j).hom.app (FundamentalGroupoid.mk ⟨y, hi, hj⟩) =
        (α i k).hom.app (FundamentalGroupoid.mk ⟨y, hi, hk⟩) := by
    let W : Opens X := (V i ⊓ V j) ⊓ V k
    let : PathConnectedSpace W := isPathConnected_iff_pathConnectedSpace.mp
      (indexedCover_inf_inf_pathConnected x U hpc hclosed i j k)
    let a : W := ⟨x, ⟨(U i).2, (U j).2⟩, (U k).2⟩
    let z : W := ⟨y, ⟨hi, hj⟩, hk⟩
    let q : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk z :=
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath a z)
    let qi : C(W, V i) := ContinuousMap.inclusion (fun _ h => h.1.1)
    let qj : C(W, V j) := ContinuousMap.inclusion (fun _ h => h.1.2)
    let qk : C(W, V k) := ContinuousMap.inclusion (fun _ h => h.2)
    let qij : C(W, ↑(V i ⊓ V j)) := ContinuousMap.inclusion (fun _ h => h.1)
    let qjk : C(W, ↑(V j ⊓ V k)) := ContinuousMap.inclusion (fun _ h => ⟨h.1.2, h.2⟩)
    let qik : C(W, ↑(V i ⊓ V k)) := ContinuousMap.inclusion (fun _ h => ⟨h.1.1, h.2⟩)
    let ti : G := (T i).map ((FundamentalGroupoid.map qi).map q)
    let tj : G := (T j).map ((FundamentalGroupoid.map qj).map q)
    let tk : G := (T k).map ((FundamentalGroupoid.map qk).map q)
    have hij : ((α i j).hom.app (FundamentalGroupoid.mk ⟨y, hi, hj⟩) : G) = tj * ti⁻¹ := by
      have h := normalizedNatTrans_app (FundamentalGroupoid.mk (b i j))
        (α i j).hom (hα i j) ((FundamentalGroupoid.map qij).map q)
      change @Eq G _ _ at h
      simp only [FundamentalGroupoid.map_map, l, r, qij] at h
      change @Eq G ((α i j).hom.app (FundamentalGroupoid.mk ⟨y, hi, hj⟩))
        (tj * ti⁻¹) at h
      exact h
    have hjk : ((α j k).hom.app (FundamentalGroupoid.mk ⟨y, hj, hk⟩) : G) = tk * tj⁻¹ := by
      have h := normalizedNatTrans_app (FundamentalGroupoid.mk (b j k))
        (α j k).hom (hα j k) ((FundamentalGroupoid.map qjk).map q)
      change @Eq G _ _ at h
      simp only [FundamentalGroupoid.map_map, l, r, qjk] at h
      change @Eq G ((α j k).hom.app (FundamentalGroupoid.mk ⟨y, hj, hk⟩))
        (tk * tj⁻¹) at h
      exact h
    have hik : ((α i k).hom.app (FundamentalGroupoid.mk ⟨y, hi, hk⟩) : G) = tk * ti⁻¹ := by
      have h := normalizedNatTrans_app (FundamentalGroupoid.mk (b i k))
        (α i k).hom (hα i k) ((FundamentalGroupoid.map qik).map q)
      change @Eq G _ _ at h
      simp only [FundamentalGroupoid.map_map, l, r, qik] at h
      change @Eq G ((α i k).hom.app (FundamentalGroupoid.mk ⟨y, hi, hk⟩))
        (tk * ti⁻¹) at h
      exact h
    rw [hij, hjk, hik]
    simp [mul_assoc]
  choose c hc using (fun y : X => hcover.exists_mem y)
  let e (i : ι) (y : FundamentalGroupoid (V i)) : G :=
    (α i (c y.as.1)).hom.app (FundamentalGroupoid.mk ⟨y.as.1, y.as.2, hc y.as.1⟩)
  have he (i j : ι) (y : ↑(V i ⊓ V j)) :
      e i (FundamentalGroupoid.mk ⟨y.1, y.2.1⟩) =
        e j (FundamentalGroupoid.mk ⟨y.1, y.2.2⟩) *
          (α i j).hom.app (FundamentalGroupoid.mk y) :=
    (hcocycle i j (c y.1) y.1 y.2.1 y.2.2 (hc y.1)).symm
  have he_base (i : ι) : e i (FundamentalGroupoid.mk (p i)) = 1 := hα i (c x)
  let T' (i : ι) : FundamentalGroupoid (V i) ⥤ SingleObj G :=
    (T i).copyObj (fun _ => SingleObj.star G) (fun y => singleObjIso (e i y))
  have hT' (i : ι) : vertexHom (FundamentalGroupoid.mk (p i)) (T' i) = φ i :=
    (vertexHom_copyObj _ _ _ _ (he_base i)).trans (hT i)
  have hstrict : ∀ i j,
      (FundamentalGroupoid.openCoverDiagram V).map (Pairwise.Hom.left i j) ⋙ T' i =
        (FundamentalGroupoid.openCoverDiagram V).map (Pairwise.Hom.right i j) ⋙ T' j := by
    intro i j
    rw [FundamentalGroupoid.openCoverDiagram_map_left,
      FundamentalGroupoid.openCoverDiagram_map_right]
    change (FundamentalGroupoid.map (l i j) ⋙ T' i :
      FundamentalGroupoid ↑(V i ⊓ V j) ⥤ SingleObj G) =
        FundamentalGroupoid.map (r i j) ⋙ T' j
    apply singleObjFunctor_ext (C := FundamentalGroupoid ↑(V i ⊓ V j))
    intro a z f
    change @Eq G ((T' i).map ((FundamentalGroupoid.map (l i j)).map f))
      ((T' j).map ((FundamentalGroupoid.map (r i j)).map f))
    simp only [T', singleObj_copyObj_map, groupoid_map_obj]
    change @Eq G
      (e i (FundamentalGroupoid.mk ⟨z.as.1, z.as.2.1⟩) *
        ((T i).map ((FundamentalGroupoid.map (l i j)).map f) : G) *
        (e i (FundamentalGroupoid.mk ⟨a.as.1, a.as.2.1⟩))⁻¹)
      (e j (FundamentalGroupoid.mk ⟨z.as.1, z.as.2.2⟩) *
        ((T j).map ((FundamentalGroupoid.map (r i j)).map f) : G) *
        (e j (FundamentalGroupoid.mk ⟨a.as.1, a.as.2.2⟩))⁻¹)
    rw [he i j z.as, he i j a.as]
    have hn := (α i j).hom.naturality f
    change ((α i j).hom.app z : G) * (T i).map ((FundamentalGroupoid.map (l i j)).map f) =
      (T j).map ((FundamentalGroupoid.map (r i j)).map f) * (α i j).hom.app a at hn
    calc
      _ = e j (FundamentalGroupoid.mk ⟨z.as.1, z.as.2.2⟩) *
          ((α i j).hom.app z * (T i).map ((FundamentalGroupoid.map (l i j)).map f)) *
          ((α i j).hom.app a)⁻¹ * (e j (FundamentalGroupoid.mk ⟨a.as.1, a.as.2.2⟩))⁻¹ := by
        simp [mul_assoc, mul_inv_rev]
      _ = _ := by rw [hn]; simp [mul_assoc]
  let D := FundamentalGroupoid.descOfIsOpenCover hcover T' hstrict
  let ψ : FundamentalGroup X x →* G := vertexHom (FundamentalGroupoid.mk x) D
  have hψ (i : ι) : ψ.comp (((openNhdsCocone x).ι.app (U i)).hom) = φ i := by
    calc
      _ = vertexHom (FundamentalGroupoid.mk (p i))
          (FundamentalGroupoid.map (ContinuousMap.subtypeVal (V i : Set X)) ⋙ D) :=
        vertexHom_comp _ _ _
      _ = vertexHom (FundamentalGroupoid.mk (p i)) (T' i) :=
        congrArg (vertexHom (FundamentalGroupoid.mk (p i)))
          (FundamentalGroupoid.inclusion_comp_descOfIsOpenCover hcover T' hstrict i)
      _ = φ i := hT' i
  refine ⟨ψ, hψ, ?_⟩
  intro χ hχ
  let K : FundamentalGroupoid X ⥤ SingleObj G :=
    frameHomFunctor (FundamentalGroupoid.mk x) (normalizedFrame (FundamentalGroupoid.mk x)) χ
  have hK : vertexHom (FundamentalGroupoid.mk x) K = χ :=
    vertexHom_frameHomFunctor _ _ (normalizedFrame_unit _) _
  let J (i : ι) := FundamentalGroupoid.map (ContinuousMap.subtypeVal (V i : Set X))
  have hlocal (i : ι) :
      vertexHom (FundamentalGroupoid.mk (p i)) (J i ⋙ K) =
        vertexHom (FundamentalGroupoid.mk (p i)) (J i ⋙ D) := by
    calc
      _ = (vertexHom (FundamentalGroupoid.mk x) K).comp
          (map (ContinuousMap.subtypeVal (V i : Set X)) (p i)) :=
        (vertexHom_comp _ _ _).symm
      _ = φ i := by rw [hK]; exact hχ i
      _ = ψ.comp (map (ContinuousMap.subtypeVal (V i : Set X)) (p i)) := (hψ i).symm
      _ = _ := vertexHom_comp _ _ _
  let β (i : ι) : J i ⋙ K ≅ J i ⋙ D :=
    vertexIso (FundamentalGroupoid.mk (p i)) _ _ (hlocal i)
  have hβ (i : ι) : ((β i).hom.app (FundamentalGroupoid.mk (p i)) : G) = 1 :=
    vertexIso_base _ _ _ (hlocal i)
  -- On an overlap both comparisons are determined by the image of a path in
  -- that overlap, whose two images in the ambient space are equal.
  have hβ_overlap (i j : ι) (y : ↑(V i ⊓ V j)) :
      ((β i).hom.app (FundamentalGroupoid.mk ⟨y.1, y.2.1⟩) : G) =
        (β j).hom.app (FundamentalGroupoid.mk ⟨y.1, y.2.2⟩) := by
    let : PathConnectedSpace ↑(V i ⊓ V j) :=
      isPathConnected_iff_pathConnectedSpace.mp
        (indexedCover_inf_pathConnected x U hpc hclosed i j)
    let q : FundamentalGroupoid.mk (b i j) ⟶ FundamentalGroupoid.mk y :=
      Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (b i j) y)
    let dq : G := D.map ((FundamentalGroupoid.map
      (ContinuousMap.subtypeVal (↑(V i ⊓ V j) : Set X))).map q)
    let kq : G := K.map ((FundamentalGroupoid.map
      (ContinuousMap.subtypeVal (↑(V i ⊓ V j) : Set X))).map q)
    have hi := normalizedNatTrans_app (FundamentalGroupoid.mk (p i))
      (β i).hom (hβ i) ((FundamentalGroupoid.map (l i j)).map q)
    have hj := normalizedNatTrans_app (FundamentalGroupoid.mk (p j))
      (β j).hom (hβ j) ((FundamentalGroupoid.map (r i j)).map q)
    change @Eq G _ _ at hi
    simp only [FundamentalGroupoid.map_map, J, l] at hi
    change @Eq G ((β i).hom.app (FundamentalGroupoid.mk ⟨y.1, y.2.1⟩))
      (dq * kq⁻¹) at hi
    change @Eq G _ _ at hj
    simp only [FundamentalGroupoid.map_map, J, r] at hj
    change @Eq G ((β j).hom.app (FundamentalGroupoid.mk ⟨y.1, y.2.2⟩))
      (dq * kq⁻¹) at hj
    exact hi.trans hj.symm
  let d (y : FundamentalGroupoid X) : G :=
    (β (c y.as)).hom.app (FundamentalGroupoid.mk ⟨y.as, hc y.as⟩)
  have hd (i : ι) (y : FundamentalGroupoid (V i)) :
      d ((J i).obj y) = (β i).hom.app y :=
    (hβ_overlap i (c y.as.1) ⟨y.as.1, y.as.2, hc y.as.1⟩).symm
  have hd_base : d (FundamentalGroupoid.mk x) = 1 := hβ (c x)
  let K' : FundamentalGroupoid X ⥤ SingleObj G :=
    K.copyObj D.obj (fun y => singleObjIso (d y))
  have hK' (i : ι) : J i ⋙ K' = T' i := by
    have hKD : J i ⋙ K' = J i ⋙ D := by
      apply singleObjFunctor_ext
      intro a z f
      change ((K').map ((J i).map f) : G) = D.map ((J i).map f)
      simp only [K', singleObj_copyObj_map, hd i]
      have hn := (β i).hom.naturality f
      change ((β i).hom.app z : G) * K.map ((J i).map f) =
        D.map ((J i).map f) * (β i).hom.app a at hn
      rw [hn]
      simp [mul_assoc]
    exact hKD.trans (FundamentalGroupoid.inclusion_comp_descOfIsOpenCover hcover T' hstrict i)
  calc
    χ = vertexHom (FundamentalGroupoid.mk x) K := hK.symm
    _ = vertexHom (FundamentalGroupoid.mk x) K' :=
      (vertexHom_copyObj _ _ _ _ hd_base).symm
    _ = vertexHom (FundamentalGroupoid.mk x) D :=
      congrArg (vertexHom (FundamentalGroupoid.mk x))
        (FundamentalGroupoid.descOfIsOpenCover_unique hcover T' hstrict K' hK')
    _ = ψ := rfl

/-- The inclusion cocone of an intersection-closed path-connected open cover is a colimit.

The diagram is the restriction of the fundamental-group functor on neighborhoods along the
induced inclusion category. Its homomorphism universal property, including target groups
in an independent universe, is `existsUnique_hom_of_isOpenCover_of_infClosed`.

See May, *A Concise Course in Algebraic Topology*, Chapter 2, §7. -/
noncomputable def isColimitOfIsOpenCover
    (x : X) (U : ι → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) :
    IsColimit ((openNhdsCocone x).whisker (inducedFunctor U)) := by
  classical
  have hup : ∀ s : Cocone (inducedFunctor U ⋙ openNhdsFunctor x),
      ∃! ψ : FundamentalGroup X x →* (s.pt : Type u),
        ∀ i, ψ.comp (((openNhdsCocone x).ι.app (U i)).hom) = (s.ι.app i).hom := by
    intro s
    apply existsUnique_hom_of_isOpenCover_of_infClosed x U hcover hpc hclosed
      (s.pt : Type u) (fun i => (s.ι.app i).hom)
    intro i j hij
    have hw := congrArg GrpCat.Hom.hom
      (s.w (InducedCategory.homMk (homOfLE hij)))
    -- Normalize the source groups as well as the maps in the cocone identity.
    dsimp only [Functor.comp_obj, inducedFunctor_obj, openNhdsFunctor_obj,
      Functor.comp_map, inducedFunctor_map, InducedCategory.homMk_hom,
      GrpCat.hom_comp, openNhdsFunctor_map_hom] at hw ⊢
    change
      ((s.ι.app j).hom :
        FundamentalGroup (U j).1 ⟨x, (U j).2⟩ →* (s.pt : Type u)).comp
          (map (ContinuousMap.inclusion (s := ((U i).1 : Set X))
            (t := ((U j).1 : Set X)) hij) ⟨x, (U i).2⟩) =
        (s.ι.app i).hom at hw
    exact hw
  refine
    { desc := fun s => GrpCat.ofHom (Classical.choose (hup s))
      fac := ?_
      uniq := ?_ }
  · intro s i
    apply GrpCat.hom_ext
    have hfac := (Classical.choose_spec (hup s)).1 i
    dsimp only [Functor.comp_obj, inducedFunctor_obj, openNhdsFunctor_obj,
      Cocone.whisker_pt, Cocone.whisker_ι, Functor.whiskerLeft_app,
      openNhdsCocone_pt, GrpCat.hom_comp, GrpCat.hom_ofHom,
      openNhdsCocone_ι_app_hom] at hfac ⊢
    change (Classical.choose (hup s)).comp
        (map (ContinuousMap.subtypeVal ((U i).1 : Set X)) ⟨x, (U i).2⟩) =
      (s.ι.app i).hom at hfac
    exact hfac
  · intro s m hm
    apply GrpCat.hom_ext
    apply (Classical.choose_spec (hup s)).2 m.hom
    intro i
    have hfac := congrArg GrpCat.Hom.hom (hm i)
    dsimp only [Functor.comp_obj, inducedFunctor_obj, openNhdsFunctor_obj,
      Cocone.whisker_pt, Cocone.whisker_ι, Functor.whiskerLeft_app,
      openNhdsCocone_pt, GrpCat.hom_comp, openNhdsCocone_ι_app_hom] at hfac ⊢
    change (m.hom : FundamentalGroup X x →* (s.pt : Type u)).comp
        (map (ContinuousMap.subtypeVal ((U i).1 : Set X)) ⟨x, (U i).2⟩) =
      (s.ι.app i).hom at hfac
    exact hfac

-- The deprecated spelling is retained for downstream compatibility.
@[deprecated (since := "2026-10-20"), nolint defsWithUnderscore]
alias isColimit_of_isOpenCover := isColimitOfIsOpenCover

end IndexedCover

section CommonOverlap

variable {I : Type v}

-- The arbitrary family need not preserve infima, so the range-of-inf-hom lemma
-- does not apply. Adjoining the common infimum supplies every missing intersection.
private theorem infClosed_range_option_of_common_inf
    {α : Type*} [SemilatticeInf α] (c : α) (f : I → α)
    (hcf : ∀ i, c ≤ f i) (hinf : ∀ i j, i ≠ j → f i ⊓ f j = c) :
    InfClosed (Set.range (fun o : Option I => o.elim c f)) := by
  classical
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  cases i with
  | none =>
    cases j with
    | none => exact ⟨none, (inf_idem c).symm⟩
    | some j => exact ⟨none, (inf_eq_left.mpr (hcf j)).symm⟩
  | some i =>
    cases j with
    | none => exact ⟨none, (inf_eq_right.mpr (hcf i)).symm⟩
    | some j =>
      by_cases hij : i = j
      · subst j
        exact ⟨some i, (inf_idem (f i)).symm⟩
      · exact ⟨none, (hinf i j hij).symm⟩

-- When a presented neighborhood lies below the core, its inclusion into the
-- core is inverse to the core inclusion. Proof irrelevance identifies all
-- presentations of the resulting inclusion into the target neighborhood.
private theorem hom_comp_of_le_core
    (x : X) (C A B : OpenNhds (X := TopCat.of X) x)
    (hCA : C ≤ A) (hCB : C ≤ B) (hAC : A ≤ C) (hAB : A ≤ B)
    {G : Type w} [Group G]
    (fC : FundamentalGroup C.1 ⟨x, C.2⟩ →* G)
    (fA : FundamentalGroup A.1 ⟨x, A.2⟩ →* G)
    (fB : FundamentalGroup B.1 ⟨x, B.2⟩ →* G)
    (hA : fA.comp (((openNhdsFunctor x).map (homOfLE hCA)).hom) = fC)
    (hB : fB.comp (((openNhdsFunctor x).map (homOfLE hCB)).hom) = fC) :
    fB.comp (((openNhdsFunctor x).map (homOfLE hAB)).hom) = fA := by
  have hAC' : A = C := le_antisymm hAC hCA
  subst A
  have hfA : fA = fC := by
    change fA.comp (((openNhdsFunctor x).map (𝟙 C)).hom) = fC at hA
    rw [(openNhdsFunctor x).map_id C] at hA
    exact hA
  exact hB.trans hfA.symm

/-- Homomorphisms from a common-overlap open cover glue uniquely to the ambient
fundamental group.

The core and each member are path connected, and adjoining the core gives an open
cover. Distinct indices intersect in the core. Only compatibility along the core
inclusions is required, even when the family is empty or an open set is presented
more than once. All maps are induced by the actual subspace inclusions. The target
group, index type and ambient space may lie in independent universes.

This is the common-overlap specialization of the intersection-closed cover theorem;
see May, *A Concise Course in Algebraic Topology*, Chapter 2, §7. -/
theorem existsUnique_hom_of_isOpenCover_of_commonOverlap
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x)
    (hCU : ∀ i, C ≤ U i)
    (hinter : ∀ i j, i ≠ j → U i ⊓ U j = C)
    (hcover : IsOpenCover (fun o : Option I => (o.elim C U).1))
    (hpcC : IsPathConnected (C.1 : Set X))
    (hpcU : ∀ i, IsPathConnected ((U i).1 : Set X))
    (G : Type w) [Group G]
    (hC : FundamentalGroup C.1 ⟨x, C.2⟩ →* G)
    (hU : ∀ i, FundamentalGroup (U i).1 ⟨x, (U i).2⟩ →* G)
    (hcomp : ∀ i,
      (hU i).comp (((openNhdsFunctor x).map (homOfLE (hCU i))).hom) = hC) :
    ∃! h : FundamentalGroup X x →* G,
      h.comp (((openNhdsCocone x).ι.app C).hom) = hC ∧
        ∀ i, h.comp (((openNhdsCocone x).ι.app (U i)).hom) = hU i := by
  classical
  let V : Option I → OpenNhds (X := TopCat.of X) x := fun o => o.elim C U
  let φ : ∀ o, FundamentalGroup (V o).1 ⟨x, (V o).2⟩ →* G
    | none => hC
    | some i => hU i
  have hpc : ∀ o, IsPathConnected ((V o).1 : Set X) := by
    intro o
    cases o with
    | none => exact hpcC
    | some i => exact hpcU i
  have hφ : ∀ i j (hij : V i ≤ V j),
      (φ j).comp (((openNhdsFunctor x).map (homOfLE hij)).hom) = φ i := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none =>
        change hC.comp (((openNhdsFunctor x).map (𝟙 C)).hom) = hC
        rw [(openNhdsFunctor x).map_id C]
        exact MonoidHom.comp_id hC
      | some j => exact hcomp j
    | some i =>
      cases j with
      | none =>
        exact hom_comp_of_le_core x C (U i) C (hCU i) le_rfl hij hij
          hC (hU i) hC (hcomp i) (by
            change hC.comp (((openNhdsFunctor x).map (𝟙 C)).hom) = hC
            rw [(openNhdsFunctor x).map_id C]
            exact MonoidHom.comp_id hC)
      | some j =>
        by_cases heq : i = j
        · subst j
          change (hU i).comp (((openNhdsFunctor x).map (𝟙 (U i))).hom) = hU i
          rw [(openNhdsFunctor x).map_id (U i)]
          exact MonoidHom.comp_id (hU i)
        · have hUi : U i ≤ C := by
            rw [← hinter i j heq]
            exact le_inf le_rfl hij
          exact hom_comp_of_le_core x C (U i) (U j) (hCU i) (hCU j) hUi hij
            hC (hU i) (hU j) (hcomp i) (hcomp j)
  obtain ⟨h, hh, huniq⟩ := existsUnique_hom_of_isOpenCover_of_infClosed x V
    hcover hpc (infClosed_range_option_of_common_inf C U hCU hinter) G φ hφ
  refine ⟨h, ⟨hh none, fun i => hh (some i)⟩, ?_⟩
  intro g hg
  apply huniq g
  intro o
  cases o with
  | none => exact hg.1
  | some i => exact hg.2 i

/-- Homomorphisms out of the ambient fundamental group agree if their composites
with the core and all members of a common-overlap cover agree. -/
theorem hom_ext_of_isOpenCover_of_commonOverlap
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x)
    (hCU : ∀ i, C ≤ U i)
    (hinter : ∀ i j, i ≠ j → U i ⊓ U j = C)
    (hcover : IsOpenCover (fun o : Option I => (o.elim C U).1))
    (hpcC : IsPathConnected (C.1 : Set X))
    (hpcU : ∀ i, IsPathConnected ((U i).1 : Set X))
    {G : Type w} [Group G] {f g : FundamentalGroup X x →* G}
    (hC : f.comp (((openNhdsCocone x).ι.app C).hom) =
      g.comp (((openNhdsCocone x).ι.app C).hom))
    (hU : ∀ i, f.comp (((openNhdsCocone x).ι.app (U i)).hom) =
      g.comp (((openNhdsCocone x).ι.app (U i)).hom)) : f = g := by
  have hcomp (i : I) :
      (g.comp (((openNhdsCocone x).ι.app (U i)).hom)).comp
          (((openNhdsFunctor x).map (homOfLE (hCU i))).hom) =
        g.comp (((openNhdsCocone x).ι.app C).hom) := by
    have hleg := congrArg GrpCat.Hom.hom
      ((openNhdsCocone x).w (homOfLE (hCU i)))
    dsimp only [GrpCat.hom_comp] at hleg
    change g.comp ((((openNhdsCocone x).ι.app (U i)).hom).comp
      (((openNhdsFunctor x).map (homOfLE (hCU i))).hom)) = _
    exact congrArg (fun k => g.comp k) hleg
  obtain ⟨h, _, huniq⟩ := existsUnique_hom_of_isOpenCover_of_commonOverlap
    x C U hCU hinter hcover hpcC hpcU G
    (g.comp (((openNhdsCocone x).ι.app C).hom))
    (fun i => g.comp (((openNhdsCocone x).ι.app (U i)).hom)) hcomp
  exact (huniq f ⟨hC, hU⟩).trans (huniq g ⟨rfl, fun _ => rfl⟩).symm

end CommonOverlap

end FundamentalGroup
