/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic

/-!
# A circle cylinder with two proper open strips

The strips of heights `t < 1` and `-1 < t` cover `AddCircle 1 × ℝ`. Both strips and their
intersection are path connected. Projection to the circle has a zero-height section on each
of the four spaces. The quotient covering `ℝ → AddCircle 1` supplies a specified nonidentity
circle class, whose four section images remain nonidentity and agree under all inclusions.

The geometric data, retractions, classes, and inclusion cocone below use only the existing
covering-space and fundamental-group APIs. In particular, their proofs do not use the
open-cover universal-property theorems. No orientation of the specified circle class is claimed.
-/

@[expose] public section

noncomputable section

universe v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CircleCylinderCover

private abbrev A := AddCircle (1 : ℝ)
private abbrev X := A × ℝ

private def U : Opens X :=
  ⟨{q | q.2 < 1}, isOpen_lt continuous_snd continuous_const⟩

private def V : Opens X :=
  ⟨{q | -1 < q.2}, isOpen_lt continuous_const continuous_snd⟩

private abbrev I := U ⊓ V

private def p : I := ⟨(0, 0), by constructor <;> norm_num [U, V]⟩
private def pU : U := ⟨p.1, p.2.1⟩
private def pV : V := ⟨p.1, p.2.2⟩
private def pX : X := p.1

private theorem cover : U ⊔ V = ⊤ := by
  apply top_unique
  intro q _
  change q.2 < 1 ∨ -1 < q.2
  by_cases hq : q.2 < 1
  · exact Or.inl hq
  · exact Or.inr (by linarith)

private theorem proper : U ≠ ⊤ ∧ V ≠ ⊤ := by
  constructor
  · intro hU
    have h := congrArg (fun W : Opens X => ((0, 2) : X) ∈ W) hU
    norm_num [U] at h
  · intro hV
    have h := congrArg (fun W : Opens X => ((0, -2) : X) ∈ W) hV
    norm_num [V] at h

private theorem boundary_heights :
    ((0, -1) : X) ∈ U ∧ ((0, 1) : X) ∈ V ∧
      ((0, 1) : X) ∉ U ∧ ((0, -1) : X) ∉ V := by
  norm_num [U, V]

private theorem intersection_nonempty : (I : Set X).Nonempty := ⟨p.1, p.2⟩

private theorem pathConnected_U : IsPathConnected (U : Set X) := by
  have hU : (U : Set X) = Set.univ ×ˢ Set.Iio (1 : ℝ) := by
    ext q
    simp [U]
  rw [hU]
  exact (isPathConnected_univ : IsPathConnected (Set.univ : Set A)).prod
    ((convex_Iio (𝕜 := ℝ) (1 : ℝ)).isPathConnected ⟨0, by norm_num⟩)

private theorem pathConnected_V : IsPathConnected (V : Set X) := by
  have hV : (V : Set X) = Set.univ ×ˢ Set.Ioi (-1 : ℝ) := by
    ext q
    simp [V]
  rw [hV]
  exact (isPathConnected_univ : IsPathConnected (Set.univ : Set A)).prod
    ((convex_Ioi (𝕜 := ℝ) (-1 : ℝ)).isPathConnected ⟨0, by norm_num⟩)

private theorem pathConnected_I : IsPathConnected (I : Set X) := by
  have hI : (I : Set X) = Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    ext q
    simp [I, U, V, and_comm]
  rw [hI]
  exact (isPathConnected_univ : IsPathConnected (Set.univ : Set A)).prod
    ((convex_Ioo (𝕜 := ℝ) (-1 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩)

-- These are the four continuous inclusions used in the based open-cover statements.
private def iU : C(I, U) := ContinuousMap.inclusion Set.inter_subset_left
private def iV : C(I, V) := ContinuousMap.inclusion Set.inter_subset_right
private def jU : C(U, X) := ContinuousMap.subtypeVal (U : Set X)
private def jV : C(V, X) := ContinuousMap.subtypeVal (V : Set X)
private def jI : C(I, X) := ContinuousMap.subtypeVal (I : Set X)

private def rX : C(X, A) := ContinuousMap.fst
private def rU : C(U, A) := rX.comp jU
private def rV : C(V, A) := rX.comp jV
private def rI : C(I, A) := rX.comp jI

private def sX : C(A, X) :=
  (ContinuousMap.id A).prodMk (ContinuousMap.const A (0 : ℝ))

private def sU : C(A, U) where
  toFun z := ⟨(z, 0), by change (0 : ℝ) < 1; norm_num⟩
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk (by
    intro z
    change (0 : ℝ) < 1
    norm_num)

private def sV : C(A, V) where
  toFun z := ⟨(z, 0), by change (-1 : ℝ) < 0; norm_num⟩
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk (by
    intro z
    change (-1 : ℝ) < 0
    norm_num)

private def sI : C(A, I) where
  toFun z := ⟨(z, 0), by constructor <;> norm_num [U, V]⟩
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk (by
    intro z
    constructor <;> norm_num [U, V])

private theorem based_maps :
    iU p = pU ∧ iV p = pV ∧ jU pU = pX ∧ jV pV = pX ∧
      sI 0 = p ∧ sU 0 = pU ∧ sV 0 = pV ∧ sX 0 = pX ∧
      rI p = 0 ∧ rU pU = 0 ∧ rV pV = 0 ∧ rX pX = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem continuous_retractions :
    rI.comp sI = ContinuousMap.id A ∧ rU.comp sU = ContinuousMap.id A ∧
      rV.comp sV = ContinuousMap.id A ∧ rX.comp sX = ContinuousMap.id A :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem inclusion_equations :
    jU.comp iU = jI ∧ jV.comp iV = jI ∧
      iU.comp sI = sU ∧ iV.comp sI = sV ∧
      jU.comp sU = sX ∧ jV.comp sV = sX ∧
      rU.comp iU = rI ∧ rV.comp iV = rI ∧
      rX.comp jU = rU ∧ rX.comp jV = rV :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- The covering equivalence takes values in the opposite group.
private abbrev Γ := AddSubgroup.zmultiples (1 : ℝ)
private def η : Γ := ⟨1, AddSubgroup.mem_zmultiples (1 : ℝ)⟩

private theorem η_ne_zero : η ≠ 0 := by
  intro hη
  exact one_ne_zero (congrArg (fun z : Γ => (z : ℝ)) hη)

private def eπ : FundamentalGroup A (0 : A) ≃* (Multiplicative Γ)ᵐᵒᵖ :=
  (AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).fundamentalGroupEquiv
    (x := (0 : A)) ⟨(0 : ℝ), rfl⟩

private def h : FundamentalGroup A (0 : A) :=
  eπ.symm (MulOpposite.op (Multiplicative.ofAdd η))

private theorem h_ne_one : h ≠ 1 := by
  intro hh
  have he : MulOpposite.op (Multiplicative.ofAdd η) = 1 := by
    simpa only [h, MulEquiv.apply_symm_apply, map_one] using congrArg eπ hh
  exact η_ne_zero
    (congrArg (fun z : (Multiplicative Γ)ᵐᵒᵖ => Multiplicative.toAdd z.unop) he)

private def aI : FundamentalGroup I p := FundamentalGroup.map sI 0 h
private def aU : FundamentalGroup U pU := FundamentalGroup.map sU 0 h
private def aV : FundamentalGroup V pV := FundamentalGroup.map sV 0 h
private def aX : FundamentalGroup X pX := FundamentalGroup.map sX 0 h

-- Quotient induction proves the induced retraction laws without any open-cover result.
private theorem group_retractions :
    (FundamentalGroup.map rI p).comp (FundamentalGroup.map sI 0) = MonoidHom.id _ ∧
      (FundamentalGroup.map rU pU).comp (FundamentalGroup.map sU 0) = MonoidHom.id _ ∧
      (FundamentalGroup.map rV pV).comp (FundamentalGroup.map sV 0) = MonoidHom.id _ ∧
      (FundamentalGroup.map rX pX).comp (FundamentalGroup.map sX 0) = MonoidHom.id _ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply MonoidHom.ext
    intro q
    induction q using Path.Homotopic.Quotient.ind with
    | mk q => rfl

private theorem recovered_classes :
    FundamentalGroup.map rI p aI = h ∧ FundamentalGroup.map rU pU aU = h ∧
      FundamentalGroup.map rV pV aV = h ∧ FundamentalGroup.map rX pX aX = h :=
  ⟨DFunLike.congr_fun group_retractions.1 h,
    DFunLike.congr_fun group_retractions.2.1 h,
    DFunLike.congr_fun group_retractions.2.2.1 h,
    DFunLike.congr_fun group_retractions.2.2.2 h⟩

private theorem classes_ne_one : aI ≠ 1 ∧ aU ≠ 1 ∧ aV ≠ 1 ∧ aX ≠ 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ha
    have hr := recovered_classes.1
    rw [ha, map_one] at hr
    exact h_ne_one hr.symm
  · intro ha
    have hr := recovered_classes.2.1
    rw [ha, map_one] at hr
    exact h_ne_one hr.symm
  · intro ha
    have hr := recovered_classes.2.2.1
    rw [ha, map_one] at hr
    exact h_ne_one hr.symm
  · intro ha
    have hr := recovered_classes.2.2.2
    rw [ha, map_one] at hr
    exact h_ne_one hr.symm

private abbrev GI := GrpCat.of (FundamentalGroup I p)
private abbrev GU := GrpCat.of (FundamentalGroup U pU)
private abbrev GV := GrpCat.of (FundamentalGroup V pV)
private abbrev GX := GrpCat.of (FundamentalGroup X pX)

private def f : GI ⟶ GU := GrpCat.ofHom (FundamentalGroup.map iU p)
private def g : GI ⟶ GV := GrpCat.ofHom (FundamentalGroup.map iV p)
private def legU : GU ⟶ GX := GrpCat.ofHom (FundamentalGroup.map jU pU)
private def legV : GV ⟶ GX := GrpCat.ofHom (FundamentalGroup.map jV pV)
private def intersectionLeg : GI ⟶ GX := GrpCat.ofHom (FundamentalGroup.map jI p)

private theorem left_composite : f ≫ legU = intersectionLeg := by
  apply GrpCat.ext
  intro q
  change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map q iU) jU =
    Path.Homotopic.Quotient.map q jI
  exact (Path.Homotopic.Quotient.map_comp (p := q) (f := iU) (g := jU)).symm

private theorem right_composite : g ≫ legV = intersectionLeg := by
  apply GrpCat.ext
  intro q
  change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map q iV) jV =
    Path.Homotopic.Quotient.map q jI
  exact (Path.Homotopic.Quotient.map_comp (p := q) (f := iV) (g := jV)).symm

private def inclusionCocone : PushoutCocone f g :=
  PushoutCocone.mk legU legV (left_composite.trans right_composite.symm)

private theorem cocone_fields :
    inclusionCocone.pt = GX ∧ inclusionCocone.inl = legU ∧ inclusionCocone.inr = legV ∧
      inclusionCocone.ι.app WalkingSpan.zero = f ≫ inclusionCocone.inl ∧
      inclusionCocone.ι.app WalkingSpan.zero = intersectionLeg :=
  ⟨rfl, rfl, rfl, rfl, left_composite⟩

private theorem class_images :
    f aI = aU ∧ g aI = aV ∧ inclusionCocone.inl aU = aX ∧
      inclusionCocone.inr aV = aX := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map h sI) iU =
      Path.Homotopic.Quotient.map h sU
    exact (Path.Homotopic.Quotient.map_comp (p := h) (f := sI) (g := iU)).symm
  · change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map h sI) iV =
      Path.Homotopic.Quotient.map h sV
    exact (Path.Homotopic.Quotient.map_comp (p := h) (f := sI) (g := iV)).symm
  · change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map h sU) jU =
      Path.Homotopic.Quotient.map h sX
    exact (Path.Homotopic.Quotient.map_comp (p := h) (f := sU) (g := jU)).symm
  · change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.map h sV) jV =
      Path.Homotopic.Quotient.map h sX
    exact (Path.Homotopic.Quotient.map_comp (p := h) (f := sV) (g := jV)).symm

private theorem leg_images_ne_one :
    inclusionCocone.inl (f aI) ≠ 1 ∧ inclusionCocone.inr (g aI) ≠ 1 := by
  rw [class_images.1, class_images.2.1, class_images.2.2.1, class_images.2.2.2]
  exact ⟨classes_ne_one.2.2.2, classes_ne_one.2.2.2⟩

-- The proper open strips and their intersection are path connected; their classes
-- and their images under both cocone legs are nonidentity.
private theorem strip_model :
    U ≠ ⊤ ∧ V ≠ ⊤ ∧ U ⊔ V = ⊤ ∧ (I : Set X).Nonempty ∧
      IsPathConnected (U : Set X) ∧ IsPathConnected (V : Set X) ∧
      IsPathConnected (I : Set X) ∧
      aI ≠ 1 ∧ aU ≠ 1 ∧ aV ≠ 1 ∧ aX ≠ 1 ∧
      inclusionCocone.inl (f aI) ≠ 1 ∧ inclusionCocone.inr (g aI) ≠ 1 :=
  ⟨proper.1, proper.2, cover, intersection_nonempty,
    pathConnected_U, pathConnected_V, pathConnected_I,
    classes_ne_one.1, classes_ne_one.2.1, classes_ne_one.2.2.1, classes_ne_one.2.2.2,
    leg_images_ne_one.1, leg_images_ne_one.2⟩

private theorem hom_client (G : Type v) [Group G]
    (φU : FundamentalGroup U pU →* G) (φV : FundamentalGroup V pV →* G)
    (hcompat : φU.comp (FundamentalGroup.map iU p) =
      φV.comp (FundamentalGroup.map iV p)) :
    ∃! φ : FundamentalGroup X pX →* G,
      φ.comp (FundamentalGroup.map jU pU) = φU ∧
      φ.comp (FundamentalGroup.map jV pV) = φV :=
  FundamentalGroup.existsUnique_hom_of_isOpenCover U V cover
    pathConnected_U pathConnected_V pathConnected_I p G φU φV hcompat

private def pushout_client : IsColimit inclusionCocone :=
  (FundamentalGroup.isPushout_of_isOpenCover U V cover
    pathConnected_U pathConnected_V pathConnected_I p).isColimit

end CircleCylinderCover
