/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.SectionsPresheaf
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Sections of representations on opens

Integer negation commutes with restriction from the real line to `(-∞, 1)`. The constant section
with value seven is constructed through the canonical sections equivalence and evaluates to negative
seven after restriction and negation.

The constant-seven families on `(-∞, 1)` and `(0, +∞)` glue uniquely to the constant-seven
section on the real line.

The empty open has a unique section, including for the constant empty representation. On an open
with a specified point, a single empty fiber rules out sections.
-/

open CategoryTheory FundamentalGroupoid TopologicalSpace Opposite

namespace FundamentalGroupoidsTest.SectionsPresheaf

noncomputable section

private def integerRepresentation : FundamentalGroupoid ℝ ⥤ Type :=
  (Functor.const (FundamentalGroupoid ℝ)).obj ℤ

private def integerNegation : integerRepresentation ⟶ integerRepresentation :=
  (Functor.const (FundamentalGroupoid ℝ)).map (TypeCat.ofHom fun n : ℤ => -n)

private def leftRay : Opens ℝ := ⟨Set.Iio 1, isOpen_Iio⟩

private def leftRayInclusion : leftRay ⟶ (⊤ : Opens ℝ) := homOfLE le_top

private def origin : leftRay := ⟨0, by
  change (0 : ℝ) < 1
  exact zero_lt_one⟩

private def sevenSection (U : Opens ℝ) :
    ((sectionsPresheafFunctor ℝ).obj integerRepresentation).obj (op U) :=
  (sectionsPresheafSectionsEquiv integerRepresentation U).symm
    ⟨fun _ => (7 : ℤ), by intro a b γ; rfl⟩

private theorem negation_restricts_seven :
    let P := (sectionsPresheafFunctor ℝ).obj integerRepresentation
    let ν := (sectionsPresheafFunctor ℝ).map integerNegation
    P.map leftRayInclusion.op (ν.app (op ⊤) (sevenSection ⊤)) =
        ν.app (op leftRay) (P.map leftRayInclusion.op (sevenSection ⊤)) ∧
      (sectionsPresheafSectionsEquiv integerRepresentation leftRay
        (ν.app (op leftRay) (P.map leftRayInclusion.op (sevenSection ⊤)))).val
          (FundamentalGroupoid.mk origin) = (-7 : ℤ) := by
  dsimp only
  constructor
  · exact (((sectionsPresheafFunctor ℝ).map integerNegation).naturality_apply
      leftRayInclusion.op (sevenSection ⊤)).symm
  · rw [sectionsPresheafSectionsEquiv_apply_val, sectionsPresheafFunctor_map_app_val,
      sectionsPresheafFunctor_obj_map_val]
    change Neg.neg (α := ℤ) ((sevenSection ⊤).val
      (Set.inclusion (leOfHom leftRayInclusion) origin)) = (-7 : ℤ)
    simp only [sevenSection, sectionsPresheafSectionsEquiv_symm_apply_val]

private theorem sevenSection_unique_gluing :
    let P := (sectionsPresheafFunctor ℝ).obj integerRepresentation
    let rightRay : Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
    let rightRayInclusion : rightRay ⟶ (⊤ : Opens ℝ) := homOfLE le_top
    P.map leftRayInclusion.op (sevenSection ⊤) = sevenSection leftRay ∧
      P.map rightRayInclusion.op (sevenSection ⊤) = sevenSection rightRay ∧
      ∀ s : P.obj (op (⊤ : Opens ℝ)),
        P.map leftRayInclusion.op s = sevenSection leftRay →
        P.map rightRayInclusion.op s = sevenSection rightRay →
        s = sevenSection ⊤ := by
  dsimp only
  let P := (sectionsPresheafFunctor ℝ).obj integerRepresentation
  let rightRay : Opens ℝ := ⟨Set.Ioi 0, isOpen_Ioi⟩
  let U : Bool → Opens ℝ := fun i => if i then rightRay else leftRay
  let inclusions : ∀ i : Bool, U i ⟶ (⊤ : Opens ℝ) := fun _ => homOfLE le_top
  have hcover : (⊤ : Opens ℝ) ≤ iSup U := by
    intro x _
    apply Opens.mem_iSup.mpr
    by_cases hx : x < 1
    · exact ⟨false, hx⟩
    · exact ⟨true, lt_of_lt_of_le zero_lt_one (le_of_not_gt hx)⟩
  have restrict_seven {V W : Opens ℝ} (i : V ⟶ W) :
      P.map i.op (sevenSection W) = sevenSection V := by
    apply Subtype.ext
    funext x
    simp only [P, sectionsPresheafFunctor_obj_map_val, sevenSection,
      sectionsPresheafSectionsEquiv_symm_apply_val]
    rfl
  have compatible :
      TopCat.Presheaf.IsCompatible (C := Type) (X := TopCat.of ℝ) P U
        (fun i => sevenSection (U i)) := by
    intro i j
    exact
      (restrict_seven (Opens.infLELeft (X := TopCat.of ℝ) (U i) (U j))).trans
        (restrict_seven (Opens.infLERight (X := TopCat.of ℝ) (U i) (U j))).symm
  let S : TopCat.Sheaf (Type) (TopCat.of ℝ) :=
    ⟨P, sectionsPresheafFunctor_obj_isSheaf integerRepresentation⟩
  obtain ⟨s, hs, huniq⟩ := S.existsUnique_gluing' U (⊤ : Opens ℝ) inclusions hcover
    (fun i => sevenSection (U i)) compatible
  have hseven : ∀ i : Bool,
      P.map (inclusions i).op (sevenSection ⊤) = sevenSection (U i) :=
    fun i => restrict_seven (inclusions i)
  have hs_eq : s = sevenSection ⊤ := (huniq _ hseven).symm
  refine ⟨?_, ?_, ?_⟩
  · simpa [S, P, U, inclusions, leftRayInclusion, hs_eq] using hs false
  · simpa [S, P, U, inclusions, hs_eq] using hs true
  · intro t hleft hright
    refine (huniq t ?_).trans hs_eq
    intro i
    cases i with
    | false => exact hleft
    | true => exact hright

universe u w

private abbrev emptyOpenUnique {X : Type u} [TopologicalSpace X]
    (F : FundamentalGroupoid X ⥤ Type w) :
    Unique (((sectionsPresheafFunctor X).obj F).obj (op (⊥ : Opens X))) where
  default := by
    change (TopCat.subpresheafToTypes (sectionsPrelocal F)).obj (op (⊥ : Opens X))
    refine ⟨fun x => False.elim (Opens.mem_bot.mp x.property), ?_⟩
    rw [sectionsPrelocal_pred_iff]
    intro a b γ
    exact False.elim (Opens.mem_bot.mp a.as.property)
  uniq s := by
    apply Subtype.ext
    funext x
    exact False.elim (Opens.mem_bot.mp x.property)

private abbrev emptyFiberEmptyOpenUnique :
    Unique (((sectionsPresheafFunctor ℝ).obj
      ((Functor.const (FundamentalGroupoid ℝ)).obj Empty)).obj (op (⊥ : Opens ℝ))) :=
  emptyOpenUnique _

private theorem emptyFiber_no_section {X : Type u} [TopologicalSpace X]
    (F : FundamentalGroupoid X ⥤ Type w) (U : Opens X) (x : U)
    [IsEmpty (F.obj (FundamentalGroupoid.mk (x : X)))] :
    IsEmpty (((sectionsPresheafFunctor X).obj F).obj (op U)) :=
  ⟨fun s => isEmptyElim (s.val x)⟩

end

end FundamentalGroupoidsTest.SectionsPresheaf
