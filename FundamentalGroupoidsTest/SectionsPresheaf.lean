/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.SectionsPresheaf
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Sections of representations on opens

Integer negation commutes with restriction from the real line to `(-∞, 1)`. The constant section
with value seven is constructed through the canonical sections equivalence and evaluates to negative
seven after restriction and negation.

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
