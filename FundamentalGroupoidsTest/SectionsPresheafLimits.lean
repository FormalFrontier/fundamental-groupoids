/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.SectionsPresheafLimits
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Types.Equalizers

/-!
# Products and equalizers on a point

The comparison identifies the product of two constant `Fin 2` coefficients with four
sections on the whole point space and one on the empty open. The equalizer of identity
and swap has no section on the whole space and one on the empty open.
-/

open CategoryTheory CategoryTheory.Limits FundamentalGroupoid TopologicalSpace Opposite

namespace FundamentalGroupoidsTest.SectionsPresheafLimits

noncomputable section

private instance : TopologicalSpace PUnit := ⊥

private def pointSectionsEquiv (A : Type) :
    (((sectionsPresheafFunctor PUnit).obj
      ((Functor.const (FundamentalGroupoid PUnit)).obj A)).obj (op ⊤)) ≃ A where
  toFun s := s.val ⟨PUnit.unit, by simp⟩
  invFun a := ⟨fun _ => a, by intro p q γ; rfl⟩
  left_inv s := by
    apply Subtype.ext
    funext x
    exact congrArg s.val (Subsingleton.elim _ _)
  right_inv _ := rfl

private def emptySectionsEquiv (F : FundamentalGroupoid PUnit ⥤ Type) :
    ((sectionsPresheafFunctor PUnit).obj F).obj (op ⊥) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := by
    refine ⟨fun x => False.elim (Opens.mem_bot.mp x.property), ?_⟩
    rw [sectionsPrelocal_pred_iff]
    intro a b γ
    exact False.elim (Opens.mem_bot.mp a.as.property)
  left_inv s := by
    apply Subtype.ext
    funext x
    exact False.elim (Opens.mem_bot.mp x.property)
  right_inv _ := Subsingleton.elim _ _

private def pairFourEquiv : (Fin 2 × Fin 2) ≃ Fin 4 := finProdFinEquiv

private def typeProduct : BinaryFan (Fin 2 : Type) (Fin 2 : Type) :=
  Types.binaryProductCone (Fin 2) (Fin 2)

private def typeProductIsLimit : IsLimit typeProduct :=
  Types.binaryProductLimit (Fin 2) (Fin 2)

private def productRepresentationIsLimit :
    IsLimit ((Functor.const (FundamentalGroupoid PUnit)).mapCone typeProduct) :=
  isLimitOfPreserves _ typeProductIsLimit

private def productDiagram : Discrete WalkingPair ⥤ (FundamentalGroupoid PUnit ⥤ Type) :=
  pair (Fin 2 : Type) (Fin 2 : Type) ⋙ Functor.const (FundamentalGroupoid PUnit)

private def productComparison :
    (sectionsPresheafFunctor PUnit).obj
        ((Functor.const (FundamentalGroupoid PUnit)).obj (Fin 2 × Fin 2)) ≅
      limit (productDiagram ⋙ sectionsPresheafFunctor PUnit) :=
  (sectionsPresheafFunctor PUnit).mapIso
      (productRepresentationIsLimit.conePointUniqueUpToIso (limit.isLimit productDiagram)) ≪≫
    preservesLimitIso (sectionsPresheafFunctor PUnit) productDiagram

private def productTopEquiv :
    (limit (productDiagram ⋙ sectionsPresheafFunctor PUnit)).obj (op ⊤) ≃ Fin 4 :=
  (productComparison.app (op ⊤)).toEquiv.symm.trans
    ((pointSectionsEquiv (Fin 2 × Fin 2)).trans pairFourEquiv)

private def productEmptyEquiv :
    (limit (productDiagram ⋙ sectionsPresheafFunctor PUnit)).obj (op ⊥) ≃ PUnit :=
  (productComparison.app (op ⊥)).toEquiv.symm.trans (emptySectionsEquiv _)

private theorem product_projection (j : Discrete WalkingPair)
    (s : ((sectionsPresheafFunctor PUnit).obj (limit productDiagram)).obj (op ⊤))
    (x : (⊤ : Opens PUnit)) :
    (((limit.π (productDiagram ⋙ sectionsPresheafFunctor PUnit) j).app (op ⊤))
      ((preservesLimitIso (sectionsPresheafFunctor PUnit) productDiagram).hom.app
        (op ⊤) s)).val x =
      (limit.π productDiagram j).app (mk (x : PUnit)) (s.val x) :=
  sectionsPresheafFunctor_preservesLimitIso_hom_app_π_val productDiagram j ⊤ s x

private def swap (b : Fin 2) : Fin 2 := if b = 0 then 1 else 0

private def swapMap : (Fin 2 : Type) ⟶ Fin 2 := TypeCat.ofHom swap

private def equalizerFiber := {b : Fin 2 // b = swap b}

private instance : IsEmpty equalizerFiber :=
  ⟨fun b => (show ∀ x : Fin 2, x ≠ swap x by decide) b.val b.property⟩

private def typeEqualizer : Fork (𝟙 (Fin 2 : Type)) swapMap :=
  (Types.equalizerLimit (g := 𝟙 (Fin 2 : Type)) (h := swapMap)).cone

private def typeEqualizerIsLimit : IsLimit typeEqualizer :=
  (Types.equalizerLimit (g := 𝟙 (Fin 2 : Type)) (h := swapMap)).isLimit

private def equalizerRepresentationIsLimit :
    IsLimit ((Functor.const (FundamentalGroupoid PUnit)).mapCone typeEqualizer) :=
  isLimitOfPreserves _ typeEqualizerIsLimit

private def equalizerDiagram : WalkingParallelPair ⥤ (FundamentalGroupoid PUnit ⥤ Type) :=
  parallelPair (𝟙 (Fin 2 : Type)) swapMap ⋙ Functor.const (FundamentalGroupoid PUnit)

private def equalizerComparison :
    (sectionsPresheafFunctor PUnit).obj
        ((Functor.const (FundamentalGroupoid PUnit)).obj equalizerFiber) ≅
      limit (equalizerDiagram ⋙ sectionsPresheafFunctor PUnit) :=
  (sectionsPresheafFunctor PUnit).mapIso
      (equalizerRepresentationIsLimit.conePointUniqueUpToIso (limit.isLimit equalizerDiagram)) ≪≫
    preservesLimitIso (sectionsPresheafFunctor PUnit) equalizerDiagram

private theorem equalizerTopIsEmpty :
    IsEmpty ((limit (equalizerDiagram ⋙ sectionsPresheafFunctor PUnit)).obj (op ⊤)) :=
  ⟨fun t => isEmptyElim ((pointSectionsEquiv equalizerFiber)
    ((equalizerComparison.app (op ⊤)).inv t))⟩

private def equalizerEmptyEquiv :
    (limit (equalizerDiagram ⋙ sectionsPresheafFunctor PUnit)).obj (op ⊥) ≃ PUnit :=
  (equalizerComparison.app (op ⊥)).toEquiv.symm.trans (emptySectionsEquiv _)

private theorem product_restriction
    (s : ((sectionsPresheafFunctor PUnit).obj (limit productDiagram)).obj (op ⊤)) :
    (preservesLimitIso (sectionsPresheafFunctor PUnit) productDiagram).hom.app (op ⊥)
        (((sectionsPresheafFunctor PUnit).obj (limit productDiagram)).map
          (homOfLE (bot_le : (⊥ : Opens PUnit) ≤ ⊤)).op s) =
      (limit (productDiagram ⋙ sectionsPresheafFunctor PUnit)).map
        (homOfLE (bot_le : (⊥ : Opens PUnit) ≤ ⊤)).op
          ((preservesLimitIso (sectionsPresheafFunctor PUnit) productDiagram).hom.app
            (op ⊤) s) :=
  sectionsPresheafFunctor_preservesLimitIso_hom_restrict productDiagram
    (homOfLE bot_le) s

end

end FundamentalGroupoidsTest.SectionsPresheafLimits
