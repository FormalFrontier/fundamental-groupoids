/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.SectionsPresheaf
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Limits of sections presheaves

The sections-presheaf functor preserves limits of shape `J` whenever the coefficient
category `Type v` has limits of that shape. In particular, it preserves limits indexed
by categories with `v`-small objects, with no bound on the universe of morphisms.
The space and coefficient universes are independent.

Sections commute with lifting the coefficient universe. After this lift, sections are
an internal limit, hence a right adjoint. This gives preservation without requiring
all `J`-limits in the larger universe of presheaf values.

The comparison is `CategoryTheory.preservesLimitIso`. Its projections are the
pointwise coefficient projections, and it commutes with restriction to every open.
-/

@[expose] public section

noncomputable section

universe u v w h k

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open TopologicalSpace Opposite

namespace CategoryTheory.Functor

/-- Lifting the coefficient universe does not change compatible families. -/
def sectionsFunctorUliftIso (C : Type u) [Category.{k} C] :
    (sectionsFunctor C : (C ⥤ Type v) ⥤ Type (max u v)) ≅
      (whiskeringRight C (Type v) (Type (max u v))).obj uliftFunctor.{u, v} ⋙
        sectionsFunctor C :=
  NatIso.ofComponents (fun F => (Types.sectionsEquiv F).toIso) fun η => by
    apply ConcreteCategory.ext_apply
    intro s
    apply Subtype.ext
    funext c
    rfl

/-- The lifted family has the same values, wrapped in `ULift`. -/
@[simp]
theorem sectionsFunctorUliftIso_hom_app_val (C : Type u) [Category.{k} C]
    (F : C ⥤ Type v) (s : F.sections) (c : C) :
    dsimp% (((sectionsFunctorUliftIso C).hom.app F) s).val c = ULift.up (s.val c) := rfl

/-- The inverse family comparison removes the coefficient lift. -/
@[simp]
theorem sectionsFunctorUliftIso_inv_app_val (C : Type u) [Category.{k} C]
    (F : C ⥤ Type v) (s : (F ⋙ uliftFunctor.{u, v}).sections) (c : C) :
    dsimp% (((sectionsFunctorUliftIso C).inv.app F) s).val c = (s.val c).down := rfl

/-- Sections preserve any shape of limits that exists in the coefficient category. -/
instance sectionsFunctor_preservesLimitsOfShape (C : Type u) [Category.{k} C]
    (J : Type w) [Category.{h} J] [HasLimitsOfShape J (Type v)] :
    PreservesLimitsOfShape J
      (sectionsFunctor C : (C ⥤ Type v) ⥤ Type (max u v)) := by
  let : PreservesLimitsOfSize.{h, w}
      (lim : (C ⥤ Type (max u v)) ⥤ Type (max u v)) :=
    (constLimAdj (J := C) (C := Type (max u v))).rightAdjoint_preservesLimits
  let : PreservesLimitsOfShape J
      (sectionsFunctor C : (C ⥤ Type (max u v)) ⥤ Type (max u v)) :=
    preservesLimitsOfShape_of_natIso (Types.limNatIsoSectionsFunctor (J := C))
  exact preservesLimitsOfShape_of_natIso (sectionsFunctorUliftIso C).symm

end CategoryTheory.Functor

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X]

/-- The sections equivalence at an open is natural in the coefficient representation. -/
def sectionsPresheafSectionsIso (U : Opens X) :
    (sectionsPresheafFunctor X :
      (FundamentalGroupoid X ⥤ Type v) ⥤ ((Opens X)ᵒᵖ ⥤ Type (max u v))) ⋙
        (evaluation (Opens X)ᵒᵖ (Type (max u v))).obj (op U) ≅
      (whiskeringLeft (FundamentalGroupoid U) (FundamentalGroupoid X) (Type v)).obj
          (map (ContinuousMap.subtypeVal (U : Set X))) ⋙
        sectionsFunctor (FundamentalGroupoid U) :=
  NatIso.ofComponents (fun F => (sectionsPresheafSectionsEquiv F U).toIso) fun η => by
    apply ConcreteCategory.ext_apply
    intro s
    exact sectionsPresheafSectionsEquiv_map_app η U s

/-- Evaluation of the sections isomorphism is evaluation of the family. -/
@[simp]
theorem sectionsPresheafSectionsIso_hom_apply_val
    (F : FundamentalGroupoid X ⥤ Type v) (U : Opens X)
    (s : ((sectionsPresheafFunctor X).obj F).obj (op U)) (x : U) :
    dsimp% ((sectionsPresheafSectionsIso U).hom.app F s).val (mk x) = s.val x :=
  sectionsPresheafSectionsEquiv_apply_val F U s x

/-- The inverse sections isomorphism preserves every value of the family. -/
@[simp]
theorem sectionsPresheafSectionsIso_inv_apply_val
    (F : FundamentalGroupoid X ⥤ Type v) (U : Opens X)
    (t : (map (ContinuousMap.subtypeVal (U : Set X)) ⋙ F).sections) (x : U) :
    dsimp% (((sectionsPresheafSectionsIso U).inv.app F) t).val x = t.val (mk x) :=
  sectionsPresheafSectionsEquiv_symm_apply_val F U t x

/-- The sections isomorphism commutes with open restriction. -/
theorem sectionsPresheafSectionsIso_hom_restrict_val
    (F : FundamentalGroupoid X ⥤ Type v) {U V : Opens X} (i : U ⟶ V)
    (s : ((sectionsPresheafFunctor X).obj F).obj (op V)) (x : U) :
    ((sectionsPresheafSectionsIso U).hom.app F
        (((sectionsPresheafFunctor X).obj F).map i.op s)).val (mk x) =
      ((sectionsPresheafSectionsIso V).hom.app F s).val
        (mk (Set.inclusion (leOfHom i) x)) :=
  sectionsPresheafSectionsEquiv_obj_map_val F i s x

/-- At each open, sections preserve every shape of limits available in `Type v`. -/
instance sectionsPresheafFunctor_evaluation_preservesLimitsOfShape
    (J : Type w) [Category.{h} J] [HasLimitsOfShape J (Type v)]
    (U : (Opens X)ᵒᵖ) :
    PreservesLimitsOfShape J
      ((sectionsPresheafFunctor X :
        (FundamentalGroupoid X ⥤ Type v) ⥤ ((Opens X)ᵒᵖ ⥤ Type (max u v))) ⋙
          (evaluation (Opens X)ᵒᵖ (Type (max u v))).obj U) :=
  preservesLimitsOfShape_of_natIso (sectionsPresheafSectionsIso U.unop).symm

/-- The sections-presheaf functor preserves limits of every shape for which the
coefficient types have limits. -/
instance sectionsPresheafFunctor_preservesLimitsOfShape
    (J : Type w) [Category.{h} J] [HasLimitsOfShape J (Type v)] :
    PreservesLimitsOfShape J
      (sectionsPresheafFunctor X :
        (FundamentalGroupoid X ⥤ Type v) ⥤ ((Opens X)ᵒᵖ ⥤ Type (max u v))) :=
  preservesLimitsOfShape_of_evaluation _ J fun _ => inferInstance

/-- Object-small shapes are preserved, independently of the morphism universe. -/
instance sectionsPresheafFunctor_preservesLimitsOfSize :
    PreservesLimitsOfSize.{h, v}
      (sectionsPresheafFunctor X :
        (FundamentalGroupoid X ⥤ Type v) ⥤ ((Opens X)ᵒᵖ ⥤ Type (max u v))) where
  preservesLimitsOfShape {J} := sectionsPresheafFunctor_preservesLimitsOfShape J

/-- The same conclusion holds for a shape equivalent to a coefficient-small type. -/
theorem sectionsPresheafFunctor_preservesLimitsOfShape_of_small
    (J : Type w) [Category.{h} J] [Small.{v} J] :
    PreservesLimitsOfShape J
      (sectionsPresheafFunctor X :
        (FundamentalGroupoid X ⥤ Type v) ⥤ ((Opens X)ᵒᵖ ⥤ Type (max u v))) :=
  inferInstance

section Comparisons

variable {J : Type w} [Category.{h} J] [HasLimitsOfShape J (Type v)]
variable (D : J ⥤ (FundamentalGroupoid X ⥤ Type v))

/-- The image diagram has a limit at every open, even without shape-wide
completeness of the category of presheaf values. -/
instance sectionsPresheafFunctor_evaluation_hasLimit (U : (Opens X)ᵒᵖ) :
    HasLimit ((D ⋙ sectionsPresheafFunctor X).flip.obj U) := by
  change HasLimit (D ⋙
    (sectionsPresheafFunctor X ⋙
      (evaluation (Opens X)ᵒᵖ (Type (max u v))).obj U))
  infer_instance

/-- Evaluation preserves the limit of the image diagram. -/
instance sectionsPresheafFunctor_evaluation_preservesLimit (U : (Opens X)ᵒᵖ) :
    PreservesLimit (D ⋙ sectionsPresheafFunctor X)
      ((evaluation (Opens X)ᵒᵖ (Type (max u v))).obj U) := by
  let : ∀ V, HasLimit ((D ⋙ sectionsPresheafFunctor X).flip.obj V) :=
    fun V => sectionsPresheafFunctor_evaluation_hasLimit D V
  infer_instance

/-- A projection of the comparison sends a section to its coefficient projection
at every point of the open. -/
@[simp]
theorem sectionsPresheafFunctor_preservesLimitIso_hom_app_π_val (j : J) (U : Opens X)
    (s : ((sectionsPresheafFunctor X).obj (limit D)).obj (op U)) (x : U) :
    dsimp% (((limit.π (D ⋙ sectionsPresheafFunctor X) j).app (op U))
      ((preservesLimitIso (sectionsPresheafFunctor X) D).hom.app (op U) s)).val x =
        (limit.π D j).app (mk (x : X)) (s.val x) := by
  have h := NatTrans.congr_app
    (preservesLimitIso_hom_π (sectionsPresheafFunctor X) D j) (op U)
  exact (congrArg (fun t => t.val x) (ConcreteCategory.congr_hom h s)).trans
    (sectionsPresheafFunctor_map_app_val (limit.π D j) U s x)

/-- The inverse comparison is characterized by all coefficient projections. -/
@[simp]
theorem sectionsPresheafFunctor_preservesLimitIso_inv_app_π_val (j : J) (U : Opens X)
    (t : (limit (D ⋙ sectionsPresheafFunctor X)).obj (op U)) (x : U) :
    (limit.π D j).app (mk (x : X))
        (((preservesLimitIso (sectionsPresheafFunctor X) D).inv.app (op U) t).val x) =
      (((limit.π (D ⋙ sectionsPresheafFunctor X) j).app (op U)) t).val x := by
  have h := NatTrans.congr_app
    (preservesLimitIso_inv_π (sectionsPresheafFunctor X) D j) (op U)
  calc
    _ = (((sectionsPresheafFunctor X).map (limit.π D j)).app (op U)
        ((preservesLimitIso (sectionsPresheafFunctor X) D).inv.app (op U) t)).val x :=
      (sectionsPresheafFunctor_map_app_val (limit.π D j) U _ x).symm
    _ = _ := congrArg (fun s => s.val x) (ConcreteCategory.congr_hom h t)

/-- The comparison commutes with every open restriction. -/
theorem sectionsPresheafFunctor_preservesLimitIso_hom_restrict
    {U V : Opens X} (i : U ⟶ V)
    (s : ((sectionsPresheafFunctor X).obj (limit D)).obj (op V)) :
    (preservesLimitIso (sectionsPresheafFunctor X) D).hom.app (op U)
        (((sectionsPresheafFunctor X).obj (limit D)).map i.op s) =
      (limit (D ⋙ sectionsPresheafFunctor X)).map i.op
        ((preservesLimitIso (sectionsPresheafFunctor X) D).hom.app (op V) s) :=
  ConcreteCategory.congr_hom
    ((preservesLimitIso (sectionsPresheafFunctor X) D).hom.naturality i.op) s

/-- The inverse comparison restricts by precomposition with the open inclusion. -/
theorem sectionsPresheafFunctor_preservesLimitIso_inv_restrict_val
    {U V : Opens X} (i : U ⟶ V)
    (t : (limit (D ⋙ sectionsPresheafFunctor X)).obj (op V)) (x : U) :
    ((preservesLimitIso (sectionsPresheafFunctor X) D).inv.app (op U)
        ((limit (D ⋙ sectionsPresheafFunctor X)).map i.op t)).val x =
      ((preservesLimitIso (sectionsPresheafFunctor X) D).inv.app (op V) t).val
        (Set.inclusion (leOfHom i) x) := by
  have h := ConcreteCategory.congr_hom
    ((preservesLimitIso (sectionsPresheafFunctor X) D).inv.naturality i.op) t
  exact (congrArg (fun s => s.val x) h).trans
    (sectionsPresheafFunctor_obj_map_val (limit D) i _ x)

end Comparisons

end FundamentalGroupoid
