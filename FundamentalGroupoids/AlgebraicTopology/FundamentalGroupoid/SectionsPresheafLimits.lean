/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.SectionsPresheaf
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Limits of sections presheaves

Sections of a type-valued functor are corepresented by a constant singleton
representation. Hence the sections functor preserves every existing limit,
with independent category, coefficient and indexing universes.

The sections-presheaf functor sends pointwise limit cones of representations to
limit cones. If the fundamental groupoid has coefficient-small Hom types, it
preserves all existing limits of arbitrary indexing size. This is a sufficient
condition, not a necessity statement or an assertion of completeness.
The coefficient-shape and object-small preservation instances remain available.

Sections also commute with lifting the coefficient universe. The limit comparison
is `CategoryTheory.preservesLimitIso`: its projections are the pointwise coefficient
projections, and it commutes with restriction to every open.
-/

@[expose] public section

noncomputable section

universe u v w h k

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open TopologicalSpace Opposite

namespace CategoryTheory

universe a

/-- Sections are morphisms from a constant functor on any singleton coefficient type. -/
def sectionsFunctorCoyonedaIso {C : Type u} [Category.{a} C]
    (A : Type v) [Unique A] :
    (Functor.sectionsFunctor C : (C ⥤ Type v) ⥤ Type (max u v)) ≅
      coyoneda.obj (op ((Functor.const C).obj A)) :=
  NatIso.ofComponents (fun F => (F.sectionsEquivHom A).toIso) fun f => by
    apply ConcreteCategory.ext_apply
    intro s
    exact Functor.sectionsEquivHom_naturality f A s

/-- The natural transformation associated to a section is constant at each object. -/
@[simp]
theorem sectionsFunctorCoyonedaIso_hom_app_apply {C : Type u} [Category.{a} C]
    (A : Type v) [Unique A] (F : C ⥤ Type v) (s : F.sections) (p : C) (x : A) :
    dsimp% (((sectionsFunctorCoyonedaIso (C := C) A).hom.app F) s).app p x =
      s.val p := rfl

/-- A morphism from the constant singleton functor determines a section by evaluation. -/
@[simp]
theorem sectionsFunctorCoyonedaIso_inv_app_val {C : Type u} [Category.{a} C]
    (A : Type v) [Unique A] (F : C ⥤ Type v)
    (η : (Functor.const C).obj A ⟶ F) (p : C) :
    dsimp% (((sectionsFunctorCoyonedaIso (C := C) A).inv.app F) η).val p =
      η.app p (default : A) := rfl

/-- The section-to-morphism comparison commutes with coefficient morphisms at each value. -/
theorem sectionsFunctorCoyonedaIso_hom_naturality_apply {C : Type u} [Category.{a} C]
    (A : Type v) [Unique A] {F G : C ⥤ Type v} (f : F ⟶ G)
    (s : F.sections) (p : C) (x : A) :
    dsimp% (((sectionsFunctorCoyonedaIso (C := C) A).hom.app G)
        ((Functor.sectionsFunctor C).map f s)).app p x =
      f.app p ((((sectionsFunctorCoyonedaIso (C := C) A).hom.app F) s).app p x) := by
  exact congrArg (fun η : (Functor.const C).obj A ⟶ G => η.app p x)
    (Functor.sectionsEquivHom_naturality f A s)

/-- The morphism-to-section comparison commutes with coefficient morphisms at each value. -/
theorem sectionsFunctorCoyonedaIso_inv_naturality_val {C : Type u} [Category.{a} C]
    (A : Type v) [Unique A] {F G : C ⥤ Type v} (f : F ⟶ G)
    (η : (Functor.const C).obj A ⟶ F) (p : C) :
    dsimp% (((sectionsFunctorCoyonedaIso (C := C) A).inv.app G) (η ≫ f)).val p =
      f.app p ((((sectionsFunctorCoyonedaIso (C := C) A).inv.app F) η).val p) := by
  exact congrArg (fun s : G.sections => s.val p)
    (Functor.sectionsEquivHom_naturality_symm f A η)

/-- At the expanded coefficient universe, the two sections/co-Yoneda comparisons agree. -/
theorem sectionsFunctorCoyonedaIso_eq_sectionsFunctorNatIsoCoyoneda
    {C : Type u} [Category.{a} C] (A : Type (max u v)) [Unique A] :
    sectionsFunctorCoyonedaIso (C := C) A =
      sectionsFunctorNatIsoCoyoneda (C := C) A := by
  rfl

namespace Functor

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

/-- Sections preserve limits of any size whenever those limits exist in the domain. -/
instance sectionsFunctor_preservesLimitsOfSize (C : Type u) [Category.{a} C] :
    PreservesLimitsOfSize.{h, w} (Functor.sectionsFunctor.{a, v} C) := by
  exact preservesLimits_of_natIso
    (CategoryTheory.sectionsFunctorCoyonedaIso (C := C) (PUnit : Type v)).symm

/-- Sections preserve limits of any shape whenever those limits exist in the domain. -/
instance sectionsFunctor_preservesLimitsOfShape (C : Type u) [Category.{a} C]
    (J : Type w) [Category.{h} J] :
    PreservesLimitsOfShape J
      (sectionsFunctor C : (C ⥤ Type v) ⥤ Type (max u v)) := by
  have : PreservesLimitsOfSize.{h, w} (Functor.sectionsFunctor.{a, v} C) :=
    sectionsFunctor_preservesLimitsOfSize (C := C)
  infer_instance

end Functor

end CategoryTheory

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

/-- A pointwise limit cone of representations induces a limit cone of sections
presheaves. -/
def sectionsPresheafFunctorMapConeIsLimitOfPointwise
    {J : Type w} [Category.{h} J]
    (D : J ⥤ (FundamentalGroupoid X ⥤ Type v)) (c : Cone D)
    (hc : ∀ p : FundamentalGroupoid X,
      IsLimit (((evaluation (FundamentalGroupoid X) (Type v)).obj p).mapCone c)) :
    IsLimit ((sectionsPresheafFunctor X).mapCone c) := by
  apply evaluationJointlyReflectsLimits
  intro U
  let I : FundamentalGroupoid U.unop ⥤ FundamentalGroupoid X :=
    map (ContinuousMap.subtypeVal (U.unop : Set X))
  let R : (FundamentalGroupoid X ⥤ Type v) ⥤
      (FundamentalGroupoid U.unop ⥤ Type v) :=
    (whiskeringLeft (FundamentalGroupoid U.unop)
      (FundamentalGroupoid X) (Type v)).obj I
  have hR : IsLimit (R.mapCone c) := by
    apply evaluationJointlyReflectsLimits
    intro q
    change IsLimit
      (((evaluation (FundamentalGroupoid X) (Type v)).obj (I.obj q)).mapCone c)
    exact hc (I.obj q)
  letI : PreservesLimitsOfSize.{h, w}
      (sectionsFunctor (FundamentalGroupoid U.unop) :
        (FundamentalGroupoid U.unop ⥤ Type v) ⥤ Type (max u v)) :=
    CategoryTheory.Functor.sectionsFunctor_preservesLimitsOfSize
      (C := FundamentalGroupoid U.unop)
  have hΓ : IsLimit
      ((R ⋙ sectionsFunctor (FundamentalGroupoid U.unop)).mapCone c) :=
    isLimitOfPreserves (sectionsFunctor (FundamentalGroupoid U.unop)) hR
  change IsLimit
    (((sectionsPresheafFunctor X :
        (FundamentalGroupoid X ⥤ Type v) ⥤ ((Opens X)ᵒᵖ ⥤ Type (max u v))) ⋙
      (evaluation (Opens X)ᵒᵖ (Type (max u v))).obj U).mapCone c)
  exact IsLimit.mapConeEquiv (sectionsPresheafSectionsIso U.unop).symm hΓ

/-- Coefficient-small Hom types in the fundamental groupoid suffice for preservation
of all existing limits by the sections-presheaf functor. -/
instance sectionsPresheafFunctor_preservesLimitsOfSize_of_locallySmall
    [LocallySmall.{v} (FundamentalGroupoid X)] :
    PreservesLimitsOfSize.{h, w}
      (sectionsPresheafFunctor X :
        (FundamentalGroupoid X ⥤ Type v) ⥤ ((Opens X)ᵒᵖ ⥤ Type (max u v))) := by
  let : ∀ p q : FundamentalGroupoid X,
      HasCoproductsOfShape (p ⟶ q) (Type v) := fun p q => by
    let : Small.{v} (p ⟶ q) := LocallySmall.hom_small p q
    let : Small.{v} (Discrete (p ⟶ q)) := inferInstance
    exact CategoryTheory.Limits.Types.hasColimitsOfShape
  refine { preservesLimitsOfShape := ?_ }
  intro J instJ
  refine { preservesLimit := ?_ }
  intro D
  refine { preserves := ?_ }
  intro c hc
  refine ⟨sectionsPresheafFunctorMapConeIsLimitOfPointwise D c (fun p => ?_)⟩
  letI : ((evaluation (FundamentalGroupoid X) (Type v)).obj p).IsRightAdjoint :=
    CategoryTheory.evaluationIsRightAdjoint (Type v) p
  letI : PreservesLimitsOfSize.{h, w}
      ((evaluation (FundamentalGroupoid X) (Type v)).obj p) := inferInstance
  exact isLimitOfPreserves ((evaluation (FundamentalGroupoid X) (Type v)).obj p) hc

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

variable {J : Type w} [Category.{h} J]

section

variable [HasLimitsOfShape J (Type v)]
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

end

variable (D : J ⥤ (FundamentalGroupoid X ⥤ Type v))
variable [HasLimit D] [PreservesLimit D (sectionsPresheafFunctor X)]

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
