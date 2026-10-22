/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# Sections presheaves of fundamental-groupoid representations

A representation of the fundamental groupoid determines a presheaf of transport-invariant
families on open subspaces. The transport condition uses the fundamental groupoid of the
open subspace itself: only paths staying inside that open enter the condition.

The construction uses `TopCat.PrelocalPredicate` and `TopCat.subpresheafToTypes` for the
presheaf of families. Its values are canonically equivalent to the `Functor.sections`
of the representation restricted along the open-subspace inclusion. Natural transformations
of representations act pointwise, compatibly with this equivalence and open restriction.

The space and fiber universes are independent. No connectedness, local connectedness or
inhabited-fiber hypothesis is needed. Only a presheaf is constructed here; no sheaf condition
or realization by a covering space is asserted.

## References

* Mathlib's fundamental groupoid and its underlying point equivalence, by Shing Tak Lam.
* Mathlib's prelocal predicates and presheaves of dependent functions, by Johan Commelin,
  Kim Morrison and Adam Topaz.
* Mathlib's sections of functors to types and their functorial action, by the authors of
  `Mathlib.CategoryTheory.Types.Basic`.
-/

@[expose] public section

noncomputable section

universe u w

open CategoryTheory TopologicalSpace Opposite

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X]

/-- Transport-invariance along paths in each open subspace is a prelocal predicate on
families in a fundamental-groupoid representation. -/
def sectionsPrelocal (F : FundamentalGroupoid X ⥤ Type w) :
    TopCat.PrelocalPredicate (X := TopCat.of X) (fun x : X => F.obj (mk x)) where
  pred {U} f := ∀ {a b : FundamentalGroupoid U} (γ : a ⟶ b),
    F.map ((map (ContinuousMap.subtypeVal (U : Set X))).map γ) (f a.as) = f b.as
  res {U V} i f hf := by
    intro a b γ
    let k : C(U, V) := ((Opens.toTopCat (TopCat.of X)).map i).hom
    have hcomp : map k ⋙ map (ContinuousMap.subtypeVal (V : Set X)) =
        map (ContinuousMap.subtypeVal (U : Set X)) := by
      rw [← FundamentalGroupoid.map_comp]
      rfl
    have hγ : (map (ContinuousMap.subtypeVal (V : Set X))).map ((map k).map γ) =
        (map (ContinuousMap.subtypeVal (U : Set X))).map γ :=
      eq_of_heq (Functor.hcongr_hom hcomp γ)
    change F.map ((map (ContinuousMap.subtypeVal (U : Set X))).map γ)
      (f (Set.inclusion (leOfHom i) a.as)) = f (Set.inclusion (leOfHom i) b.as)
    rw [← hγ]
    exact hf ((map k).map γ)

/-- The prelocal predicate uses all arrows in the fundamental groupoid of the open
subspace, rather than all ambient arrows between its points. -/
@[simp]
theorem sectionsPrelocal_pred_iff (F : FundamentalGroupoid X ⥤ Type w) {U : Opens X}
    (f : ∀ x : U, F.obj (mk (x : X))) :
    (sectionsPrelocal F).pred f ↔
      ∀ {a b : FundamentalGroupoid U} (γ : a ⟶ b),
        F.map ((map (ContinuousMap.subtypeVal (U : Set X))).map γ) (f a.as) = f b.as :=
  Iff.rfl

/-- A fundamental-groupoid representation gives a presheaf of transport-invariant
families, and an arbitrary natural transformation acts on these families pointwise.
The object presheaves are supplied by `TopCat.subpresheafToTypes`. -/
def sectionsPresheafFunctor (X : Type u) [TopologicalSpace X] :
    (FundamentalGroupoid X ⥤ Type w) ⥤ ((Opens X)ᵒᵖ ⥤ Type (max u w)) where
  obj F := TopCat.subpresheafToTypes (sectionsPrelocal F)
  map {F G} η :=
    { app := fun U => ↾fun s =>
        ⟨fun x => η.app (mk (x : X)) (s.val x), by
          intro a b γ
          exact (η.naturality_apply
            ((map (ContinuousMap.subtypeVal (U.unop : Set X))).map γ) (s.val a.as)).symm.trans
              (congrArg (fun z => η.app (mk (b.as : X)) z) (s.property γ))⟩
      naturality := by
        intro U V i
        apply ConcreteCategory.ext_apply
        intro s
        apply Subtype.ext
        funext x
        rfl }
  map_id F := by
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.ext_apply
    intro s
    apply Subtype.ext
    funext x
    rfl
  map_comp η θ := by
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.ext_apply
    intro s
    apply Subtype.ext
    funext x
    rfl

/-- Open restriction is precomposition with the inclusion of the smaller open. -/
@[simp]
theorem sectionsPresheafFunctor_obj_map_val (F : FundamentalGroupoid X ⥤ Type w)
    {U V : Opens X} (i : U ⟶ V)
    (s : ((sectionsPresheafFunctor X).obj F).obj (op V)) (x : U) :
    (((sectionsPresheafFunctor X).obj F).map i.op s).val x =
      s.val (Set.inclusion (leOfHom i) x) := rfl

/-- A natural transformation of representations acts pointwise on presheaf sections. -/
@[simp]
theorem sectionsPresheafFunctor_map_app_val {F G : FundamentalGroupoid X ⥤ Type w}
    (η : F ⟶ G) (U : Opens X)
    (s : ((sectionsPresheafFunctor X).obj F).obj (op U)) (x : U) :
    (((sectionsPresheafFunctor X).map η).app (op U) s).val x =
      η.app (mk (x : X)) (s.val x) := rfl

/-- The value of the sections presheaf is canonically equivalent to the sections
of the representation pulled back to the fundamental groupoid of the open subspace.
The reindexing is the underlying point equivalence `FundamentalGroupoid.equiv`. -/
def sectionsPresheafSectionsEquiv (F : FundamentalGroupoid X ⥤ Type w) (U : Opens X) :
    ((sectionsPresheafFunctor X).obj F).obj (op U) ≃
      (map (ContinuousMap.subtypeVal (U : Set X)) ⋙ F).sections where
  toFun s := ⟨fun a => s.val (equiv U a), s.property⟩
  invFun t := ⟨fun x => t.val ((equiv U).symm x), by
    intro a b γ
    exact t.property γ⟩
  left_inv s := by
    apply Subtype.ext
    funext x
    rfl
  right_inv t := by
    apply Subtype.ext
    funext a
    rfl

/-- The canonical equivalence preserves evaluation at points of the open. -/
@[simp]
theorem sectionsPresheafSectionsEquiv_apply_val (F : FundamentalGroupoid X ⥤ Type w)
    (U : Opens X) (s : ((sectionsPresheafFunctor X).obj F).obj (op U)) (x : U) :
    (sectionsPresheafSectionsEquiv F U s).val (mk x) = s.val x := rfl

/-- The inverse equivalence reads a section at the corresponding point wrapper. -/
@[simp]
theorem sectionsPresheafSectionsEquiv_symm_apply_val (F : FundamentalGroupoid X ⥤ Type w)
    (U : Opens X) (t : (map (ContinuousMap.subtypeVal (U : Set X)) ⋙ F).sections)
    (x : U) :
    ((sectionsPresheafSectionsEquiv F U).symm t).val x = t.val (mk x) := rfl

/-- The canonical sections equivalence commutes with open restriction at every point. -/
theorem sectionsPresheafSectionsEquiv_obj_map_val (F : FundamentalGroupoid X ⥤ Type w)
    {U V : Opens X} (i : U ⟶ V)
    (s : ((sectionsPresheafFunctor X).obj F).obj (op V)) (x : U) :
    (sectionsPresheafSectionsEquiv F U
        (((sectionsPresheafFunctor X).obj F).map i.op s)).val (mk x) =
      (sectionsPresheafSectionsEquiv F V s).val
        (mk (Set.inclusion (leOfHom i) x)) := rfl

/-- The canonical equivalence intertwines the representation action with the
`Functor.sectionsFunctor` action of the left-whiskered natural transformation. -/
@[simp]
theorem sectionsPresheafSectionsEquiv_map_app {F G : FundamentalGroupoid X ⥤ Type w}
    (η : F ⟶ G) (U : Opens X)
    (s : ((sectionsPresheafFunctor X).obj F).obj (op U)) :
    sectionsPresheafSectionsEquiv G U
        (((sectionsPresheafFunctor X).map η).app (op U) s) =
      (Functor.sectionsFunctor (FundamentalGroupoid U)).map
        (Functor.whiskerLeft (map (ContinuousMap.subtypeVal (U : Set X))) η)
        (sectionsPresheafSectionsEquiv F U s) := by
  apply Functor.sections_ext_iff.mpr
  intro a
  rfl

end FundamentalGroupoid
