/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Relative
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Based spaces and their based-homotopy category

A based topological space is an object of the under category of the one-point
space. Two based maps are related when their underlying continuous maps are
homotopic relative to the source basepoint. This relation is a congruence, so
morphisms of its quotient are equal exactly when their representatives are
based homotopic.

`BasedTopCat.HomotopyCategory` is Mathlib's category quotient. Its universal
property and descent of natural transformations and natural isomorphisms are
`CategoryTheory.Quotient.lift`, `CategoryTheory.Quotient.lift_spec`,
`CategoryTheory.Quotient.lift_unique`, `CategoryTheory.Quotient.natTransLift`
and `CategoryTheory.Quotient.natIsoLift`.

No connectedness, separation or condition on the basepoint is imposed.

## References

* Mathlib's `Mathlib.CategoryTheory.Comma.Over.Basic` supplies the under category.
* Mathlib's `Mathlib.Topology.Homotopy.Basic` supplies relative homotopy and its
  equivalence and postcomposition laws.
* David Wärn's `Mathlib.CategoryTheory.Quotient` supplies the category quotient
  and its universal property.
-/

@[expose] public section

universe u

open CategoryTheory

/-- The category of based topological spaces, as the under category of the one-point space. -/
abbrev BasedTopCat := Under (TopCat.of PUnit.{u + 1})

namespace BasedTopCat

/-- The selected point of a based topological space. -/
abbrev point (X : BasedTopCat.{u}) : X.right := X.hom PUnit.unit

/-- A topological space with a specified point, regarded as an object under the one-point space. -/
def of (X : Type u) [TopologicalSpace X] (x : X) : BasedTopCat.{u} :=
  Under.mk (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x))

/-- The underlying space of `of X x` is `X`. -/
@[simp]
theorem of_right (X : Type u) [TopologicalSpace X] (x : X) :
    (of X x).right = TopCat.of X := rfl

/-- The selected point of `of X x` is `x`. -/
@[simp]
theorem point_of (X : Type u) [TopologicalSpace X] (x : X) : point (of X x) = x := rfl

/-- A continuous map preserving specified points, regarded as a morphism of based spaces. -/
def ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) : of X x ⟶ of Y y :=
  Under.homMk (TopCat.ofHom f) (by
    apply TopCat.ext
    intro t
    exact h)

/-- The continuous map underlying `ofHom f h` is `f`. -/
@[simp]
theorem ofHom_right_hom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) :
    (ofHom f h).right.hom = f := rfl

/-- A morphism in the under category preserves the selected point. -/
@[simp]
theorem map_point {X Y : BasedTopCat.{u}} (f : X ⟶ Y) :
    f.right.hom (point X) = point Y := by
  exact congrArg (fun k : TopCat.of PUnit.{u + 1} ⟶ Y.right ↦ k PUnit.unit) (Under.w f)

/-- Based homotopy is homotopy of the underlying maps relative to the source basepoint. -/
def homotopyRel : HomRel BasedTopCat.{u} :=
  fun X _ f g ↦ ContinuousMap.HomotopicRel f.right.hom g.right.hom {point X}

/-- The based-homotopy relation fixes precisely the selected source point. -/
theorem homotopyRel_iff {X Y : BasedTopCat.{u}} (f g : X ⟶ Y) :
    homotopyRel f g ↔ ContinuousMap.HomotopicRel f.right.hom g.right.hom {point X} :=
  Iff.rfl

/-- Based homotopy is an equivalence on hom-sets compatible with composition. -/
instance homotopyRel_congruence : Congruence homotopyRel.{u} where
  equivalence := by
    intro X Y
    exact (ContinuousMap.HomotopicRel.equivalence (S := {point X})).comap
      (fun f : X ⟶ Y ↦ f.right.hom)
  comp_left := by
    intro X Y Z f g g' H
    exact ContinuousMap.HomotopicRel.precomp_continuousMap H f.right.hom (by
      intro x hx
      have hx' : x = point X := Set.mem_singleton_iff.mp hx
      subst x
      exact Set.mem_singleton_iff.mpr (map_point f))
  comp_right := by
    intro X Y Z f f' g H
    exact ContinuousMap.HomotopicRel.comp_continuousMap H g.right.hom

/-- The category of based spaces and based-homotopy classes of based maps. -/
abbrev HomotopyCategory := CategoryTheory.Quotient homotopyRel.{u}

/-- The projection of based spaces to their based-homotopy category. -/
abbrev homotopyQuotient : BasedTopCat.{u} ⥤ HomotopyCategory.{u} :=
  CategoryTheory.Quotient.functor homotopyRel

/-- Two based maps have the same quotient class exactly when they are based homotopic. -/
theorem homotopyQuotient_map_eq_iff {X Y : BasedTopCat.{u}} (f g : X ⟶ Y) :
    homotopyQuotient.map f = homotopyQuotient.map g ↔
      ContinuousMap.HomotopicRel f.right.hom g.right.hom {point X} :=
  CategoryTheory.Quotient.functor_map_eq_iff homotopyRel f g

end BasedTopCat
