/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup
public import FundamentalGroupoids.Topology.Category.TopCat.Based
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# The fundamental-group functor on based spaces

`FundamentalGroup.functor` sends a based space to the vertex group of its selected
point and a based map to `FundamentalGroup.mapOfEq`. It factors through the category
of based spaces and based-homotopy classes via `FundamentalGroup.homotopyFunctor`.
The factorization is the lift along Mathlib's category quotient, with its equality,
uniqueness and natural-transformation descent API.

The spaces and their selected points are arbitrary: no connectedness, separation
or condition on the basepoint is required. The homotopies used in the quotient fix
the selected point throughout; an unbased homotopy need not give equal induced
homomorphisms at a fixed basepoint.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 1, §4, for based
  homotopy invariance and functoriality of the fundamental group.
* Mathlib's `Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup`
  supplies vertex groups and `FundamentalGroup.mapOfEq`.
* Mathlib's `Mathlib.CategoryTheory.Comma.Over.Basic` and David Wärn's
  `Mathlib.CategoryTheory.Quotient` supply the based-space category and its quotient.
* `FundamentalGroupoids.FundamentalGroup` supplies the induced-map laws and
  the moving-basepoint homotopy comparison used for relative homotopy invariance.
-/

@[expose] public section

universe u

open CategoryTheory

namespace FundamentalGroup

/-- The fundamental group as a functor from ordinary based topological spaces to groups. -/
noncomputable def functor : BasedTopCat.{u} ⥤ GrpCat.{u} where
  obj X := GrpCat.of (FundamentalGroup X.right (BasedTopCat.point X))
  map f := GrpCat.ofHom (mapOfEq f.right.hom (BasedTopCat.map_point f))
  map_id X := by
    apply GrpCat.hom_ext
    change mapOfEq (ContinuousMap.id X.right) rfl =
      MonoidHom.id (FundamentalGroup X.right (BasedTopCat.point X))
    exact mapOfEq_id (BasedTopCat.point X)
  map_comp f g := by
    apply GrpCat.hom_ext
    simpa only [GrpCat.hom_ofHom, GrpCat.hom_comp, Under.comp_right, TopCat.hom_comp] using
      mapOfEq_comp g.right.hom f.right.hom (BasedTopCat.map_point f) (BasedTopCat.map_point g)

/-- The group assigned to a based space is its fundamental group at the selected point. -/
@[simp]
theorem functor_obj (X : BasedTopCat.{u}) :
    functor.obj X = GrpCat.of (FundamentalGroup X.right (BasedTopCat.point X)) := rfl

/-- The homomorphism assigned to a based map is induced by its underlying continuous map
and the basepoint equality in the under category. -/
@[simp]
theorem functor_map_hom {X Y : BasedTopCat.{u}} (f : X ⟶ Y) :
    (functor.map f).hom = mapOfEq f.right.hom (BasedTopCat.map_point f) := rfl

/-- A based map sends a loop class to its image loop class, with endpoints cast by basedness. -/
theorem functor_map_apply {X Y : BasedTopCat.{u}} (f : X ⟶ Y)
    (q : FundamentalGroup X.right (BasedTopCat.point X)) :
    functor.map f q =
      (Path.Homotopic.Quotient.map q f.right.hom).cast
        (BasedTopCat.map_point f).symm (BasedTopCat.map_point f).symm :=
  mapOfEq_apply f.right.hom (BasedTopCat.map_point f) q

/-- On a continuous map with a specified basepoint equality, the functor gives `mapOfEq`. -/
theorem functor_map_ofHom {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (f : C(X, Y)) (h : f x = y) :
    (functor.map (BasedTopCat.ofHom f h)).hom = mapOfEq f h := rfl

/-- Based-homotopic based maps induce the same fundamental-group homomorphism. -/
theorem functor_map_eq_of_homotopicRel {X Y : BasedTopCat.{u}} {f g : X ⟶ Y}
    (H : BasedTopCat.homotopyRel f g) : functor.map f = functor.map g := by
  exact congrArg GrpCat.ofHom
    (mapOfEq_eq_of_homotopicRel ((BasedTopCat.homotopyRel_iff f g).mp H)
      (Set.mem_singleton (BasedTopCat.point X)) (BasedTopCat.map_point f) (BasedTopCat.map_point g))

/-- The fundamental-group functor on the category of based spaces and based-homotopy classes. -/
noncomputable def homotopyFunctor : BasedTopCat.HomotopyCategory.{u} ⥤ GrpCat.{u} :=
  CategoryTheory.Quotient.lift BasedTopCat.homotopyRel functor
    (fun _ _ _ _ H ↦ functor_map_eq_of_homotopicRel H)

/-- Passing to the based-homotopy category does not change the group assigned to a space. -/
@[simp]
theorem homotopyFunctor_obj (X : BasedTopCat.HomotopyCategory.{u}) :
    homotopyFunctor.obj X =
      GrpCat.of (FundamentalGroup X.as.right (BasedTopCat.point X.as)) := rfl

/-- On the class of a based map, the quotient functor gives its induced homomorphism. -/
@[simp]
theorem homotopyFunctor_map {X Y : BasedTopCat.{u}} (f : X ⟶ Y) :
    homotopyFunctor.map (BasedTopCat.homotopyQuotient.map f) = functor.map f :=
  CategoryTheory.Quotient.lift_map_functor_map BasedTopCat.homotopyRel functor
    (fun _ _ _ _ H ↦ functor_map_eq_of_homotopicRel H) f

/-- The fundamental-group functor factors through based homotopy. -/
theorem homotopyQuotient_comp_homotopyFunctor :
    BasedTopCat.homotopyQuotient.{u} ⋙ homotopyFunctor = functor :=
  CategoryTheory.Quotient.lift_spec BasedTopCat.homotopyRel functor
    (fun _ _ _ _ H ↦ functor_map_eq_of_homotopicRel H)

/-- The functor induced on the based-homotopy category is the unique factorization of
`FundamentalGroup.functor` through the quotient. -/
theorem homotopyFunctor_unique (F : BasedTopCat.HomotopyCategory.{u} ⥤ GrpCat.{u})
    (hF : BasedTopCat.homotopyQuotient ⋙ F = functor) : F = homotopyFunctor :=
  CategoryTheory.Quotient.lift_unique BasedTopCat.homotopyRel functor
    (fun _ _ _ _ H ↦ functor_map_eq_of_homotopicRel H) F hF

end FundamentalGroup
