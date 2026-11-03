/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based
public import FundamentalGroupoids.Topology.Path

/-!
# The ordinary based loop functor

The compact-open space of paths from the selected point to itself is based at
its constant path. A strict based map acts by pointwise postcomposition, with
endpoints transported along its basepoint equation.

The construction uses `ContinuousMap.loopMap` and its identity, composition and
constant-path laws. Relative homotopy of based maps is preserved, so the loop
functor descends uniquely to the based-homotopy category. Applying the descended
functor to the isomorphism given by based homotopy inverses yields an isomorphism
whose arrows are the classes of the induced loop maps.

No local compactness or separation condition on the original spaces is required.

## References

* Mathlib's path-space topology and continuous evaluation supply joint continuity
  of the induced homotopy, via `ContinuousMap.HomotopyRel.loopMap`.
* Mathlib's `CategoryTheory.Quotient.lift` and its universal property supply descent.
-/

@[expose] public section

universe u

open CategoryTheory

namespace BasedTopCat

/-- The ordinary based loop-space endofunctor, based at the constant loop. -/
def loopFunctor : BasedTopCat.{u} ⥤ BasedTopCat.{u} where
  obj X := of (Path (point X) (point X)) (Path.refl (point X))
  map {X Y} f :=
    ofHom (f.right.hom.loopMap (point X) (point Y) (map_point f))
      (ContinuousMap.loopMap_refl f.right.hom (point X) (point Y) (map_point f))
  map_id X := by
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    intro γ
    exact congrArg
      (fun k : C(Path (point X) (point X), Path (point X) (point X)) ↦ k γ)
      (ContinuousMap.loopMap_id (point X))
  map_comp {X Y Z} f g := by
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    intro γ
    exact congrArg
      (fun k : C(Path (point X) (point X), Path (point Z) (point Z)) ↦ k γ)
      (ContinuousMap.loopMap_comp f.right.hom g.right.hom (point X) (point Y) (point Z)
        (map_point f) (map_point g))

/-- The loop object is the path space based at its constant path. -/
theorem loopFunctor_obj (X : BasedTopCat.{u}) :
    loopFunctor.obj X = of (Path (point X) (point X)) (Path.refl (point X)) := by
  rfl

/-- The underlying space of the loop object is the ordinary compact-open path space. -/
theorem loopFunctor_obj_right (X : BasedTopCat.{u}) :
    (loopFunctor.obj X).right = TopCat.of (Path (point X) (point X)) := by
  rfl

/-- The selected point of the loop object is the constant loop. -/
@[simp]
theorem point_loopFunctor_obj (X : BasedTopCat.{u}) :
    point (loopFunctor.obj X) = Path.refl (point X) := by
  rfl

/-- The entire continuous map underlying the loop functor is `ContinuousMap.loopMap`. -/
theorem loopFunctor_map_right_hom {X Y : BasedTopCat.{u}} (f : X ⟶ Y) :
    (loopFunctor.map f).right.hom =
      f.right.hom.loopMap (point X) (point Y) (map_point f) := by
  rfl

/-- The loop functor sends each whole loop to its image under `ContinuousMap.loopMap`. -/
theorem loopFunctor_map_apply {X Y : BasedTopCat.{u}} (f : X ⟶ Y)
    (γ : Path (point X) (point X)) :
    (loopFunctor.map f).right.hom γ =
      f.right.hom.loopMap (point X) (point Y) (map_point f) γ := by
  rfl

/-- Evaluation of an induced loop is pointwise evaluation of the original based map. -/
@[simp]
theorem loopFunctor_map_apply_apply {X Y : BasedTopCat.{u}} (f : X ⟶ Y)
    (γ : Path (point X) (point X)) (t : unitInterval) :
    Path.toContinuousMap (x := point Y) (y := point Y)
        ((loopFunctor.map f).right.hom γ) t = f.right.hom (γ t) := by
  rfl

/-- The induced map on loop spaces preserves the whole constant loop. -/
theorem loopFunctor_map_refl {X Y : BasedTopCat.{u}} (f : X ⟶ Y) :
    (loopFunctor.map f).right.hom (Path.refl (point X)) = Path.refl (point Y) := by
  exact ContinuousMap.loopMap_refl f.right.hom (point X) (point Y) (map_point f)

/-- The loop functor preserves homotopy relative to the selected point. -/
theorem loopFunctor_map_homotopyRel {X Y : BasedTopCat.{u}} (f g : X ⟶ Y)
    (H : homotopyRel f g) : homotopyRel (loopFunctor.map f) (loopFunctor.map g) := by
  -- Expose the compact-open path-space topology at the boundary with the raw homotopy.
  change ContinuousMap.HomotopicRel
    (f.right.hom.loopMap (point X) (point Y) (map_point f))
    (g.right.hom.loopMap (point X) (point Y) (map_point g)) {Path.refl (point X)}
  exact ((homotopyRel_iff f g).1 H).loopMap (point Y) (map_point f) (map_point g)

namespace HomotopyCategory

/-- The ordinary loop-space endofunctor on the category of based-homotopy classes. -/
def loopFunctor : HomotopyCategory.{u} ⥤ HomotopyCategory.{u} :=
  CategoryTheory.Quotient.lift homotopyRel (BasedTopCat.loopFunctor ⋙ homotopyQuotient)
    (fun _ _ f g H ↦ (homotopyQuotient_map_eq_iff _ _).2
      (loopFunctor_map_homotopyRel f g H))

/-- On objects represented by based spaces, descent takes the ordinary loop space. -/
@[simp]
theorem loopFunctor_obj (X : BasedTopCat.{u}) :
    loopFunctor.obj (homotopyQuotient.obj X) =
      homotopyQuotient.obj (BasedTopCat.loopFunctor.obj X) :=
  CategoryTheory.Quotient.lift_obj_functor_obj _ _ _ X

/-- On a represented morphism, descent takes the class of the induced loop map. -/
@[simp]
theorem loopFunctor_map {X Y : BasedTopCat.{u}} (f : X ⟶ Y) :
    loopFunctor.map (homotopyQuotient.map f) =
      homotopyQuotient.map (BasedTopCat.loopFunctor.map f) :=
  CategoryTheory.Quotient.lift_map_functor_map _ _ _ f

/-- Taking loops commutes strictly with projection to based-homotopy classes. -/
theorem homotopyQuotient_comp_loopFunctor :
    homotopyQuotient ⋙ loopFunctor = BasedTopCat.loopFunctor ⋙ homotopyQuotient :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The strict commuting triangle characterizes the descended loop functor. -/
theorem loopFunctor_unique (F : HomotopyCategory.{u} ⥤ HomotopyCategory.{u})
    (hF : homotopyQuotient ⋙ F = BasedTopCat.loopFunctor ⋙ homotopyQuotient) :
    F = loopFunctor :=
  CategoryTheory.Quotient.lift_unique _ _ _ F hF

/-- There is a unique endofunctor on based-homotopy classes satisfying the strict triangle. -/
theorem loopFunctor_exists_unique :
    ∃! F : HomotopyCategory.{u} ⥤ HomotopyCategory.{u},
      homotopyQuotient ⋙ F = BasedTopCat.loopFunctor ⋙ homotopyQuotient :=
  ⟨loopFunctor, homotopyQuotient_comp_loopFunctor, loopFunctor_unique⟩

/-- The loop functor maps the forward arrow supplied by based homotopy inverses to
the class of the forward loop map. -/
theorem loopFunctor_mapIso_homotopyQuotientIso_hom {X Y : BasedTopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : homotopyRel (f ≫ g) (𝟙 X)) (hgf : homotopyRel (g ≫ f) (𝟙 Y)) :
    (loopFunctor.mapIso (homotopyQuotientIso f g hfg hgf)).hom =
      homotopyQuotient.map (BasedTopCat.loopFunctor.map f) :=
  loopFunctor_map f

/-- The loop functor maps the inverse arrow supplied by based homotopy inverses to
the class of the inverse loop map. -/
theorem loopFunctor_mapIso_homotopyQuotientIso_inv {X Y : BasedTopCat.{u}}
    (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : homotopyRel (f ≫ g) (𝟙 X)) (hgf : homotopyRel (g ≫ f) (𝟙 Y)) :
    (loopFunctor.mapIso (homotopyQuotientIso f g hfg hgf)).inv =
      homotopyQuotient.map (BasedTopCat.loopFunctor.map g) :=
  loopFunctor_map g

end HomotopyCategory

end BasedTopCat
