/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Zero morphisms of pointed types

The zero morphism between pointed types is the constant map to the target's
distinguished point. Composition with any pointed map on either side is zero.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Pointed

/-- Zero morphisms of pointed types are constant maps to the target's distinguished point. -/
instance hasZeroMorphisms : HasZeroMorphisms Pointed.{u} where
  zero _X Y := { zero := { toFun := fun _ => Y.point, map_point := rfl } }
  comp_zero _f _Z := Pointed.Hom.ext rfl
  zero_comp _X {_Y _Z} f := Pointed.Hom.ext (funext fun _ => f.map_point)

/-- The zero morphism takes every input to the target's distinguished point. -/
@[simp]
theorem zero_apply {X Y : Pointed.{u}} (x : X) :
    (0 : X ⟶ Y) x = Y.point := by rfl

/-- A pointed map is zero if and only if every value is the target's distinguished point. -/
theorem eq_zero_iff {X Y : Pointed.{u}} (f : X ⟶ Y) :
    f = 0 ↔ ∀ x : X, f x = Y.point := by
  constructor
  · rintro rfl x
    exact zero_apply x
  · intro h
    apply Pointed.Hom.ext
    funext x
    exact (h x).trans (zero_apply (Y := Y) x).symm

/-- A composite of pointed maps is zero if and only if every composite value is the final
target's distinguished point. -/
theorem comp_eq_zero_iff {X Y Z : Pointed.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = 0 ↔ ∀ x : X, g (f x) = Z.point := by
  simpa only [CategoryTheory.comp_apply] using (eq_zero_iff (f ≫ g))

end Pointed
