/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Zero objects and zero morphisms of pointed types

The zero morphism between pointed types is the constant map to the target's
distinguished point. Composition with any pointed map on either side is zero.
A pointed type is a zero object exactly when its underlying type is a subsingleton.
The pointed singleton supplies a zero object in every universe.
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

/-- A pointed type is a zero object if and only if its underlying type is a subsingleton. -/
@[simp]
theorem isZero_iff_subsingleton (X : Pointed.{u}) : IsZero X ↔ Subsingleton X := by
  rw [IsZero.iff_id_eq_zero, eq_zero_iff]
  change (∀ x : X, x = X.point) ↔ Subsingleton X
  constructor
  · intro h
    exact ⟨fun x y => (h x).trans (h y).symm⟩
  · intro h x
    exact @Subsingleton.elim X h x X.point

/-- Pointed singletons provide a zero object in every universe. -/
instance hasZeroObject : HasZeroObject Pointed.{u} :=
  IsZero.hasZeroObject
    ((isZero_iff_subsingleton (Pointed.of (PUnit.unit : PUnit.{u + 1}))).2 inferInstance)

end Pointed
