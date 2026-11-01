/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.ConnectedComponents

/-!
# Connected components of a groupoid

Two objects of a groupoid represent the same categorical connected component
exactly when there is a morphism between them. The object and morphism universes
are independent.
-/

@[expose] public section

universe v u

namespace CategoryTheory.ConnectedComponents

variable {C : Type u} [Groupoid.{v} C]

/-- Two objects of a groupoid have the same connected component exactly when
there is a morphism between them. -/
theorem mk_eq_mk_iff_nonempty_hom (x y : C) :
    mk x = mk y ↔ Nonempty (x ⟶ y) := by
  constructor
  · intro h
    have hxy : Zigzag x y := Quotient.exact h
    clear h
    induction hxy with
    | refl => exact ⟨𝟙 _⟩
    | tail _ h ih =>
      rcases ih with ⟨g⟩
      rcases h with h | h
      · obtain ⟨f⟩ := h
        exact ⟨g ≫ f⟩
      · obtain ⟨f⟩ := h
        exact ⟨g ≫ inv f⟩
  · rintro ⟨f⟩
    exact Quotient.sound (Zigzag.of_hom f)

end CategoryTheory.ConnectedComponents
