/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.Combinatorics.Quiver.Covering

/-!
# The category-of-elements projection as a quiver covering

For a functor `F : G ⥤ Type w` on a groupoid, the projection `Functor.Elements.π F`
is a covering of the underlying quivers. For an element `x`, an outgoing arrow
`g : x.obj ⟶ b` determines the target element `F.map g x.val` and the whole lifted
arrow. Reversal gives the corresponding bijection on incoming arrows.
No nonemptiness, connectedness or surjectivity on objects is required.

The category of elements, its groupoid structure and its projection are Mathlib's
constructions. The proof uses Mathlib's bijective-star criterion and groupoid reversal.

## References

* `Mathlib.CategoryTheory.Elements`, by Kim Morrison and Joël Riou, supplies the
  category of elements and its projection.
* `Mathlib.CategoryTheory.Groupoid`, by Reid Barton, Kim Morrison and David Wärn,
  supplies groupoid reversal.
* `Mathlib.Combinatorics.Quiver.Covering`, by Antoine Labelle and Rémi Bottinelli,
  supplies the covering criterion for quivers with involutive reversal.
-/

@[expose] public section

universe u v w

namespace CategoryTheory.Functor.Elements

/-- The projection from the category of elements of a type-valued functor on a
groupoid is a covering of the underlying quivers. -/
theorem π_isCovering {G : Type u} [Category.{v} G] [IsGroupoid G]
    (F : G ⥤ Type w) : (π F).toPrefunctor.IsCovering := by
  let baseGroupoid : Groupoid.{v} G := Groupoid.ofIsGroupoid
  let elementsGroupoid : Groupoid.{v} F.Elements :=
    @Functor.Elements.groupoid G baseGroupoid F
  refine @Prefunctor.isCovering_of_bijective_star
    F.Elements elementsGroupoid.toCategory.toCategoryStruct.toQuiver
    G baseGroupoid.toCategory.toCategoryStruct.toQuiver
    (π F).toPrefunctor
    (@groupoidHasInvolutiveReverse F.Elements elementsGroupoid)
    (@groupoidHasInvolutiveReverse G baseGroupoid)
    (@functorMapReverse F.Elements elementsGroupoid G baseGroupoid (π F)) ?_
  intro x
  constructor
  · rintro ⟨y, f⟩ ⟨z, g⟩ h
    rcases y with @⟨b, y⟩
    rcases z with @⟨c, z⟩
    change (⟨b, f.hom⟩ : Quiver.Star x.obj) = ⟨c, g.hom⟩ at h
    obtain rfl : b = c := congrArg Sigma.fst h
    have hfg : f.hom = g.hom := sigma_mk_injective h
    have hyz : y = z := by
      calc
        y = F.map f.hom x.val := f.map_val.symm
        _ = F.map g.hom x.val := congrArg (fun k => F.map k x.val) hfg
        _ = z := g.map_val
    subst z
    have hhom : f = g := hom_ext hfg
    cases hhom
    rfl
  · rintro ⟨b, g⟩
    refine ⟨⟨F.elementsMk b (F.map g x.val), homMk g rfl⟩, ?_⟩
    rfl

end CategoryTheory.Functor.Elements
