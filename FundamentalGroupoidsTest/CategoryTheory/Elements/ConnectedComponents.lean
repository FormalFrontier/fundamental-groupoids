/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.CategoryTheory.Elements.ConnectedComponents
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
# Components of categories of elements: two values, empty diagrams and a span

For the constant `Bool` functor on a one-object discrete category, the two values
lie in distinct components even though their underlying base object is the same.
The components/type-colimit equivalence detects this distinction through a cocone
with vertex `Bool`. Diagrams on the empty discrete category have neither elements
components nor colimit values.

For the span from `PUnit` to two copies of `Bool`, with legs selecting `true` and
`false`, the corresponding elements lie in one component. Transporting this
identification through the components/colimit equivalence identifies their images
under the two colimit inclusions.

These examples and proofs are by Formal Frontier Agents, using Mathlib's discrete
categories, span constructors and quotient-type cocones.
-/

namespace CategoryTheory

universe w

example : ∃ X : Discrete PUnit ⥤ Type, ∃ x y : X.obj ⟨PUnit.unit⟩,
    x ≠ y ∧ ConnectedComponents.mk (X.elementsMk ⟨PUnit.unit⟩ x) ≠
      ConnectedComponents.mk (X.elementsMk ⟨PUnit.unit⟩ y) := by
  let X : Discrete PUnit ⥤ Type := (Functor.const (Discrete PUnit)).obj Bool
  refine ⟨X, true, false, ?_, ?_⟩
  · intro h
    cases h
  let cocone : X.CoconeTypes.{0} :=
    { pt := Bool
      ι _ := id
      ι_naturality := by intros j j' f; rfl }
  intro h
  have h' : X.ιColimitType ⟨PUnit.unit⟩ true =
      X.ιColimitType ⟨PUnit.unit⟩ false := by
    simpa using congrArg X.elementsConnectedComponentsEquivColimitType h
  have hval := congrArg (X.descColimitType cocone) h'
  change true = false at hval
  cases hval

example (X : Discrete PEmpty ⥤ Type w) : IsEmpty X.ColimitType := by
  refine ⟨fun z => ?_⟩
  obtain ⟨c, _, _⟩ := X.ιColimitType_jointly_surjective z
  exact PEmpty.elim c.as

example (X : Discrete PEmpty ⥤ Type w) :
    IsEmpty (ConnectedComponents X.Elements) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨e, _⟩ := Quotient.exists_rep z
  exact PEmpty.elim e.obj.as

example :
    let X : Limits.WalkingSpan ⥤ Type :=
      Limits.span (↾fun _ : PUnit => true) (↾fun _ : PUnit => false)
    Limits.colimit.ι X Limits.WalkingSpan.left true =
      Limits.colimit.ι X Limits.WalkingSpan.right false := by
  let X : Limits.WalkingSpan ⥤ Type :=
    Limits.span (↾fun _ : PUnit => true) (↾fun _ : PUnit => false)
  let x : X.obj Limits.WalkingSpan.zero := PUnit.unit
  have h :
      ConnectedComponents.mk (X.elementsMk Limits.WalkingSpan.left
        (X.map Limits.WalkingSpan.Hom.fst x)) =
      ConnectedComponents.mk (X.elementsMk Limits.WalkingSpan.right
        (X.map Limits.WalkingSpan.Hom.snd x)) := by
    apply Quotient.sound
    have first : X.elementsMk Limits.WalkingSpan.zero x ⟶
        X.elementsMk Limits.WalkingSpan.left (X.map Limits.WalkingSpan.Hom.fst x) :=
      Functor.Elements.homMk Limits.WalkingSpan.Hom.fst rfl
    have second : X.elementsMk Limits.WalkingSpan.zero x ⟶
        X.elementsMk Limits.WalkingSpan.right (X.map Limits.WalkingSpan.Hom.snd x) :=
      Functor.Elements.homMk Limits.WalkingSpan.Hom.snd rfl
    exact (Zigzag.of_inv first).trans (Zigzag.of_hom second)
  simpa only [Functor.elementsConnectedComponentsEquivColimit_apply, X, x,
    Limits.span_map_fst, Limits.span_map_snd, TypeCat.ofHom_apply] using
    congrArg X.elementsConnectedComponentsEquivColimit h

end CategoryTheory
