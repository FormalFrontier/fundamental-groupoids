/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Equivalence

/-!
# The canonical vertex functor

For an object `x` of a category `C`, the existing functor
`SingleObj.functor (MonoidHom.id (End x)) : SingleObj (End x) ⥤ C`
sends the unique object to `x` and acts as the identity on endomorphisms.
It is full and faithful for every category. In a preconnected groupoid it is
also essentially surjective, hence an equivalence.

## Implementation notes

The full and faithful instances do not require a groupoid or connectedness.
Essential surjectivity uses `nonempty_hom_of_preconnected_groupoid` and
`Groupoid.isoEquivHom`. A chosen vertex suffices, without a separate nonemptiness
hypothesis. Apply `Functor.asEquivalence` to the existing functor to obtain the
equivalence; its quasi-inverse need not make normalized choices at the vertex.
The object and morphism equations are the existing `SingleObj.functor_obj` and
`SingleObj.functor_map`.

## References

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §5.
-/

@[expose] public section

universe v u

namespace CategoryTheory.SingleObj

section Category

variable {C : Type u} [Category.{v} C]

/-- The canonical functor from the one-object endomorphism category at `x` is full. -/
instance full_functor_id (x : C) :
    (SingleObj.functor (MonoidHom.id (End x))).Full := by
  refine { map_surjective := ?_ }
  intro a b
  change Function.Surjective (fun f : End x ↦ f)
  exact Function.surjective_id

/-- The canonical functor from the one-object endomorphism category at `x` is faithful. -/
instance faithful_functor_id (x : C) :
    (SingleObj.functor (MonoidHom.id (End x))).Faithful := by
  refine { map_injective := ?_ }
  intro a b
  change Function.Injective (fun f : End x ↦ f)
  exact Function.injective_id

end Category

section Groupoid

variable {C : Type u} [Groupoid.{v} C] [IsPreconnected C]

/-- In a preconnected groupoid, every object is isomorphic to the chosen vertex. -/
instance essSurj_functor_id (x : C) :
    (SingleObj.functor (MonoidHom.id (End x))).EssSurj := by
  refine { mem_essImage := ?_ }
  intro y
  refine ⟨SingleObj.star (End x), ?_⟩
  simpa only [SingleObj.functor_obj] using
    Nonempty.map (Groupoid.isoEquivHom x y).symm
      (inferInstance : Nonempty (x ⟶ y))

/-- The canonical vertex functor is an equivalence for a preconnected groupoid.
This is the chosen-vertex equivalence of May, Chapter 2, §5. -/
instance isEquivalence_functor_id (x : C) :
    (SingleObj.functor (MonoidHom.id (End x))).IsEquivalence where

end Groupoid

end CategoryTheory.SingleObj
