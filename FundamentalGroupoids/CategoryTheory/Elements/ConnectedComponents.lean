/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Connected components of the category of elements

The connected components of the category of elements of a type-valued functor are its
type colimit, with no size or connectedness assumptions on the indexing category.
When the diagram has a colimit in its original universe, this also identifies the
components with that actual colimit.

The object, morphism and value universes are independent. The quotient-type
comparison requires no smallness, nonemptiness or connectedness hypothesis;
comparison with a colimit in `Type w` requires only `Limits.HasColimit X`.

## References

The equivalences and naturality proofs are by Formal Frontier Agents. They use:

* Kim Morrison and Joël Riou's category of elements in
  `Mathlib.CategoryTheory.Elements`.
* Bhavik Mehta's connected components in
  `Mathlib.CategoryTheory.ConnectedComponents`.
* Joël Riou's quotient-type colimits in
  `Mathlib.CategoryTheory.Limits.Types.ColimitType`, and Kim Morrison, Reid Barton
  and Joël Riou's colimits in `Mathlib.CategoryTheory.Limits.Types.Colimits`.
-/

set_option warningAsError true

@[expose] public section

namespace CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

namespace Functor

variable (X : C ⥤ Type w)

private theorem ιColimitType_eq_of_elements_hom {e e' : X.Elements} (f : e ⟶ e') :
    X.ιColimitType e.obj e.val = X.ιColimitType e'.obj e'.val := by
  calc
    X.ιColimitType e.obj e.val = X.ιColimitType e'.obj (X.map f.hom e.val) :=
      (X.ιColimitType_map f.hom e.val).symm
    _ = X.ιColimitType e'.obj e'.val := congrArg _ f.map_val

/-- The canonical equivalence from the components of the category of elements to
the quotient-type colimit. Both quotients retain the fiber elements, not just
their underlying objects in `C`. -/
def elementsConnectedComponentsEquivColimitType :
    ConnectedComponents X.Elements ≃ X.ColimitType := by
  let forward : ConnectedComponents X.Elements → X.ColimitType :=
    Quotient.lift (fun e : X.Elements => X.ιColimitType e.obj e.val) (by
      intro e e' h
      induction h with
      | refl => rfl
      | tail _ edge ih =>
          exact ih.trans (by
            rcases edge with (⟨⟨f⟩⟩ | ⟨⟨f⟩⟩)
            · exact X.ιColimitType_eq_of_elements_hom f
            · exact (X.ιColimitType_eq_of_elements_hom f).symm))
  let cocone : X.CoconeTypes.{max u w} :=
    { pt := ConnectedComponents X.Elements
      ι c x := ConnectedComponents.mk (X.elementsMk c x)
      ι_naturality f := by
        funext x
        exact (Quotient.sound (Zigzag.of_hom
          (Functor.Elements.homMk f (show X.map f x = X.map f x from rfl)))).symm }
  refine ⟨forward, X.descColimitType cocone, ?_, ?_⟩
  · intro z
    induction z using Quotient.inductionOn'
    rfl
  · intro z
    obtain ⟨c, x, rfl⟩ := X.ιColimitType_jointly_surjective z
    rfl

@[simp]
theorem elementsConnectedComponentsEquivColimitType_apply (c : C) (x : X.obj c) :
    X.elementsConnectedComponentsEquivColimitType
        (ConnectedComponents.mk (X.elementsMk c x)) = X.ιColimitType c x := rfl

@[simp]
theorem elementsConnectedComponentsEquivColimitType_symm_apply (c : C) (x : X.obj c) :
    X.elementsConnectedComponentsEquivColimitType.symm (X.ιColimitType c x) =
      ConnectedComponents.mk (X.elementsMk c x) := rfl

end Functor

namespace NatTrans

/-- The map of quotient-type colimits induced by a natural transformation. -/
def mapColimitType {X Y : C ⥤ Type w} (α : X ⟶ Y) : X.ColimitType → Y.ColimitType :=
  X.descColimitType (Y.coconeTypes.precompose (fun c => α.app c) (by
    intro c d f
    funext x
    simpa only [Function.comp_apply] using (α.naturality_apply f x)))

@[simp]
theorem mapColimitType_ι {X Y : C ⥤ Type w} (α : X ⟶ Y) (c : C) (x : X.obj c) :
    mapColimitType α (X.ιColimitType c x) = Y.ιColimitType c (α.app c x) := rfl

@[simp]
theorem mapColimitType_id (X : C ⥤ Type w) :
    mapColimitType (𝟙 X) = id := by
  funext z
  obtain ⟨c, x, rfl⟩ := X.ιColimitType_jointly_surjective z
  simp

@[simp]
theorem mapColimitType_comp {X Y Z : C ⥤ Type w} (α : X ⟶ Y) (β : Y ⟶ Z) :
    mapColimitType (α ≫ β) = mapColimitType β ∘ mapColimitType α := by
  funext z
  obtain ⟨c, x, rfl⟩ := X.ιColimitType_jointly_surjective z
  simp

end NatTrans

namespace Functor

/-- Naturality of the components/type-colimit equivalence, using the canonical map
between categories of elements. -/
theorem elementsConnectedComponentsEquivColimitType_natural
    {X Y : C ⥤ Type w} (α : X ⟶ Y) (z : ConnectedComponents X.Elements) :
    Y.elementsConnectedComponentsEquivColimitType
        ((NatTrans.mapElements α).mapConnectedComponents z) =
      NatTrans.mapColimitType α (X.elementsConnectedComponentsEquivColimitType z) := by
  obtain ⟨e, he⟩ := Quotient.exists_rep z
  rw [← he]
  change Y.elementsConnectedComponentsEquivColimitType
    (ConnectedComponents.mk (Y.elementsMk e.obj (α.app e.obj e.val))) =
      Y.ιColimitType e.obj (α.app e.obj e.val)
  exact Y.elementsConnectedComponentsEquivColimitType_apply e.obj (α.app e.obj e.val)

variable (X : C ⥤ Type w) [Limits.HasColimit X]

/-- The components of the elements category as an actual colimit in `Type w`.
Unlike the quotient-type colimit, this requires the individual diagram to have
a colimit in its original universe. -/
noncomputable def elementsConnectedComponentsEquivColimit :
    ConnectedComponents X.Elements ≃ (Limits.colimit X : Type w) :=
  X.elementsConnectedComponentsEquivColimitType.trans
    (Limits.Types.colimitEquivColimitType X).symm

@[simp]
theorem elementsConnectedComponentsEquivColimit_apply (c : C) (x : X.obj c) :
    X.elementsConnectedComponentsEquivColimit
        (ConnectedComponents.mk (X.elementsMk c x)) = Limits.colimit.ι X c x := by
  change (Limits.Types.colimitEquivColimitType X).symm (X.ιColimitType c x) =
    Limits.colimit.ι X c x
  exact Limits.Types.colimitEquivColimitType_symm_apply X c x

@[simp]
theorem elementsConnectedComponentsEquivColimit_symm_apply (c : C) (x : X.obj c) :
    X.elementsConnectedComponentsEquivColimit.symm (Limits.colimit.ι X c x) =
      ConnectedComponents.mk (X.elementsMk c x) := by
  change X.elementsConnectedComponentsEquivColimitType.symm
    ((Limits.Types.colimitEquivColimitType X) (Limits.colimit.ι X c x)) = _
  rw [Limits.Types.colimitEquivColimitType_apply]
  exact X.elementsConnectedComponentsEquivColimitType_symm_apply c x

/-- Naturality of the actual colimit equivalence needs only the two individual
colimit instances, not all colimits of this shape in `Type w`. -/
theorem elementsConnectedComponentsEquivColimit_natural
    {X Y : C ⥤ Type w} [Limits.HasColimit X] [Limits.HasColimit Y]
    (α : X ⟶ Y) (z : ConnectedComponents X.Elements) :
    Y.elementsConnectedComponentsEquivColimit
        ((NatTrans.mapElements α).mapConnectedComponents z) =
      Limits.colimMap α (X.elementsConnectedComponentsEquivColimit z) := by
  obtain ⟨e, he⟩ := Quotient.exists_rep z
  rw [← he]
  have helem : e = X.elementsMk e.obj e.val := by cases e; rfl
  rw [helem]
  have hobj : (NatTrans.mapElements α).obj (X.elementsMk e.obj e.val) =
      Y.elementsMk e.obj (α.app e.obj e.val) := rfl
  simp only [Functor.mapConnectedComponents_mk, hobj,
    elementsConnectedComponentsEquivColimit_apply]
  simpa only [CategoryTheory.comp_apply] using
    (ConcreteCategory.congr_hom (Limits.ι_colimMap α e.obj) e.val).symm

end Functor

end CategoryTheory
