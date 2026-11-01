/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based.Coproducts
public import FundamentalGroupoids.Topology.Category.TopCat.Limits.WidePushout.ULift

/-!
# Universe lifting of based wedges

The universe lift of a point-wide-pushout, based at its lifted head, is
isomorphic to the based wedge of the lifted pointed factors. The comparison
preserves the head and every factor inclusion, with underlying-map and
inverse evaluation equations.

The index type may be empty: the common head is retained without choosing
a factor. No separation or local compactness assumptions are needed.

## References

Mathlib's `TopCat.isoOfHomeo` and `CategoryTheory.Under.isoMk` supply the
categorical packaging. The point-wide-pushout universe-lift homeomorphism
and based-wedge formalization of Formal Frontier Agents supply the
underlying comparison and its selected point.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

section

namespace BasedTopCat

/-- The lifted original point-wide-pushout, based at its lifted head, is
isomorphic to the based wedge of the lifted pointed factors. -/
def basedWedgeULiftIso.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j) :
    of (ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
      (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
        TopCat.{max u w}))
      (ULift.up (WidePushout.head
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit)) ≅
      basedWedge (fun j ↦ of (ULift.{v} (X j)) (ULift.up (x j))) :=
  Under.isoMk
    (TopCat.isoOfHomeo
      (X := TopCat.of (ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
          TopCat.{max u w})))
      (Y := (widePushout (TopCat.of PUnit.{max v (max u w) + 1})
        (fun j ↦ TopCat.of (ULift.{v} (X j)))
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
          TopCat.{max v (max u w)}))
      (TopCat.widePushoutPointULiftHomeomorph.{u, v, w} X x)) (by
    rw [hom_eq_const_point (basedWedge (fun j ↦ of (ULift.{v} (X j)) (ULift.up (x j))))]
    apply TopCat.ext
    intro _
    exact TopCat.widePushoutPointULiftHomeomorph_head.{u, v, w} X x PUnit.unit)

/-- The forward based comparison has the point-wide-pushout homeomorphism
as its underlying continuous map. -/
theorem basedWedgeULiftIso_hom_right_hom.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j) :
    (basedWedgeULiftIso.{u, v, w} X x).hom.right.hom =
      (TopCat.widePushoutPointULiftHomeomorph.{u, v, w} X x :
        C(ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
            (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
              TopCat.{max u w}),
          (widePushout (TopCat.of PUnit.{max v (max u w) + 1})
            (fun j ↦ TopCat.of (ULift.{v} (X j)))
            (fun j ↦ (TopCat.const (ULift.up (x j)) :
              TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
              TopCat.{max v (max u w)}))) := rfl

/-- The inverse based comparison has the inverse homeomorphism as its
underlying continuous map. -/
theorem basedWedgeULiftIso_inv_right_hom.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j) :
    (basedWedgeULiftIso.{u, v, w} X x).inv.right.hom =
      ((TopCat.widePushoutPointULiftHomeomorph.{u, v, w} X x).symm :
        C((widePushout (TopCat.of PUnit.{max v (max u w) + 1})
            (fun j ↦ TopCat.of (ULift.{v} (X j)))
            (fun j ↦ (TopCat.const (ULift.up (x j)) :
              TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
              TopCat.{max v (max u w)}),
          ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
            (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
              TopCat.{max u w}))) := rfl

/-- The forward based comparison preserves the lifted original head. -/
@[simp] theorem basedWedgeULiftIso_hom_head.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (q : PUnit.{max u w + 1}) :
    CategoryTheory.ConcreteCategory.hom
      (X := TopCat.of (ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
          TopCat.{max u w})))
      (basedWedgeULiftIso.{u, v, w} X x).hom.right
      (ULift.up (WidePushout.head
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) q)) =
        point (basedWedge (fun j ↦ of (ULift.{v} (X j)) (ULift.up (x j)))) :=
  TopCat.widePushoutPointULiftHomeomorph_head.{u, v, w} X x q

/-- The forward based comparison carries each original factor to the same
lifted-factor inclusion. -/
@[simp] theorem basedWedgeULiftIso_hom_ι.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (j : J) (z : X j) :
    CategoryTheory.ConcreteCategory.hom
      (X := TopCat.of (ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
          TopCat.{max u w})))
      (basedWedgeULiftIso.{u, v, w} X x).hom.right
      (ULift.up (WidePushout.ι
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) j z)) =
        (basedWedgeι (fun k ↦ of (ULift.{v} (X k)) (ULift.up (x k))) j).right
          (ULift.up z) :=
  TopCat.widePushoutPointULiftHomeomorph_ι.{u, v, w} X x j z

/-- The inverse based comparison sends the wedge point to the lifted original head. -/
theorem basedWedgeULiftIso_inv_point.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j) :
    (basedWedgeULiftIso.{u, v, w} X x).inv.right
      (point (basedWedge (fun j ↦ of (ULift.{v} (X j)) (ULift.up (x j))))) =
        ULift.up (WidePushout.head
          (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit) :=
  TopCat.widePushoutPointULiftHomeomorph_symm_head.{u, v, w} X x PUnit.unit

/-- The inverse based comparison sends each lifted factor inclusion to the
lift of its original factor inclusion. -/
@[simp] theorem basedWedgeULiftIso_inv_ι.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (j : J) (z : ULift.{v} (X j)) :
    CategoryTheory.ConcreteCategory.hom
      (Y := TopCat.of (ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
          TopCat.{max u w})))
      (basedWedgeULiftIso.{u, v, w} X x).inv.right
      (CategoryTheory.ConcreteCategory.hom (X := TopCat.of (ULift.{v} (X j)))
        (basedWedgeι (fun k ↦ of (ULift.{v} (X k)) (ULift.up (x k))) j).right z) =
        ULift.up (WidePushout.ι
          (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) j z.down) :=
  TopCat.widePushoutPointULiftHomeomorph_symm_ι.{u, v, w} X x j z

end BasedTopCat

end
