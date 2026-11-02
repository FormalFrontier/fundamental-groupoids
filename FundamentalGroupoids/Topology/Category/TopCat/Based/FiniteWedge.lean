/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based.Coproducts
import Mathlib.Tactic.FinCases

/-!
# Ordered finite based wedges

The wedge of a `Fin 2` family is compared with the wedge indexed by
`WalkingPair`, with `0` sent to `left` and `1` to `right`. The two nested binary
wedges of a `Fin 3` family are compared with its three-factor wedge, with leaves
sent to `0`, `1`, `2` in that order. The factors may be different based spaces,
and all spaces lie in an arbitrary common universe.

Each forward and inverse map is built with `basedWedgeDesc`. Thus these are
comparisons in `BasedTopCat`, before passage to based homotopy. Their images in
the based-homotopy category are obtained with the existing
`homotopyQuotient.mapIso`; no additional mapped-isomorphism definitions are needed.

## Implementation notes

The inverse laws and ordered-leg equations are strict equalities of based maps,
proved using the coproduct descent and extensionality API. No separation,
local compactness, connectedness or condition on the basepoints is required.

## References

* The based-wedge descent and extensionality API of Formal Frontier Agents
  supplies the coproduct universal properties.
* Mathlib supplies `WalkingPair`, finite case analysis and categorical
  isomorphisms, including functorial transport by `Functor.mapIso`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace BasedTopCat

/-- The two-factor wedge, with factor `0` on the left and factor `1` on the right. -/
def basedWedgeFinTwoIso (D : Fin 2 → BasedTopCat.{u}) :
    basedWedge D ≅ basedWedge (pairFunction (D 0) (D 1)) where
  hom := basedWedgeDesc D
    (Fin.cases
      (motive := fun j : Fin 2 ↦
        D j ⟶ basedWedge (pairFunction (D 0) (D 1)))
      (basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.left)
      (Fin.cases
        (basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.right)
        (fun j : Fin 0 ↦ Fin.elim0 j)))
  inv := basedWedgeDesc (pairFunction (D 0) (D 1))
    (fun j ↦ match j with
      | WalkingPair.left => basedWedgeι D 0
      | WalkingPair.right => basedWedgeι D 1)
  hom_inv_id := by
    apply basedWedge_hom_ext D
    intro j
    rw [← Category.assoc, basedWedgeι_desc, Category.comp_id]
    fin_cases j
    · exact basedWedgeι_desc (pairFunction (D 0) (D 1)) _ WalkingPair.left
    · exact basedWedgeι_desc (pairFunction (D 0) (D 1)) _ WalkingPair.right
  inv_hom_id := by
    apply basedWedge_hom_ext (pairFunction (D 0) (D 1))
    intro j
    rw [← Category.assoc, basedWedgeι_desc, Category.comp_id]
    cases j
    · exact basedWedgeι_desc D _ 0
    · exact basedWedgeι_desc D _ 1

/-- Factor `0` is sent to the left factor. -/
theorem basedWedgeFinTwoIso_ι_zero_hom (D : Fin 2 → BasedTopCat.{u}) :
    basedWedgeι D 0 ≫ (basedWedgeFinTwoIso D).hom =
      basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.left := by
  exact basedWedgeι_desc D _ 0

/-- Factor `1` is sent to the right factor. -/
theorem basedWedgeFinTwoIso_ι_one_hom (D : Fin 2 → BasedTopCat.{u}) :
    basedWedgeι D 1 ≫ (basedWedgeFinTwoIso D).hom =
      basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.right := by
  exact basedWedgeι_desc D _ 1

/-- The inverse sends the left factor to factor `0`. -/
theorem basedWedgeFinTwoIso_ι_left_inv (D : Fin 2 → BasedTopCat.{u}) :
    basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.left ≫
        (basedWedgeFinTwoIso D).inv = basedWedgeι D 0 := by
  exact basedWedgeι_desc (pairFunction (D 0) (D 1)) _ WalkingPair.left

/-- The inverse sends the right factor to factor `1`. -/
theorem basedWedgeFinTwoIso_ι_right_inv (D : Fin 2 → BasedTopCat.{u}) :
    basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.right ≫
        (basedWedgeFinTwoIso D).inv = basedWedgeι D 1 := by
  exact basedWedgeι_desc (pairFunction (D 0) (D 1)) _ WalkingPair.right

/-- The forward comparison preserves the common point. -/
theorem basedWedgeFinTwoIso_hom_point (D : Fin 2 → BasedTopCat.{u}) :
    (basedWedgeFinTwoIso D).hom.right.hom (point (basedWedge D)) =
      point (basedWedge (pairFunction (D 0) (D 1))) :=
  map_point (basedWedgeFinTwoIso D).hom

/-- The inverse comparison preserves the common point. -/
theorem basedWedgeFinTwoIso_inv_point (D : Fin 2 → BasedTopCat.{u}) :
    (basedWedgeFinTwoIso D).inv.right.hom
        (point (basedWedge (pairFunction (D 0) (D 1)))) =
      point (basedWedge D) :=
  map_point (basedWedgeFinTwoIso D).inv

/-- Flatten the left-nested binary wedge into factors `0`, `1`, `2`, in that order. -/
def basedWedgeFinThreeLeftIso (D : Fin 3 → BasedTopCat.{u}) :
    basedWedge
        (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2)) ≅
      basedWedge D where
  hom := basedWedgeDesc
    (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
    (fun j ↦ match j with
      | WalkingPair.left => basedWedgeDesc (pairFunction (D 0) (D 1))
          (fun k ↦ match k with
            | WalkingPair.left => basedWedgeι D 0
            | WalkingPair.right => basedWedgeι D 1)
      | WalkingPair.right => basedWedgeι D 2)
  inv := basedWedgeDesc D
    (Fin.cases
      (motive := fun j : Fin 3 ↦ D j ⟶
        basedWedge
          (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2)))
      (basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.left ≫
        basedWedgeι
          (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
          WalkingPair.left)
      (Fin.cases
        (basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.right ≫
          basedWedgeι
            (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
            WalkingPair.left)
        (Fin.cases
          (basedWedgeι
            (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
            WalkingPair.right)
          (fun j : Fin 0 ↦ Fin.elim0 j))))
  hom_inv_id := by
    apply basedWedge_hom_ext
      (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
    intro j
    cases j with
    | left =>
        rw [← Category.assoc, basedWedgeι_desc, Category.comp_id]
        apply basedWedge_hom_ext (pairFunction (D 0) (D 1))
        intro k
        cases k with
        | left =>
            exact (basedWedgeι_desc_assoc (pairFunction (D 0) (D 1))
              _ WalkingPair.left _).trans (basedWedgeι_desc D _ 0)
        | right =>
            exact (basedWedgeι_desc_assoc (pairFunction (D 0) (D 1))
              _ WalkingPair.right _).trans (basedWedgeι_desc D _ 1)
    | right =>
        rw [← Category.assoc, basedWedgeι_desc, Category.comp_id]
        exact basedWedgeι_desc D _ 2
  inv_hom_id := by
    apply basedWedge_hom_ext D
    intro j
    rw [← Category.assoc, basedWedgeι_desc, Category.comp_id]
    fin_cases j
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun f ↦ basedWedgeι (pairFunction (D 0) (D 1))
        WalkingPair.left ≫ f) (basedWedgeι_desc
          (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
          _ WalkingPair.left)).trans ?_
      exact basedWedgeι_desc (pairFunction (D 0) (D 1)) _ WalkingPair.left
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun f ↦ basedWedgeι (pairFunction (D 0) (D 1))
        WalkingPair.right ≫ f) (basedWedgeι_desc
          (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
          _ WalkingPair.left)).trans ?_
      exact basedWedgeι_desc (pairFunction (D 0) (D 1)) _ WalkingPair.right
    · exact basedWedgeι_desc
        (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2)) _ WalkingPair.right

/-- The left leaf of the left branch is sent to factor `0`. -/
theorem basedWedgeFinThreeLeftIso_ι_zero_hom (D : Fin 3 → BasedTopCat.{u}) :
    (basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.left ≫
        basedWedgeι
          (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
          WalkingPair.left) ≫ (basedWedgeFinThreeLeftIso D).hom =
      basedWedgeι D 0 := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun f ↦ basedWedgeι (pairFunction (D 0) (D 1))
    WalkingPair.left ≫ f) (basedWedgeι_desc
      (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
      _ WalkingPair.left)).trans ?_
  exact basedWedgeι_desc (pairFunction (D 0) (D 1)) _ WalkingPair.left

/-- The right leaf of the left branch is sent to factor `1`. -/
theorem basedWedgeFinThreeLeftIso_ι_one_hom (D : Fin 3 → BasedTopCat.{u}) :
    (basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.right ≫
        basedWedgeι
          (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
          WalkingPair.left) ≫ (basedWedgeFinThreeLeftIso D).hom =
      basedWedgeι D 1 := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun f ↦ basedWedgeι (pairFunction (D 0) (D 1))
    WalkingPair.right ≫ f) (basedWedgeι_desc
      (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
      _ WalkingPair.left)).trans ?_
  exact basedWedgeι_desc (pairFunction (D 0) (D 1)) _ WalkingPair.right

/-- The right branch is sent to factor `2`. -/
theorem basedWedgeFinThreeLeftIso_ι_two_hom (D : Fin 3 → BasedTopCat.{u}) :
    basedWedgeι
        (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
        WalkingPair.right ≫ (basedWedgeFinThreeLeftIso D).hom =
      basedWedgeι D 2 := by
  exact basedWedgeι_desc
    (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2)) _ WalkingPair.right

/-- The inverse sends factor `0` to the left leaf of the left branch. -/
theorem basedWedgeFinThreeLeftIso_ι_zero_inv (D : Fin 3 → BasedTopCat.{u}) :
    basedWedgeι D 0 ≫ (basedWedgeFinThreeLeftIso D).inv =
      basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.left ≫
        basedWedgeι
          (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
          WalkingPair.left := by
  exact basedWedgeι_desc D _ 0

/-- The inverse sends factor `1` to the right leaf of the left branch. -/
theorem basedWedgeFinThreeLeftIso_ι_one_inv (D : Fin 3 → BasedTopCat.{u}) :
    basedWedgeι D 1 ≫ (basedWedgeFinThreeLeftIso D).inv =
      basedWedgeι (pairFunction (D 0) (D 1)) WalkingPair.right ≫
        basedWedgeι
          (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
          WalkingPair.left := by
  exact basedWedgeι_desc D _ 1

/-- The inverse sends factor `2` to the right branch. -/
theorem basedWedgeFinThreeLeftIso_ι_two_inv (D : Fin 3 → BasedTopCat.{u}) :
    basedWedgeι D 2 ≫ (basedWedgeFinThreeLeftIso D).inv =
      basedWedgeι
        (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))
        WalkingPair.right := by
  exact basedWedgeι_desc D _ 2

/-- Left-nested flattening preserves the common point. -/
theorem basedWedgeFinThreeLeftIso_hom_point (D : Fin 3 → BasedTopCat.{u}) :
    (basedWedgeFinThreeLeftIso D).hom.right.hom
        (point (basedWedge
          (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2)))) =
      point (basedWedge D) :=
  map_point (basedWedgeFinThreeLeftIso D).hom

/-- The inverse of left-nested flattening preserves the common point. -/
theorem basedWedgeFinThreeLeftIso_inv_point (D : Fin 3 → BasedTopCat.{u}) :
    (basedWedgeFinThreeLeftIso D).inv.right.hom (point (basedWedge D)) =
      point (basedWedge
        (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2))) :=
  map_point (basedWedgeFinThreeLeftIso D).inv

/-- Flatten the right-nested binary wedge into factors `0`, `1`, `2`, in that order. -/
def basedWedgeFinThreeRightIso (D : Fin 3 → BasedTopCat.{u}) :
    basedWedge
        (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2)))) ≅
      basedWedge D where
  hom := basedWedgeDesc
    (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
    (fun j ↦ match j with
      | WalkingPair.left => basedWedgeι D 0
      | WalkingPair.right => basedWedgeDesc (pairFunction (D 1) (D 2))
          (fun k ↦ match k with
            | WalkingPair.left => basedWedgeι D 1
            | WalkingPair.right => basedWedgeι D 2))
  inv := basedWedgeDesc D
    (Fin.cases
      (motive := fun j : Fin 3 ↦ D j ⟶
        basedWedge
          (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2)))))
      (basedWedgeι
        (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
        WalkingPair.left)
      (Fin.cases
        (basedWedgeι (pairFunction (D 1) (D 2)) WalkingPair.left ≫
          basedWedgeι
            (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
            WalkingPair.right)
        (Fin.cases
          (basedWedgeι (pairFunction (D 1) (D 2)) WalkingPair.right ≫
            basedWedgeι
              (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
              WalkingPair.right)
          (fun j : Fin 0 ↦ Fin.elim0 j))))
  hom_inv_id := by
    apply basedWedge_hom_ext
      (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
    intro j
    cases j with
    | left =>
        rw [← Category.assoc, basedWedgeι_desc, Category.comp_id]
        exact basedWedgeι_desc D _ 0
    | right =>
        rw [← Category.assoc, basedWedgeι_desc, Category.comp_id]
        apply basedWedge_hom_ext (pairFunction (D 1) (D 2))
        intro k
        cases k with
        | left =>
            exact (basedWedgeι_desc_assoc (pairFunction (D 1) (D 2))
              _ WalkingPair.left _).trans (basedWedgeι_desc D _ 1)
        | right =>
            exact (basedWedgeι_desc_assoc (pairFunction (D 1) (D 2))
              _ WalkingPair.right _).trans (basedWedgeι_desc D _ 2)
  inv_hom_id := by
    apply basedWedge_hom_ext D
    intro j
    rw [← Category.assoc, basedWedgeι_desc, Category.comp_id]
    fin_cases j
    · exact basedWedgeι_desc
        (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2)))) _ WalkingPair.left
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun f ↦ basedWedgeι (pairFunction (D 1) (D 2))
        WalkingPair.left ≫ f) (basedWedgeι_desc
          (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
          _ WalkingPair.right)).trans ?_
      exact basedWedgeι_desc (pairFunction (D 1) (D 2)) _ WalkingPair.left
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun f ↦ basedWedgeι (pairFunction (D 1) (D 2))
        WalkingPair.right ≫ f) (basedWedgeι_desc
          (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
          _ WalkingPair.right)).trans ?_
      exact basedWedgeι_desc (pairFunction (D 1) (D 2)) _ WalkingPair.right

/-- The left branch is sent to factor `0`. -/
theorem basedWedgeFinThreeRightIso_ι_zero_hom (D : Fin 3 → BasedTopCat.{u}) :
    basedWedgeι
        (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
        WalkingPair.left ≫ (basedWedgeFinThreeRightIso D).hom =
      basedWedgeι D 0 := by
  exact basedWedgeι_desc
    (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2)))) _ WalkingPair.left

/-- The left leaf of the right branch is sent to factor `1`. -/
theorem basedWedgeFinThreeRightIso_ι_one_hom (D : Fin 3 → BasedTopCat.{u}) :
    (basedWedgeι (pairFunction (D 1) (D 2)) WalkingPair.left ≫
        basedWedgeι
          (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
          WalkingPair.right) ≫ (basedWedgeFinThreeRightIso D).hom =
      basedWedgeι D 1 := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun f ↦ basedWedgeι (pairFunction (D 1) (D 2))
    WalkingPair.left ≫ f) (basedWedgeι_desc
      (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
      _ WalkingPair.right)).trans ?_
  exact basedWedgeι_desc (pairFunction (D 1) (D 2)) _ WalkingPair.left

/-- The right leaf of the right branch is sent to factor `2`. -/
theorem basedWedgeFinThreeRightIso_ι_two_hom (D : Fin 3 → BasedTopCat.{u}) :
    (basedWedgeι (pairFunction (D 1) (D 2)) WalkingPair.right ≫
        basedWedgeι
          (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
          WalkingPair.right) ≫ (basedWedgeFinThreeRightIso D).hom =
      basedWedgeι D 2 := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun f ↦ basedWedgeι (pairFunction (D 1) (D 2))
    WalkingPair.right ≫ f) (basedWedgeι_desc
      (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
      _ WalkingPair.right)).trans ?_
  exact basedWedgeι_desc (pairFunction (D 1) (D 2)) _ WalkingPair.right

/-- The inverse sends factor `0` to the left branch. -/
theorem basedWedgeFinThreeRightIso_ι_zero_inv (D : Fin 3 → BasedTopCat.{u}) :
    basedWedgeι D 0 ≫ (basedWedgeFinThreeRightIso D).inv =
      basedWedgeι
        (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
        WalkingPair.left := by
  exact basedWedgeι_desc D _ 0

/-- The inverse sends factor `1` to the left leaf of the right branch. -/
theorem basedWedgeFinThreeRightIso_ι_one_inv (D : Fin 3 → BasedTopCat.{u}) :
    basedWedgeι D 1 ≫ (basedWedgeFinThreeRightIso D).inv =
      basedWedgeι (pairFunction (D 1) (D 2)) WalkingPair.left ≫
        basedWedgeι
          (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
          WalkingPair.right := by
  exact basedWedgeι_desc D _ 1

/-- The inverse sends factor `2` to the right leaf of the right branch. -/
theorem basedWedgeFinThreeRightIso_ι_two_inv (D : Fin 3 → BasedTopCat.{u}) :
    basedWedgeι D 2 ≫ (basedWedgeFinThreeRightIso D).inv =
      basedWedgeι (pairFunction (D 1) (D 2)) WalkingPair.right ≫
        basedWedgeι
          (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))
          WalkingPair.right := by
  exact basedWedgeι_desc D _ 2

/-- Right-nested flattening preserves the common point. -/
theorem basedWedgeFinThreeRightIso_hom_point (D : Fin 3 → BasedTopCat.{u}) :
    (basedWedgeFinThreeRightIso D).hom.right.hom
        (point (basedWedge
          (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2)))))) =
      point (basedWedge D) :=
  map_point (basedWedgeFinThreeRightIso D).hom

/-- The inverse of right-nested flattening preserves the common point. -/
theorem basedWedgeFinThreeRightIso_inv_point (D : Fin 3 → BasedTopCat.{u}) :
    (basedWedgeFinThreeRightIso D).inv.right.hom (point (basedWedge D)) =
      point (basedWedge
        (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))))) :=
  map_point (basedWedgeFinThreeRightIso D).inv

end BasedTopCat
