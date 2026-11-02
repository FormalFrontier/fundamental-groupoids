/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based.Coproducts
public import FundamentalGroupoids.Topology.Category.TopCat.Based.FiniteWedge
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# Finite products in the opposite based-homotopy category

The ordinary opposite of `BasedTopCat.HomotopyCategory` has chosen finite products:
the terminal object is the opposite of the empty based wedge, and the binary
product of two objects is the opposite of their ordered two-factor based wedge.
The limiting properties follow from the initiality of the empty wedge and the
binary coproduct property of the two-factor wedge.

`homotopyOppositeCartesianMonoidalCategory` packages these choices using
`CartesianMonoidalCategory.ofChosenFiniteProducts`. Its first projection is the
opposite of the left wedge inclusion, and its second projection is the opposite
of the right wedge inclusion. For three possibly different factors, the unop of
its associator followed by left-nested flattening agrees with right-nested
flattening in the based-homotopy category, preserving the order `0`, `1`, `2`.

## Implementation notes

The cartesian structure is a named definition, not a global instance. The
monoidal-notation equations use this structure. The binary cocone supplied by
`basedWedgePairHomotopyCofan` already compares the mapped pair diagram with the
pair of quotient objects; taking its binary opposite preserves the leg order.

## References

* Mathlib's `BinaryCofan.op`, `BinaryCofan.IsColimit.op` and `IsInitial.op`
  supply passage to the ordinary opposite category.
* Mathlib's `CartesianMonoidalCategory.ofChosenFiniteProducts` supplies the
  cartesian monoidal structure from the chosen limit cones. Its projection
  equations and product extensionality characterize the associator.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace BasedTopCat

/-- The terminal limit cone in the opposite based-homotopy category, chosen as
    the opposite of the empty based wedge. -/
def homotopyOppositeTerminalLimitCone :
    LimitCone (Functor.empty.{0} HomotopyCategory.{u}ᵒᵖ) where
  cone := asEmptyCone
    (op (homotopyQuotient.obj
      (basedWedge (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u})))))
  isLimit := IsInitial.op HomotopyCategory.{u}
    (basedWedgeHomotopyIsInitial
      (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u})))

/-- The chosen terminal cone has the opposite empty-wedge vertex. -/
theorem homotopyOppositeTerminalLimitCone_pt :
    homotopyOppositeTerminalLimitCone.{u}.cone.pt =
      op (homotopyQuotient.obj
        (basedWedge (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u})))) := rfl

/-- The binary limit cone in the opposite based-homotopy category, chosen by
    taking the opposite of the ordered two-factor based-wedge cocone. -/
def homotopyOppositeBinaryLimitCone (X Y : HomotopyCategory.{u}ᵒᵖ) :
    LimitCone (pair X Y) := by
  -- Both the category quotient and the opposite have single-field object wrappers.
  -- Their eta equalities identify these representatives with the given objects.
  change LimitCone (pair
    (op (homotopyQuotient.obj X.unop.as))
    (op (homotopyQuotient.obj Y.unop.as)))
  exact {
    cone := BinaryCofan.op (basedWedgePairHomotopyCofan X.unop.as Y.unop.as)
    isLimit := BinaryCofan.IsColimit.op
      (basedWedgePairHomotopyCofanIsColimit X.unop.as Y.unop.as) }

/-- The chosen binary cone has the opposite two-factor-wedge vertex. -/
theorem homotopyOppositeBinaryLimitCone_pt (X Y : HomotopyCategory.{u}ᵒᵖ) :
    (homotopyOppositeBinaryLimitCone X Y).cone.pt =
      op (homotopyQuotient.obj (basedWedge (pairFunction X.unop.as Y.unop.as))) := rfl

/-- The first projection is the opposite of the left based-wedge inclusion. -/
theorem homotopyOppositeBinaryLimitCone_fst (X Y : HomotopyCategory.{u}ᵒᵖ) :
    BinaryFan.fst ((homotopyOppositeBinaryLimitCone X Y).cone) =
      (homotopyQuotient.map
        (basedWedgeι (pairFunction X.unop.as Y.unop.as) WalkingPair.left)).op :=
  congrArg Quiver.Hom.op (basedWedgePairHomotopyCofan_inl X.unop.as Y.unop.as)

/-- The second projection is the opposite of the right based-wedge inclusion. -/
theorem homotopyOppositeBinaryLimitCone_snd (X Y : HomotopyCategory.{u}ᵒᵖ) :
    BinaryFan.snd ((homotopyOppositeBinaryLimitCone X Y).cone) =
      (homotopyQuotient.map
        (basedWedgeι (pairFunction X.unop.as Y.unop.as) WalkingPair.right)).op :=
  congrArg Quiver.Hom.op (basedWedgePairHomotopyCofan_inr X.unop.as Y.unop.as)

/-- The cartesian monoidal structure on the ordinary opposite based-homotopy
    category determined by the empty and ordered binary based wedges. -/
@[instance_reducible]
def homotopyOppositeCartesianMonoidalCategory :
    CartesianMonoidalCategory HomotopyCategory.{u}ᵒᵖ :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    homotopyOppositeTerminalLimitCone homotopyOppositeBinaryLimitCone

section Cartesian

attribute [local instance] homotopyOppositeCartesianMonoidalCategory

open MonoidalCategory

/-- The tensor unit of the chosen cartesian structure is the opposite empty wedge. -/
theorem homotopyOpposite_tensorUnit :
    𝟙_ (HomotopyCategory.{u}ᵒᵖ) =
      op (homotopyQuotient.obj
        (basedWedge (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u})))) :=
  homotopyOppositeTerminalLimitCone_pt

/-- The tensor product of the chosen cartesian structure is the opposite ordered wedge. -/
theorem homotopyOpposite_tensorObj (X Y : HomotopyCategory.{u}ᵒᵖ) :
    X ⊗ Y =
      op (homotopyQuotient.obj (basedWedge (pairFunction X.unop.as Y.unop.as))) :=
  homotopyOppositeBinaryLimitCone_pt X Y

/-- The first cartesian projection is the opposite left wedge inclusion. -/
theorem homotopyOpposite_fst (X Y : HomotopyCategory.{u}ᵒᵖ) :
    CartesianMonoidalCategory.fst X Y =
      (homotopyQuotient.map
        (basedWedgeι (pairFunction X.unop.as Y.unop.as) WalkingPair.left)).op :=
  homotopyOppositeBinaryLimitCone_fst X Y

/-- The second cartesian projection is the opposite right wedge inclusion. -/
theorem homotopyOpposite_snd (X Y : HomotopyCategory.{u}ᵒᵖ) :
    CartesianMonoidalCategory.snd X Y =
      (homotopyQuotient.map
        (basedWedgeι (pairFunction X.unop.as Y.unop.as) WalkingPair.right)).op :=
  homotopyOppositeBinaryLimitCone_snd X Y

/-- The map to the tensor unit is opposite to descent from the empty based wedge. -/
theorem homotopyOpposite_toUnit (X : HomotopyCategory.{u}ᵒᵖ) :
    CartesianMonoidalCategory.toUnit X =
      (basedWedgeHomotopyDesc
        (fun j : PEmpty.{1} ↦ (isEmptyElim j : BasedTopCat.{u})) X.unop
        (fun j ↦ isEmptyElim j)).op :=
  CartesianMonoidalCategory.toUnit_unique _ _

/-- In the based-homotopy category, the unop of the chosen cartesian associator
followed by left-nested flattening equals right-nested flattening. -/
theorem homotopyOpposite_associator_unop_comp_finThreeLeft
    (D : Fin 3 → BasedTopCat.{u}) :
    (α_ (op (homotopyQuotient.obj (D 0)))
      (op (homotopyQuotient.obj (D 1)))
      (op (homotopyQuotient.obj (D 2)))).hom.unop ≫
        homotopyQuotient.map (basedWedgeFinThreeLeftIso D).hom =
      homotopyQuotient.map (basedWedgeFinThreeRightIso D).hom := by
  let ι01 (j : WalkingPair) : pairFunction (D 0) (D 1) j ⟶
      basedWedge (pairFunction (D 0) (D 1)) :=
    basedWedgeι (pairFunction (D 0) (D 1)) j
  let ιLeft (j : WalkingPair) :
      pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2) j ⟶
        basedWedge (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2)) :=
    basedWedgeι (pairFunction (basedWedge (pairFunction (D 0) (D 1))) (D 2)) j
  let ι12 (j : WalkingPair) : pairFunction (D 1) (D 2) j ⟶
      basedWedge (pairFunction (D 1) (D 2)) :=
    basedWedgeι (pairFunction (D 1) (D 2)) j
  let ιRight (j : WalkingPair) :
      pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2))) j ⟶
        basedWedge (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2)))) :=
    basedWedgeι (pairFunction (D 0) (basedWedge (pairFunction (D 1) (D 2)))) j
  -- Apply functoriality to typed factors before reversing composition in the opposite.
  have map_comp_op {X Y Z : BasedTopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
      (homotopyQuotient.map (f ≫ g)).op =
        (homotopyQuotient.map g).op ≫ (homotopyQuotient.map f).op :=
    (congrArg Quiver.Hom.op (homotopyQuotient.map_comp f g)).trans op_comp
  have map_comp_comp_op {W X Y Z : BasedTopCat.{u}}
      (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
      (homotopyQuotient.map ((f ≫ g) ≫ h)).op =
        (homotopyQuotient.map h).op ≫
          (homotopyQuotient.map g).op ≫ (homotopyQuotient.map f).op :=
    (map_comp_op (f ≫ g) h).trans
      (congrArg (fun k : op (homotopyQuotient.obj Y) ⟶ op (homotopyQuotient.obj W) ↦
        (homotopyQuotient.map h).op ≫ k) (map_comp_op f g))
  -- In the opposite, product extensionality reduces to the three ordered leaves.
  apply Quiver.Hom.op_inj
  rw [op_comp, Quiver.Hom.op_unop]
  apply CartesianMonoidalCategory.hom_ext
    (X := op (homotopyQuotient.obj (D 0)))
    (Y := op (homotopyQuotient.obj (D 1)) ⊗ op (homotopyQuotient.obj (D 2)))
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun f ↦ (homotopyQuotient.map (basedWedgeFinThreeLeftIso D).hom).op ≫ f)
      (CartesianMonoidalCategory.associator_hom_fst
        (op (homotopyQuotient.obj (D 0))) (op (homotopyQuotient.obj (D 1)))
        (op (homotopyQuotient.obj (D 2))))).trans ?_
    simp only [homotopyOpposite_fst]
    exact (map_comp_comp_op (ι01 WalkingPair.left) (ιLeft WalkingPair.left)
      (basedWedgeFinThreeLeftIso D).hom).symm.trans
        ((congrArg (fun f ↦ (homotopyQuotient.map f).op)
          ((basedWedgeFinThreeLeftIso_ι_zero_hom D).trans
            (basedWedgeFinThreeRightIso_ι_zero_hom D).symm)).trans
              (map_comp_op (ιRight WalkingPair.left) (basedWedgeFinThreeRightIso D).hom))
  · apply CartesianMonoidalCategory.hom_ext
      (X := op (homotopyQuotient.obj (D 1))) (Y := op (homotopyQuotient.obj (D 2)))
    · refine (Category.assoc _ _ _).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun f ↦ (homotopyQuotient.map (basedWedgeFinThreeLeftIso D).hom).op ≫ f)
        (CartesianMonoidalCategory.associator_hom_snd_fst
          (op (homotopyQuotient.obj (D 0))) (op (homotopyQuotient.obj (D 1)))
          (op (homotopyQuotient.obj (D 2))))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      simp only [homotopyOpposite_fst, homotopyOpposite_snd]
      exact (map_comp_comp_op (ι01 WalkingPair.right) (ιLeft WalkingPair.left)
        (basedWedgeFinThreeLeftIso D).hom).symm.trans
          ((congrArg (fun f ↦ (homotopyQuotient.map f).op)
            ((basedWedgeFinThreeLeftIso_ι_one_hom D).trans
              (basedWedgeFinThreeRightIso_ι_one_hom D).symm)).trans
                (map_comp_comp_op (ι12 WalkingPair.left) (ιRight WalkingPair.right)
                  (basedWedgeFinThreeRightIso D).hom))
    · refine (Category.assoc _ _ _).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (fun f ↦ (homotopyQuotient.map (basedWedgeFinThreeLeftIso D).hom).op ≫ f)
        (CartesianMonoidalCategory.associator_hom_snd_snd
          (op (homotopyQuotient.obj (D 0))) (op (homotopyQuotient.obj (D 1)))
          (op (homotopyQuotient.obj (D 2))))).trans ?_
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      simp only [homotopyOpposite_snd]
      exact (map_comp_op (ιLeft WalkingPair.right) (basedWedgeFinThreeLeftIso D).hom).symm.trans
        ((congrArg (fun f ↦ (homotopyQuotient.map f).op)
          ((basedWedgeFinThreeLeftIso_ι_two_hom D).trans
            (basedWedgeFinThreeRightIso_ι_two_hom D).symm)).trans
              (map_comp_comp_op (ι12 WalkingPair.right) (ιRight WalkingPair.right)
                (basedWedgeFinThreeRightIso D).hom))

end Cartesian

end BasedTopCat
