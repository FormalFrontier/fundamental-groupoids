/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Connected.PathConnected
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map

/-!
# Empty-index homotopy classes and path components

The canonical equivalence for an empty index type sends the constant class to the
basepoint's path component and commutes with based postcomposition.
-/

@[expose] public section

open scoped Topology

universe uN uX uY

variable {X : Type uX} {Y : Type uY}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The equivalence for an empty index type sends the constant homotopy class to the
path component of the basepoint. -/
theorem homotopyGroupEquivZerothHomotopyOfIsEmpty_const
    (N : Type uN) [IsEmpty N] (x : X) :
    homotopyGroupEquivZerothHomotopyOfIsEmpty N x
        (⟦(GenLoop.const : GenLoop N X x)⟧ : HomotopyGroup N X x) =
      ZerothHomotopy.mk x := by
  rfl

/-- The equivalence for an empty index type commutes with postcomposition by a
basepoint-preserving continuous map. -/
theorem homotopyGroupEquivZerothHomotopyOfIsEmpty_mapFun
    (N : Type uN) [IsEmpty N] {x : X} {y : Y}
    (f : C(X, Y)) (hf : f x = y) (q : HomotopyGroup N X x) :
    homotopyGroupEquivZerothHomotopyOfIsEmpty N y (HomotopyGroup.mapFun N f hf q) =
      ZerothHomotopy.map f (homotopyGroupEquivZerothHomotopyOfIsEmpty N x q) := by
  refine Quotient.inductionOn q ?_
  intro p
  rw [HomotopyGroup.mapFun_class]
  rfl
