/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Iteration.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Empty-index loop iteration retains free components

In discrete `Bool` with chosen point `false`, two successive empty-index loops
can carry the free value `true`. The class obtained from both empty-loop
homeomorphism inverses is sent by `HomotopyGroup.genLoopEquiv`, followed by the
empty-index comparison, to the component of `true`, not that of `false`.
Thus an empty outer index retains every component rather than forcing the
chosen point.

## References

Mathlib's generalized loops, empty-loop comparisons and sum-flattening
homeomorphism are due to Roberto Alvarez. The same-loop component comparison is
provided by `FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace`.
The component-map API in `FundamentalGroupoids.Topology.Connected.PathConnected`
follows Restricted Product Duality's `HomotopyMaps`, by Formal Frontier Agents.
The separation argument uses Mathlib's path components (Patrick Massot and
contributors) and totally disconnected spaces.
-/

noncomputable section

namespace HomotopyGroup

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot Bool

/-- Both empty-loop inverses retain the free value `true`, despite the chosen
point being `false`. -/
private def emptyBoolTrueClass :
    HomotopyGroup Empty (GenLoop Empty Bool false) GenLoop.const :=
  ⟦(genLoopHomeoOfIsEmpty Empty (GenLoop.const : GenLoop Empty Bool false)).symm
    ((genLoopHomeoOfIsEmpty Empty (false : Bool)).symm true)⟧

/-- Flattening the two empty indices sends the free-value class to the
component of `true`. -/
private theorem emptyBoolTrueClass_component :
    homotopyGroupEquivZerothHomotopyOfIsEmpty (Empty ⊕ Empty) (false : Bool)
        (genLoopEquiv Empty Empty false emptyBoolTrueClass) =
      ZerothHomotopy.mk true := by
  rw [emptyBoolTrueClass, genLoopEquiv_class]
  rfl

/-- The free-value component is not collapsed to the chosen point's component
by empty-index loop iteration. -/
private theorem emptyBoolTrueClass_component_ne_false :
    homotopyGroupEquivZerothHomotopyOfIsEmpty (Empty ⊕ Empty) (false : Bool)
        (genLoopEquiv Empty Empty false emptyBoolTrueClass) ≠
      ZerothHomotopy.mk false := by
  rw [emptyBoolTrueClass_component]
  intro h
  have hjoined : Joined (true : Bool) false := Quotient.exact h
  have hvalues : (false : Bool) = true := by
    simpa only [connectedComponent_eq_singleton, Set.mem_singleton_iff] using
      (pathComponent_subset_component (true : Bool) hjoined)
  cases hvalues

end HomotopyGroup
