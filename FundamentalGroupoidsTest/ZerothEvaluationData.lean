/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Connected.ZerothHomotopy

/-!
# Distinct path components of the discrete Boolean space

Evaluation through the totally disconnected homeomorphism distinguishes the classes
of `false` and `true` in `ZerothHomotopy Bool` for the discrete topology.
-/

@[expose] public section

section

/-- The discrete topology used for Boolean path-class separation. -/
local instance boolTopology : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot Bool

example : (ZerothHomotopy.mk false : ZerothHomotopy Bool) ≠ ZerothHomotopy.mk true := by
  intro h
  have h' : false = true := by
    simpa only [ZerothHomotopy.homeomorphOfTotallyDisconnectedSpace_mk] using
      congrArg (ZerothHomotopy.homeomorphOfTotallyDisconnectedSpace (X := Bool)) h
  cases h'

end
