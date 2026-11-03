/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.Discrete

/-!
# Point separation in a discrete two-point space

The canonical fundamental-groupoid equivalence retains the two points of discrete `Bool`
as distinct objects in the discrete category.
-/

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot Bool

example :
    (FundamentalGroupoid.equivDiscreteOfTotallyDisconnectedSpace (X := Bool)).functor.obj
        (FundamentalGroupoid.fromTop (X := TopCat.of Bool) false) ≠
      (FundamentalGroupoid.equivDiscreteOfTotallyDisconnectedSpace (X := Bool)).functor.obj
        (FundamentalGroupoid.fromTop (X := TopCat.of Bool) true) := by
  rw [FundamentalGroupoid.equivDiscreteOfTotallyDisconnectedSpace_obj,
    FundamentalGroupoid.equivDiscreteOfTotallyDisconnectedSpace_obj]
  intro h
  cases CategoryTheory.Discrete.eq_of_hom (CategoryTheory.eqToHom h)
