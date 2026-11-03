/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Connected.ZerothHomotopy

/-!
# Homeomorphisms of path-component spaces

The map on path components induced by a continuous map is continuous for the
quotient topologies. A homotopy equivalence therefore induces a homeomorphism
whose underlying equivalence is the canonical equivalence on path components.
-/

@[expose] public section

open scoped Topology

universe u v

namespace ZerothHomotopy

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The induced map on path-component spaces is continuous. -/
theorem continuous_map (f : C(X, Y)) : Continuous (map f) := by
  apply isQuotientMap_mk.continuous_iff.mpr
  have h : (map f ∘ (mk : X → ZerothHomotopy X)) =
      (mkContinuousMap : C(Y, ZerothHomotopy Y)) ∘ f := by
    funext x
    exact (map_mk f x).trans (mkContinuousMap_apply (f x)).symm
  rw [h]
  exact (mkContinuousMap : C(Y, ZerothHomotopy Y)).continuous.comp f.continuous

/-- A homotopy equivalence induces a homeomorphism of path-component spaces. -/
noncomputable def homeomorphOfHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    ZerothHomotopy X ≃ₜ ZerothHomotopy Y where
  toEquiv := equivOfHomotopyEquiv e
  continuous_toFun := by
    change Continuous (equivOfHomotopyEquiv e : ZerothHomotopy X → ZerothHomotopy Y)
    rw [coe_equivOfHomotopyEquiv]
    exact continuous_map e.toFun
  continuous_invFun := by
    change Continuous ((equivOfHomotopyEquiv e).symm :
      ZerothHomotopy Y → ZerothHomotopy X)
    rw [equivOfHomotopyEquiv_symm, coe_equivOfHomotopyEquiv]
    exact continuous_map e.symm.toFun

/-- The induced homeomorphism has the canonical underlying equivalence. -/
theorem homeomorphOfHomotopyEquiv_toEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    (homeomorphOfHomotopyEquiv e).toEquiv = equivOfHomotopyEquiv e := by
  rfl

/-- The induced homeomorphism sends the class of a point to the class of its image. -/
theorem homeomorphOfHomotopyEquiv_mk (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    homeomorphOfHomotopyEquiv e (mk x) = mk (e x) := by
  exact equivOfHomotopyEquiv_mk e x

end ZerothHomotopy
