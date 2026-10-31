/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Covering.HomotopyGroup
import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Affine

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Higher homotopy quotients of the circle

For every index type with at least two elements and every basepoint, the circle's
homotopy quotient is subsingleton. For indices `Fin (n + 2)`, this is May's
vanishing of the circle's homotopy groups in finite degrees at least two.

## Implementation notes

`HomotopyGroup N Circle z` is Mathlib's quotient of generalized loops by homotopy
relative to `Cube.boundary N`, the union of coordinate faces. The index type may
be infinite; no identification of this boundary with a topological frontier or a
sphere is asserted. The conclusion concerns homotopy classes, not constancy of
representatives, and requires neither decidable equality on `N` nor a group instance.

The relevant covering is Mathlib's `Circle.exp`, parametrized in radians rather
than with period one. `Circle.isCoveringMap_exp` supplies its covering property,
and `Circle.exp_arg` gives the preimage `Complex.arg (z : ℂ)` of any basepoint `z`.
No continuity of `Complex.arg` is asserted.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 9, §4,
  p. 66, for the finite-degree circle calculation.
* Mathlib's `Mathlib.Topology.Homotopy.HomotopyGroup` supplies the generalized-loop
  quotient and its coordinate-face boundary.
* Mathlib's `Mathlib.Analysis.SpecialFunctions.Complex.Circle` supplies the
  exponential covering and `Circle.exp_arg`.
-/

@[expose] public section

universe u

/-- The circle's generalized-loop homotopy quotient at any basepoint is subsingleton
for every index type with at least two elements. This extends May's finite-degree
vanishing result (Chapter 9, §4, p. 66) to arbitrary index types with Mathlib's
coordinate-face boundary. -/
theorem Circle.subsingleton_homotopyGroup (N : Type u) [Nontrivial N] (z : Circle) :
    Subsingleton (HomotopyGroup N Circle z) := by
  let : Subsingleton (HomotopyGroup N ℝ (Complex.arg (z : ℂ))) :=
    HomotopyGroup.subsingleton N _
  simpa only [ContinuousMap.coe_mk, Circle.exp_arg] using
    (Circle.isCoveringMap_exp.bijective_homotopyGroup_mapFun N
      (Complex.arg (z : ℂ))).2.subsingleton
