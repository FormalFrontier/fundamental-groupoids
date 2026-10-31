/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Affine
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Generalized loops in real topological vector spaces

A generalized loop in a real topological vector space is homotopic to the
constant generalized loop, with the homotopy fixed on the cube boundary.
Consequently its boundary-relative homotopy quotient is a subsingleton.

The cube index and target have independent universes. The index may be empty,
and the chosen point is arbitrary. These statements use Mathlib's generalized
loops and their homotopy quotient; no positive-degree group structure is needed.

## References

The affine interpolation uses `ContinuousMap.Homotopy.affine` by Yury G. Kudryashov
and Mathlib's straight segment paths by Patrick Massot and Yury Kudryashov.
The generalized loops and homotopy groups are due to Roberto Alvarez, and the
relative homotopies to Shing Tak Lam and contributors.
-/

@[expose] public section

universe u v

variable {E : Type v} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

namespace GenLoop

/-- Every generalized loop in a real topological vector space is homotopic,
relative to its cube boundary, to the constant loop at its chosen point. -/
theorem homotopic_const {N : Type u} {x : E} (p : GenLoop N E x) :
    GenLoop.Homotopic p (GenLoop.const : GenLoop N E x) := by
  change p.1.HomotopicRel (GenLoop.const : GenLoop N E x).1 (Cube.boundary N)
  refine ⟨ContinuousMap.HomotopyRel.affine p.1
    (GenLoop.const : GenLoop N E x).1 ?_⟩
  intro a ha
  exact GenLoop.boundary p a ha

end GenLoop

namespace HomotopyGroup

/-- The boundary-relative homotopy quotient of a real topological vector space
is a subsingleton for every cube-index type and every chosen point. -/
theorem subsingleton (N : Type u) (x : E) :
    Subsingleton (HomotopyGroup N E x) := by
  refine ⟨fun a b ↦ ?_⟩
  refine Quotient.inductionOn₂
    (motive := fun a b : HomotopyGroup N E x ↦ a = b) a b ?_
  intro p q
  exact Quotient.sound
    (GenLoop.Homotopic.trans (GenLoop.homotopic_const p)
      (GenLoop.Homotopic.symm (GenLoop.homotopic_const q)))

end HomotopyGroup
