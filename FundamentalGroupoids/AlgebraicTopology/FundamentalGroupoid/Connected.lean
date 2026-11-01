/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.CategoryTheory.Groupoid.ConnectedComponents
public import FundamentalGroupoids.CategoryTheory.SingleObj
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Connectedness of the fundamental groupoid

Two points lie in the same categorical connected component of the fundamental
groupoid exactly when they are joined by a path. A topological space is path
connected if and only if its fundamental groupoid is categorically connected.
Both notions in the latter equivalence include nonemptiness.
Together with the canonical vertex-functor instances, this gives the equivalence
between a chosen vertex group and the fundamental groupoid of a path-connected
space by applying `Functor.asEquivalence` to
`SingleObj.functor (MonoidHom.id (End (FundamentalGroupoid.mk x)))`.

## Implementation notes

Only the implication from path connectedness to categorical connectedness is
registered as an instance. The reverse implication is available through
`FundamentalGroupoid.pathConnectedSpace_iff_isConnected`. The component criterion
`FundamentalGroupoid.connectedComponents_mk_eq_iff_joined` needs no connectedness,
local path connectedness or separation hypothesis.

## References

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §5.
-/

@[expose] public section

universe u

namespace FundamentalGroupoid

variable (X : Type u) [TopologicalSpace X]

/-- Two points have the same categorical component in the fundamental groupoid
exactly when they can be joined by a path. -/
theorem connectedComponents_mk_eq_iff_joined (x y : X) :
    CategoryTheory.ConnectedComponents.mk (FundamentalGroupoid.mk x) =
      CategoryTheory.ConnectedComponents.mk (FundamentalGroupoid.mk y) ↔ Joined x y := by
  rw [CategoryTheory.ConnectedComponents.mk_eq_mk_iff_nonempty_hom]
  exact nonempty_quotient_iff (Path.Homotopic.setoid x y)

/-- A space is path connected exactly when its fundamental groupoid is connected,
with nonemptiness on both sides. This identifies the two connectedness hypotheses
in the vertex-group equivalence of May, Chapter 2, §5. -/
theorem pathConnectedSpace_iff_isConnected :
    PathConnectedSpace X ↔ CategoryTheory.IsConnected (FundamentalGroupoid X) := by
  constructor
  · intro h
    let : Nonempty X := h.nonempty
    apply CategoryTheory.zigzag_isConnected
    intro x y
    obtain ⟨p⟩ := h.joined x.as y.as
    exact CategoryTheory.Zigzag.of_hom (Path.Homotopic.Quotient.mk p)
  · intro h
    let : CategoryTheory.IsConnected (FundamentalGroupoid X) := h
    refine ⟨(nonempty_iff X).mp inferInstance, ?_⟩
    intro x y
    exact (nonempty_quotient_iff (Path.Homotopic.setoid x y)).mp
      (inferInstance : Nonempty (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y))

/-- A path-connected space has a connected fundamental groupoid. -/
instance isConnected [PathConnectedSpace X] :
    CategoryTheory.IsConnected (FundamentalGroupoid X) :=
  (pathConnectedSpace_iff_isConnected X).mp inferInstance

end FundamentalGroupoid
