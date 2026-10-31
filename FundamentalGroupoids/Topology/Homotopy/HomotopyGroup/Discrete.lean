/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homotopy.HomotopyGroup
import FundamentalGroupoids.Topology.Homotopy.Cube
import Mathlib.Analysis.Convex.PathConnected

/-!
# Generalized loops with a subsingleton path component

At a chosen point whose path component is a subsingleton, every generalized loop
indexed by a nonempty type equals the constant loop. Its boundary-relative homotopy
quotient is therefore a subsingleton. In particular, this applies to totally
disconnected spaces, hence to discrete spaces through Mathlib's instances.

These cubical statements generalize May's discrete-target calculation in finite
positive degrees to a condition at the chosen point and to arbitrary nonempty
cube-index types. Mathlib supplies the generalized-loop carrier, homotopy quotient
and topology used here.

## Implementation notes

The cube index and target have independent universes. The boundary is the union of
coordinate faces, also for infinite indices, not a topological frontier. No
sphere-domain or compactly generated-space comparison is asserted. Nonemptiness
of the index is sharp uniformly over targets: for an empty index, the quotient
contains all path components of the target, not only the chosen point's component.
For example, discrete `Bool` has only constant representatives at either basepoint
for nonempty indices, but its empty-index quotient has two classes. For a fixed
target with only one path component, the empty-index quotient is also a subsingleton.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 9, §4,
  p. 66, for the discrete-target calculation in finite positive degrees.
* Mathlib's `Mathlib.Topology.Homotopy.HomotopyGroup` supplies generalized loops
  and their boundary-relative homotopy quotient, due to Roberto Alvarez.
* Mathlib's `Mathlib.Topology.Connected.PathConnected` and
  `Mathlib.Topology.Connected.TotallyDisconnected` supply the path-component and
  totally disconnected topology interfaces.
-/

@[expose] public section

universe u v

variable {X : Type v} [TopologicalSpace X]

namespace GenLoop

/-- Every generalized loop based at a point with a subsingleton path component equals
the constant loop. This generalizes the cubical analogue of May's discrete-target
calculation in finite positive degrees (Chapter 9, §4, p. 66) to a point-local
hypothesis and arbitrary nonempty cube indices. -/
theorem eq_const_of_subsingleton_pathComponent {N : Type u} [Nonempty N] {x : X}
    (p : GenLoop N X x) (h : (pathComponent x).Subsingleton) :
    p = (GenLoop.const : GenLoop N X x) := by
  let : PathConnectedSpace unitInterval :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, unitInterval.zero_mem⟩)
  have hp0 : p (0 : N → unitInterval) = x :=
    GenLoop.boundary p 0 (Cube.zero_mem_boundary N)
  apply GenLoop.ext
  intro t
  have ht : p t ∈ pathComponent x := by
    apply mem_pathComponent_iff.mpr
    simpa only [hp0] using
      (PathConnectedSpace.joined (0 : N → unitInterval) t).map (map_continuous p)
  simpa only [GenLoop.const_apply] using h ht (mem_pathComponent_self x)

end GenLoop

namespace HomotopyGroup

/-- The generalized-loop homotopy quotient at a point with a subsingleton path
component is a subsingleton. This cubical analogue of May's discrete positive-degree
calculation (Chapter 9, §4, p. 66) uses only the chosen path component and permits
every nonempty cube index. -/
theorem subsingleton_of_subsingleton_pathComponent (N : Type u) [Nonempty N] (x : X)
    (h : (pathComponent x).Subsingleton) :
    Subsingleton (HomotopyGroup N X x) := by
  refine ⟨fun a b ↦ ?_⟩
  refine Quotient.inductionOn₂
    (motive := fun a b : HomotopyGroup N X x ↦ a = b) a b ?_
  intro p q
  exact congrArg (fun r : GenLoop N X x ↦ (⟦r⟧ : HomotopyGroup N X x))
    ((GenLoop.eq_const_of_subsingleton_pathComponent p h).trans
      (GenLoop.eq_const_of_subsingleton_pathComponent q h).symm)

/-- A totally disconnected space has a subsingleton generalized-loop homotopy quotient
at every basepoint for any nonempty cube index. This generalizes the cubical analogue
of May's finite positive-degree discrete-target calculation (Chapter 9, §4, p. 66).
Discrete spaces are included through Mathlib's instances. -/
theorem subsingleton_of_totallyDisconnectedSpace [TotallyDisconnectedSpace X]
    (N : Type u) [Nonempty N] (x : X) :
    Subsingleton (HomotopyGroup N X x) := by
  apply subsingleton_of_subsingleton_pathComponent N x
  exact (isPreconnected_connectedComponent (x := x)).subsingleton.anti
    (pathComponent_subset_component x)

end HomotopyGroup
