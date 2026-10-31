/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Geometry of cube boundaries

The coordinate-face boundary `Cube.boundary N` is path connected when the index
type `N` has at least two elements. The index type may be infinite. This is the
set of cube points with a coordinate equal to `0` or `1`, rather than a claim
about a topological frontier. For a nonempty index type, the zero vertex lies
on the boundary. For an infinite index type, the boundary is dense in the cube.

## References

* Mathlib's `Mathlib.Topology.Homotopy.HomotopyGroup` supplies the cube boundary.
* Mathlib's `Mathlib.Topology.Connected.PathConnected` supplies set and subtype
  path connectedness and their equivalence.
-/

@[expose] public section

universe u

open scoped unitInterval Topology

namespace Cube

/-- The zero vertex lies on the boundary of a cube with a nonempty index type. -/
@[simp]
theorem zero_mem_boundary (N : Type u) [Nonempty N] : (0 : I^N) ∈ boundary N := by
  obtain ⟨i⟩ := ‹Nonempty N›
  exact ⟨i, Or.inl rfl⟩

/-- The coordinate-face boundary of a cube indexed by an infinite type is dense. -/
theorem dense_boundary (N : Type u) [Infinite N] : Dense (boundary N) := by
  classical
  refine dense_iff_inter_open.2 ?_
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨J, hJ⟩ :=
    exists_finset_piecewise_mem_of_mem_nhds (hU.mem_nhds hx) (0 : I^N)
  obtain ⟨i, hi⟩ := J.exists_notMem
  refine ⟨J.piecewise x 0, hJ, i, Or.inl ?_⟩
  exact J.piecewise_eq_of_notMem x 0 hi

private theorem joinedIn_boundary_of_eq_coord {N : Type u} {x y : I^N} (i : N)
    (hxy : x i = y i) (hx : x i = 0 ∨ x i = 1) : JoinedIn (boundary N) x y := by
  let p : Path x y := .pi fun j =>
    { toFun := Set.Icc.convexComb (x j) (y j)
      continuous_toFun := Set.Icc.continuous_convexComb _ _
      source' := Set.Icc.convexComb_zero _ _
      target' := Set.Icc.convexComb_one _ _ }
  refine ⟨p, fun t => ⟨i, ?_⟩⟩
  change Set.Icc.convexComb (x i) (y i) t = 0 ∨
    Set.Icc.convexComb (x i) (y i) t = 1
  simpa only [← hxy, Set.Icc.convexComb_eq] using hx

/-- The coordinate-face boundary of a cube with at least two coordinates is path connected. -/
theorem isPathConnected_boundary (N : Type u) [Nontrivial N] :
    IsPathConnected (boundary N) := by
  classical
  refine ⟨0, zero_mem_boundary N, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hji⟩ := exists_ne i
  -- Keep the boundary coordinate fixed while moving all other coordinates to zero.
  let z : I^N := Function.update 0 i (x i)
  have hxz : JoinedIn (boundary N) x z :=
    joinedIn_boundary_of_eq_coord i (by simp [z]) hi
  -- The distinct coordinate stays zero while the remaining coordinate moves to zero.
  have hz0 : JoinedIn (boundary N) z 0 :=
    joinedIn_boundary_of_eq_coord j (by simp [z, hji]) (Or.inl (by simp [z, hji]))
  exact (hxz.trans hz0).symm

/-- The boundary subtype of a cube with at least two coordinates is path connected. -/
instance instPathConnectedSpaceBoundary (N : Type u) [Nontrivial N] :
    PathConnectedSpace (boundary N) :=
  isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_boundary N)

end Cube
