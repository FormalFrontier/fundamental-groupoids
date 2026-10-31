/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.Separation.Connected

/-!
# An infinite cube boundary edge and the small-index boundaries

In the stock cube `ℕ → I`, varying coordinate zero from zero to one while keeping
coordinate one equal to zero gives a path in `Cube.boundary ℕ` between distinct vertices.
The path is constructed directly in the boundary subtype with the product topology.

The boundary of the empty-index cube is empty. The boundary of the singleton-index cube
consists of its two endpoint vertices and is not path connected: a nontrivial preconnected
subset of a T₁ space would be infinite. These statements use only the existing cube definition
and stock topological APIs.
-/

open scoped unitInterval Topology

noncomputable section

private abbrev natBoundaryZero : Cube.boundary ℕ :=
  ⟨fun _ ↦ 0, ⟨1, Or.inl rfl⟩⟩

private abbrev natBoundaryAxis : Cube.boundary ℕ :=
  ⟨fun n ↦ if n = 0 then 1 else 0, ⟨1, Or.inl (by simp)⟩⟩

/-- A coordinate edge lying in the coordinate-face boundary of an infinitely indexed cube. -/
private def natBoundaryEdge : Path natBoundaryZero natBoundaryAxis where
  toFun t := ⟨fun n ↦ if n = 0 then t else 0, ⟨1, Or.inl (by simp)⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun n ↦ by
      by_cases hn : n = 0
      · simpa only [ite_eq_left hn] using (continuous_id' : Continuous (fun t : I ↦ t))
      · simpa only [ite_eq_right hn] using (continuous_const : Continuous (fun _ : I ↦ (0 : I)))
  source' := by
    apply Subtype.ext
    funext n
    simp
  target' := rfl

private theorem natBoundaryEdge_coordinates (t : I) :
    (natBoundaryEdge t).val 0 = t ∧ (natBoundaryEdge t).val 1 = 0 :=
  ⟨rfl, rfl⟩

private theorem natBoundaryEndpoints_ne : natBoundaryZero ≠ natBoundaryAxis := by
  intro h
  exact zero_ne_one (congrArg (fun x : Cube.boundary ℕ ↦ x.val 0) h)

/-- There is a nonconstant path in an infinite-index stock cube boundary. -/
example : ∃ x y : Cube.boundary ℕ, x ≠ y ∧ Nonempty (Path x y) :=
  ⟨natBoundaryZero, natBoundaryAxis, natBoundaryEndpoints_ne, ⟨natBoundaryEdge⟩⟩

private theorem emptyBoundary : Cube.boundary Empty = ∅ := by
  ext x
  simp [Cube.boundary]

private theorem emptyBoundary_not_isPathConnected : ¬ IsPathConnected (Cube.boundary Empty) := by
  rw [emptyBoundary]
  rintro ⟨x, hx, _⟩
  exact hx

private theorem unitBoundary :
    Cube.boundary Unit = {fun _ : Unit ↦ (0 : I), fun _ : Unit ↦ (1 : I)} := by
  ext x
  simp only [Cube.boundary, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi | hi⟩
    · left
      funext j
      rw [Subsingleton.elim j i]
      exact hi
    · right
      funext j
      rw [Subsingleton.elim j i]
      exact hi
  · rintro (rfl | rfl)
    · exact ⟨(), Or.inl rfl⟩
    · exact ⟨(), Or.inr rfl⟩

private theorem unitBoundary_not_isPathConnected : ¬ IsPathConnected (Cube.boundary Unit) := by
  rw [unitBoundary]
  intro h
  have h01 : (fun _ : Unit ↦ (0 : I)) ≠ (fun _ : Unit ↦ (1 : I)) := by
    intro h01
    exact zero_ne_one (congrFun h01 ())
  exact (h.isConnected.isPreconnected.infinite_of_nontrivial (Set.nontrivial_pair h01))
    (Set.Finite.insert _ (Set.finite_singleton _))
