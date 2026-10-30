/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Covering.Composition
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.FiberBundle.Constructions

/-!
# Cancellation with an empty target-sheet fiber

The map `ℝ × Fin 3 → ℝ × Fin 2` sending `(x, i)` to `(x, 0)` lies over the real line.
Both projections are Mathlib's trivial discrete-fiber bundle covers, transported along
`Bundle.Trivial.homeomorphProd`. Cancellation makes this map a covering of its locally
connected, disconnected target, although its fiber over `(0, 1)` is empty and it is not
surjective.
-/

private def collapseSheets : C(ℝ × Fin 3, ℝ × Fin 2) :=
  ⟨fun z ↦ (z.1, 0), continuous_fst.prodMk continuous_const⟩

/-- A map between nonempty trivial covers can itself be a covering while omitting a sheet. -/
private theorem collapseSheets_boundary :
    IsCoveringMap collapseSheets ∧ collapseSheets ⁻¹' {(0, 1)} = ∅ ∧
      ¬ Function.Surjective collapseSheets := by
  have hprojection (n : ℕ) : IsCoveringMap (Prod.fst : ℝ × Fin n → ℝ) := by
    have h : IsCoveringMap
        (Bundle.TotalSpace.proj : Bundle.TotalSpace (Fin n) (Bundle.Trivial ℝ (Fin n)) → ℝ) :=
      FiberBundle.isCoveringMap (F := Fin n) (E := Bundle.Trivial ℝ (Fin n))
    exact h.comp_homeomorph (Bundle.Trivial.homeomorphProd ℝ (Fin n)).symm
  have hempty : collapseSheets ⁻¹' {(0, 1)} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
    have hzero : (0 : ℕ) = 1 := congrArg (fun y : ℝ × Fin 2 ↦ y.2.val) hz
    exact Nat.zero_ne_one hzero
  refine ⟨IsCoveringMap.of_comp_eq (hprojection 3) (hprojection 2) collapseSheets rfl,
    hempty, ?_⟩
  intro hsurj
  obtain ⟨z, hz⟩ := hsurj (0, 1)
  have hzmem : z ∈ collapseSheets ⁻¹' {(0, 1)} := hz
  rw [hempty] at hzmem
  exact hzmem
