/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# A nonconstant generalized loop under a two-sheet covering

The polynomial `t₀ * (1 - t₀) * t₁ * (1 - t₁)` vanishes on the square boundary
and equals `1 / 16` at the center. It defines a nonconstant `GenLoop (Fin 2) ℝ 0`.
Its explicit lift through `ℝ × Bool → ℝ` stays in the supplied sheet `(0, false)`;
projection is expressed using `GenLoop.map`. The covering proof uses the trivial
bundle and its product homeomorphism. No covering-lift construction or theorem
about connectedness of cube boundaries is used. The total space is disconnected,
so this example does not need global path connectedness of the covering space.
-/

open scoped unitInterval Topology

noncomputable section

private def bump : C((Fin 2 → I), ℝ) :=
  ⟨fun t ↦ (t 0 : ℝ) * (1 - (t 0 : ℝ)) * (t 1 : ℝ) * (1 - (t 1 : ℝ)),
    by fun_prop⟩

private def bumpLoop : GenLoop (Fin 2) ℝ 0 :=
  ⟨bump, by
    rintro t ⟨i, hi⟩
    fin_cases i
    · change t 0 = 0 ∨ t 0 = 1 at hi
      rcases hi with hi | hi <;> simp [bump, hi]
    · change t 1 = 0 ∨ t 1 = 1 at hi
      rcases hi with hi | hi <;> simp [bump, hi]⟩

private def squareCenter : Fin 2 → I :=
  fun _ ↦ ⟨1 / 2, by norm_num⟩

private theorem bumpLoop_center : bumpLoop squareCenter = (1 / 16 : ℝ) := by
  norm_num [bumpLoop, bump, squareCenter]

private def projection : C(ℝ × Bool, ℝ) := ContinuousMap.fst

private theorem projection_cover : IsCoveringMap projection := by
  have h : IsCoveringMap
      (Bundle.TotalSpace.proj : Bundle.TotalSpace Bool (Bundle.Trivial ℝ Bool) → ℝ) :=
    FiberBundle.isCoveringMap (F := Bool) (E := Bundle.Trivial ℝ Bool)
  exact h.comp_homeomorph (Bundle.Trivial.homeomorphProd ℝ Bool).symm

private def bumpLift : GenLoop (Fin 2) (ℝ × Bool) (0, false) :=
  ⟨bumpLoop.1.prodMk (ContinuousMap.const _ false),
    fun t ht ↦ Prod.ext (GenLoop.boundary bumpLoop t ht) rfl⟩

/-- The square bump is nonconstant and has a displayed based lift through a two-sheet cover. -/
private theorem bumpLift_example :
    IsCoveringMap projection ∧
      bumpLoop squareCenter = (1 / 16 : ℝ) ∧
      bumpLoop ≠ (GenLoop.const : GenLoop (Fin 2) ℝ 0) ∧
      GenLoop.map projection rfl bumpLift = bumpLoop := by
  refine ⟨projection_cover, bumpLoop_center, ?_, ?_⟩
  · intro h
    have hcenter := congrArg (fun p : GenLoop (Fin 2) ℝ 0 ↦ p squareCenter) h
    rw [bumpLoop_center, GenLoop.const_apply] at hcenter
    norm_num at hcenter
  · apply GenLoop.ext
    intro t
    rfl
