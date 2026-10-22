/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.SemilocallySimplyConnected.Basic
import Mathlib.Analysis.Convex.Contractible

/-!
# Basic semilocal simple connectivity

The chosen-center neighborhood API, its fundamental-group characterization,
the empty-space boundary, and the real line as a simply connected example.
-/

universe u

variable {X : Type u} [TopologicalSpace X]

-- A concrete open neighborhood of zero, with trivial ambient inclusion image.
example :
    IsOpen (Set.Iio (1 : ℝ)) ∧
      ∃ h0 : (0 : ℝ) ∈ Set.Iio (1 : ℝ),
        (FundamentalGroup.map (ContinuousMap.subtypeVal (Set.Iio (1 : ℝ)))
          ⟨0, h0⟩).range = ⊥ := by
  refine ⟨isOpen_Iio, ⟨(by
    change (0 : ℝ) < 1
    exact zero_lt_one), ?_⟩⟩
  exact (FundamentalGroup.range_map_subtypeVal_eq_bot_iff _).mpr
    (fun γ _ => SimplyConnectedSpace.paths_homotopic γ (Path.refl 0))

example [IsEmpty X] : SemilocallySimplyConnectedSpace X :=
  SemilocallySimplyConnectedSpace.of_forall (fun x => isEmptyElim x)

example : SemilocallySimplyConnectedSpace ℝ := inferInstance

example (x : ℝ) : IsSemilocallySimplyConnectedAt x :=
  IsSemilocallySimplyConnectedAt.of_injective_fundamentalGroup_map (ContinuousMap.id ℝ)
    (by
      rw [FundamentalGroup.map_id]
      intro a b hab
      exact hab)
    (isSemilocallySimplyConnectedAt x)
