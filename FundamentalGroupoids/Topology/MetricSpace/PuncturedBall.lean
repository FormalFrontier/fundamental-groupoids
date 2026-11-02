/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Path connectedness of punctured balls

An open ball in a real normed vector space of dimension greater than one remains
path connected after removing its center.

The proof uses Mathlib's `OpenPartialHomeomorph.univBall` to identify the punctured
ball with the continuous image of the complement of the origin. The latter is
path connected by `isPathConnected_compl_singleton_of_one_lt_rank`.
-/

@[expose] public section

universe u

/-- An open ball punctured at its center is path connected when the real dimension
exceeds one. -/
theorem isPathConnected_ball_diff_singleton_of_one_lt_rank
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : 1 < Module.rank ℝ E) (c : E) {r : ℝ} (hr : 0 < r) :
    IsPathConnected (Metric.ball c r \ {c}) := by
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.univBall c r
  have hs : e.source = Set.univ := OpenPartialHomeomorph.univBall_source c r
  have ht : e.target = Metric.ball c r := OpenPartialHomeomorph.univBall_target c hr
  have h0 : e (0 : E) = c := OpenPartialHomeomorph.univBall_apply_zero c r
  have hsource (z : E) : z ∈ e.source := by
    rw [hs]
    exact Set.mem_univ z
  have he : Continuous e :=
    continuousOn_univ.mp (by simpa only [hs] using e.continuousOn)
  have himage : e '' ({(0 : E)}ᶜ : Set E) = Metric.ball c r \ {c} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← ht]
        exact e.map_source (hsource z)
      · intro hy
        have hz0 : z = 0 := e.injOn (hsource z) (hsource 0)
          ((Set.mem_singleton_iff.mp hy).trans h0.symm)
        exact hz (Set.mem_singleton_iff.mpr hz0)
    · rintro ⟨hy, hy0⟩
      have hy' : y ∈ e.target := by simpa only [ht] using hy
      refine ⟨e.symm y, ?_, e.right_inv hy'⟩
      intro hz
      apply hy0
      apply Set.mem_singleton_iff.mpr
      calc
        y = e (e.symm y) := (e.right_inv hy').symm
        _ = e 0 := congrArg e (Set.mem_singleton_iff.mp hz)
        _ = c := h0
  rw [← himage]
  exact (isPathConnected_compl_singleton_of_one_lt_rank h (0 : E)).image he
