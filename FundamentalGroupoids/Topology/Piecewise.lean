/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Piecewise

/-!
# Continuous pasting under specialization

Continuous maps can be pasted along a closed set when the outside value
specializes to the inside value at each point of that set. The specialization
condition need not hold away from the closed set, and no separation assumption
is imposed on either space.

## References

* Mathlib's `IsClosed.continuous_piecewise_of_specializes` gives continuous
  pasting under a global specialization hypothesis.
* Mathlib's `continuous_if'` gives continuous pasting from limits at the frontier.
-/

@[expose] public section

universe u v

open scoped Topology

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
  {s : Set A} {f g : A → B}

/-- Pasting continuous maps along a closed set is continuous if the outside
value specializes to the inside value at each point of the closed set.
This localizes the hypothesis of `IsClosed.continuous_piecewise_of_specializes`,
which assumes specialization at every source point. -/
theorem IsClosed.continuous_piecewise_of_specializes_on [DecidablePred (· ∈ s)]
    (hs : IsClosed s) (hf : Continuous f) (hg : Continuous g)
    (hspec : ∀ a ∈ s, g a ⤳ f a) : Continuous (s.piecewise f g) := by
  apply continuous_if'
  · intro a ha
    have has : a ∈ s := hs.frontier_subset ha
    rw [ite_eq_left has]
    exact hf.continuousAt.continuousWithinAt
  · intro a ha
    have has : a ∈ s := hs.frontier_subset ha
    rw [ite_eq_left has]
    exact ((show Filter.Tendsto g (𝓝 a) (𝓝 (g a)) from hg.continuousAt).mono_right
      (hspec a has).nhds_le_nhds).mono_left nhdsWithin_le_nhds
  · exact hf.continuousOn
  · exact hg.continuousOn
