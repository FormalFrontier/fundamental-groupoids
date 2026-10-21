/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Monodromy
public import FundamentalGroupoids.Topology.Covering.Proper
public import Mathlib.GroupTheory.Index

/-!
# Proper coverings and finite-index fundamental-group images

A covering map with path-connected total space is proper if and only if the image of its
induced based fundamental-group homomorphism has finite index. The basepoint is a supplied
point of the total space. No connectedness assumption on the base or surjectivity assumption
on the covering is needed.

The proof identifies the ordinary based fiber with the left cosets of the image subgroup
using `IsCoveringMap.monodromyQuotientEquiv`, then transfers finiteness. The subgroup is the
range of `FundamentalGroup.map` at the given point, not a conjugate subgroup. Only the total
space needs to be preconnected for the intermediate properness criterion in
`IsCoveringMap.isProperMap_iff_finite_fiber_of_preconnectedSpace`; path-connectedness is used
for the monodromy quotient equivalence. Total and base spaces may lie in independent universes.

## References

* The monodromy quotient equivalence in `FundamentalGroupoids.Topology.Covering.Monodromy`,
  using Mathlib's covering lifts and orbit-stabilizer theory and GroupTheory's equivariance API.
* Mathlib's `Subgroup.finiteIndex_iff_finite_quotient` in `Mathlib.GroupTheory.Index`.
* The all-fibers properness criterion and local constancy of fiber cardinality in
  `FundamentalGroupoids.Topology.Covering.Proper` and
  `FundamentalGroupoids.Topology.Covering.Cardinality`.
-/

@[expose] public section

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

namespace IsCoveringMap

/-- A covering map with path-connected total space is proper exactly when the range of its
canonical based fundamental-group homomorphism has finite index. The base need not be
connected, and the covering need not be surjective. -/
theorem isProperMap_iff_finiteIndex (hp : IsCoveringMap p) [PathConnectedSpace E] (e0 : E) :
    IsProperMap p ↔
      (FundamentalGroup.map ⟨p, hp.continuous⟩ e0).range.FiniteIndex := by
  have hrange :
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ (rfl : p e0 = p e0)).range =
        (FundamentalGroup.map ⟨p, hp.continuous⟩ e0).range := by
    apply congrArg (fun f : FundamentalGroup E e0 →* FundamentalGroup B (p e0) ↦ f.range)
    apply MonoidHom.ext
    intro γ
    simp only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
    rfl
  rw [hp.isProperMap_iff_finite_fiber_of_preconnectedSpace e0,
    Subgroup.finiteIndex_iff_finite_quotient]
  have e := hp.monodromyQuotientEquiv (p e0) ⟨e0, rfl⟩
  rw [hrange] at e
  exact e.finite_iff.symm

end IsCoveringMap
