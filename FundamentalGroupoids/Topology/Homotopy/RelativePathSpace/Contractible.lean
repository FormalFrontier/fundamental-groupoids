/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.PathSpace
public import FundamentalGroupoids.Topology.Homotopy.RelativePathSpace
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractibility of fixed-start paths

The compact-open space `ContinuousMap.RelativePathSpace b Set.univ` contracts to
its constant path by shortening the time interval: at homotopy time `s`, a path
`γ` is sent to `t ↦ γ ((1 - s) * t)`. The constant path is fixed throughout.

## Implementation notes

These are ordinary compact-open and subspace topologies. No separation or local
compactness hypothesis on the target is needed. Only the starting point is fixed:
the endpoint at time `s` is `γ (1 - s)`, so this construction is not a contraction
of fixed-endpoint path spaces or loop spaces. The topology is not replaced by a
kification; no equality with function-space topologies in May's category U is asserted.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 7, §3, p. 50:
  the time-shortening deformation of the mapping-path space, specialized here to
  fixed-start paths with ordinary compact-open topology.
* Mathlib contributors, `Mathlib.Topology.CompactOpen`: compact-open evaluation
  and continuity of currying.
* Mathlib contributors, `Mathlib.Topology.Homotopy.Contractible`: contractibility
  characterized by nullhomotopy of the identity.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap.RelativePathSpace

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Shorten a fixed-start path to its constant path, fixing that constant path
throughout the homotopy. This uses May's time-shortening deformation (*A Concise
Course in Algebraic Topology*, Chapter 7, §3, p. 50) with ordinary compact-open
topology. The terminal point of the path is free to move. -/
noncomputable def contraction (b : X) :
    (ContinuousMap.id (RelativePathSpace b Set.univ)).HomotopyRel
      (ContinuousMap.const _ (const (Set.mem_univ b))) {const (Set.mem_univ b)} where
  toFun p := mk
    (ContinuousMap.initialSegment (unitInterval.symm p.1, path p.2))
    (by simpa only [ContinuousMap.initialSegment_apply_zero] using path_zero p.2)
    (Set.mem_univ _)
  continuous_toFun := by
    apply continuous_iff.mpr
    simp only [path_mk]
    exact (ContinuousMap.continuous_initialSegment (B := X)).comp
      ((unitInterval.continuous_symm.comp continuous_fst).prodMk
        (path.continuous.comp continuous_snd))
  map_zero_left := by
    intro γ
    apply ext
    apply ContinuousMap.ext
    intro t
    simp only [path_mk, ContinuousMap.initialSegment_apply, unitInterval.symm_zero, one_mul,
      ContinuousMap.id_apply]
  map_one_left := by
    intro γ
    apply ext
    apply ContinuousMap.ext
    intro t
    simp only [path_mk, ContinuousMap.initialSegment_apply, unitInterval.symm_one, zero_mul,
      path_zero, ContinuousMap.const_apply, path_const]
  prop' := by
    intro s γ hγ
    rcases Set.mem_singleton_iff.mp hγ with rfl
    apply ext
    apply ContinuousMap.ext
    intro t
    rfl

/-- Evaluate the shortened path at any path time. -/
theorem eval_contraction (b : X) (s : I) (γ : RelativePathSpace b Set.univ) (t : I) :
    eval t (contraction b (s, γ)) = eval (unitInterval.symm s * t) γ := by
  rfl

/-- The constant path is fixed at every homotopy time. -/
@[simp]
theorem contraction_const (b : X) (s : I) :
    contraction b (s, const (Set.mem_univ b)) = const (Set.mem_univ b) := by
  exact (contraction b).eq_fst s (Set.mem_singleton _)

/-- The endpoint of the shortened path moves backwards along the original path. -/
theorem endpoint_contraction_coe (b : X) (s : I) (γ : RelativePathSpace b Set.univ) :
    (endpoint (contraction b (s, γ)) : X) = eval (unitInterval.symm s) γ := by
  simpa only [endpoint_coe, eval_apply, mul_one] using eval_contraction b s γ 1

/-- Compact-open paths with a fixed starting point and a free endpoint form a
contractible space, via `contraction` and May's time-shortening deformation
(*A Concise Course in Algebraic Topology*, Chapter 7, §3, p. 50). -/
instance instContractibleSpaceUniv (b : X) :
    ContractibleSpace (RelativePathSpace b Set.univ) := by
  exact (contractible_iff_id_nullhomotopic (RelativePathSpace b Set.univ)).2
    ⟨const (Set.mem_univ b), ⟨(contraction b).toHomotopy⟩⟩

end ContinuousMap.RelativePathSpace
