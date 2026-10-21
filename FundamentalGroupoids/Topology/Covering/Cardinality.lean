/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Cardinalities and finiteness of covering fibers

The cardinality of the point fibers of a covering map is locally constant, as is the predicate
that a point fiber is finite. In particular, the finite-fiber locus is clopen. Empty fibers
belong to this locus, while infinite fibers do not.

The total and base spaces have independent universes and arbitrary given topologies. Empty
and infinite fibers retain their cardinalities; no finiteness, connectedness, local path
connectedness, surjectivity or nonemptiness assumption is imposed.

The existing `IsLocallyConstant.apply_eq_of_isPreconnected` and
`IsLocallyConstant.apply_eq_of_preconnectedSpace` give the corresponding constancy statements
on preconnected subsets and preconnected bases, for both cardinality and finiteness.

## References

* Mathlib's `IsEvenlyCovered.fiberHomeomorph` in `Mathlib.Topology.Covering.Basic`, for
  comparing model fibers with point fibers, including empty fibers.
* Mathlib's `Cardinal.mk_congr`, `Cardinal.mk_lt_aleph0_iff` and `IsLocallyConstant` APIs.
-/

@[expose] public section

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

namespace IsCoveringMap

/-- The cardinality of the point fiber of a covering map is locally constant. -/
theorem isLocallyConstant_cardinalMk_fiber (cov : IsCoveringMap p) :
    IsLocallyConstant (fun b : B ↦ Cardinal.mk (p ⁻¹' {b})) := by
  refine (IsLocallyConstant.iff_exists_open _).2 ?_
  intro b
  rcases cov b with ⟨hdisc, U, hbU, hU, hpU, H, hH⟩
  refine ⟨U, hU, hbU, ?_⟩
  intro b' hb'U
  have h : IsEvenlyCovered p b' (p ⁻¹' {b}) :=
    ⟨hdisc, U, hb'U, hU, hpU, H, hH⟩
  exact (Cardinal.mk_congr h.fiberHomeomorph.toEquiv).symm

/-- Finiteness of the canonical point fiber of a covering map is locally constant.
Empty fibers are finite, and infinite fibers do not satisfy this predicate. -/
theorem isLocallyConstant_finite_fiber (cov : IsCoveringMap p) :
    IsLocallyConstant (fun b : B ↦ Finite (p ⁻¹' {b})) := by
  have hfinite :
      (fun b : B ↦ Cardinal.mk (p ⁻¹' {b}) < Cardinal.aleph0) =
        (fun b : B ↦ Finite (p ⁻¹' {b})) := by
    funext b
    exact propext Cardinal.mk_lt_aleph0_iff
  rw [← hfinite]
  exact cov.isLocallyConstant_cardinalMk_fiber.comp
    (fun c : Cardinal.{u} ↦ c < Cardinal.aleph0)

/-- The locus of finite point fibers of a covering map is clopen, including points with empty
fibers and excluding points with infinite fibers. No connectedness assumption is needed. -/
theorem isClopen_setOf_finite_fiber (cov : IsCoveringMap p) :
    IsClopen {b : B | Finite (p ⁻¹' {b})} := by
  simpa only [eq_iff_iff, iff_true] using
    cov.isLocallyConstant_finite_fiber.isClopen_fiber True

end IsCoveringMap
