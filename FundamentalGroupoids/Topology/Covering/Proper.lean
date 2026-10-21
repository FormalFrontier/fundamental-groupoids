/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocalAtTarget
public import FundamentalGroupoids.Topology.Covering.Cardinality

/-!
# Proper covering maps

A covering map is proper if and only if all its point fibers are finite. The fibers are the
canonical subtypes with their inherited topologies. The total and base spaces have independent
universes and arbitrary given topologies; no separation, local compactness, connectedness,
surjectivity, nonemptiness or uniform sheet cardinality is assumed.

On a preconnected base, properness is equivalent to finiteness of the fiber over any given
point, by `IsCoveringMap.isProperMap_iff_finite_fiber`. This uses local constancy of the
finiteness predicate; the finite-fiber locus is clopen even on a disconnected base. Empty
fibers are finite and infinite fibers are not. The point criterion requires preconnectedness
of the whole base: finiteness on just one component need not imply properness. On an empty
base properness still holds, but there is no point at which to apply the point criterion.

For compact inverse images, apply `IsProperMap.isCompact_preimage` to the properness supplied by
either criterion.

The all-fibers criterion uses Mathlib's raw evenly covered charts, including charts with empty
fibers. Finite fibers make the restricted maps proper product projections, and closedness glues
over the open cover of the target. This follows the local closed-map/compact-fiber proof pattern of
VectorBundles' `FiberBundle.isProperMap_proj_iff`. That result concerns fixed-model bundle
projections; no global model fiber or total-space representation is chosen here.

## References

* [Mathlib's covering maps](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Covering/Basic.lean).
* [Mathlib's proper maps](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Maps/Proper/Basic.lean)
  and [local closedness](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/LocalAtTarget.lean).
* [Mathlib's compactness theory](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Compactness/Compact.lean).
* [VectorBundles' proper bundle projections](https://github.com/FormalFrontier/vector-bundles/blob/9d2d4b48577e873679271aeee0899239d9a835a1/VectorBundles/Topology/FiberBundle/Proper.lean#L58-L105),
  for the local closed-map/compact-fiber formalization pattern.
-/

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y}

namespace IsCoveringMap

/-- A covering map is proper exactly when each canonical point fiber is finite, without
separation or inhabitation assumptions. The proof uses Mathlib's evenly covered charts and
proper-map APIs, following the local closed-map/compact-fiber argument of VectorBundles'
`FiberBundle.isProperMap_proj_iff` (see the module references). -/
theorem isProperMap_iff_finite_fibers (hp : IsCoveringMap p) :
    IsProperMap p ↔ ∀ y : Y, Finite (p ⁻¹' {y}) := by
  classical
  constructor
  · intro hproper y
    let : CompactSpace (p ⁻¹' {y}) :=
      isCompact_iff_compactSpace.mp (hproper.isCompact_preimage isCompact_singleton)
    let : DiscreteTopology (p ⁻¹' {y}) := (hp y).discreteTopology_fiber
    exact finite_of_compact_of_discrete
  · intro hfinite
    have hcompact (y : Y) : CompactSpace (p ⁻¹' {y}) := by
      let : Finite (p ⁻¹' {y}) := hfinite y
      infer_instance
    refine isProperMap_iff_isClosedMap_and_compact_fibers.2
      ⟨hp.continuous, ?_, fun y ↦ isCompact_iff_compactSpace.mpr (hcompact y)⟩
    -- The raw charts work for empty fibers as well as nonempty ones.
    choose U hyU hU _ H hH using fun y ↦ (hp y).2
    have hcover := TopologicalSpace.IsOpenCover.of_sets hU (by
      ext y
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      exact ⟨y, hyU y⟩)
    apply hcover.isClosedMap_iff_restrictPreimage.2
    intro y
    let : CompactSpace (p ⁻¹' {y}) := hcompact y
    -- This is an equality into the given open subtype, not just into the base space.
    have hproj : (U y).restrictPreimage p = Prod.fst ∘ H y := by
      funext x
      apply Subtype.ext
      simp only [Set.restrictPreimage_coe, Function.comp_apply]
      exact (hH y x).symm
    rw [hproj]
    exact ((isProperMap_fst_of_compactSpace (X := U y) (Y := p ⁻¹' {y})).comp
      (H y).isProperMap).isClosedMap

/-- On a preconnected base, a covering map is proper exactly when its canonical fiber over
the given point is finite. No additional nonemptiness assumption is needed; empty fibers
are finite, while infinite fibers are excluded. An empty base has no point to supply. -/
theorem isProperMap_iff_finite_fiber (hp : IsCoveringMap p)
    [PreconnectedSpace Y] (y0 : Y) :
    IsProperMap p ↔ Finite (p ⁻¹' {y0}) := by
  rw [hp.isProperMap_iff_finite_fibers]
  constructor
  · exact fun h ↦ h y0
  · intro h y
    exact (hp.isLocallyConstant_finite_fiber.apply_eq_of_preconnectedSpace y0 y) ▸ h

end IsCoveringMap
