/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber
public import FundamentalGroupoids.Topology.Connected.PathConnected

/-!
# Homotopy fibers and path components

An ordinary homotopy fiber is nonempty precisely when the basepoint can be joined
to the image of a retained source point. Thus the induced map on path components
is surjective if and only if every homotopy fiber is nonempty. This does not require
the continuous map itself to be surjective. The image on path components of the
retained-point projection is the preimage of the basepoint's component under the
original map. This describes an image, not injectivity of the component projection.

The fiber has the existing ordinary product/subspace topology. Path components are
Mathlib's quotient by `Joined`, not connected components.

## References

These characteristic statements use the existing ordinary homotopy-fiber model,
its point and path API, and Mathlib's paths, `Joined` and quotient path components.
The component map and representative laws are supplied by
`FundamentalGroupoids.Topology.Connected.PathConnected`.
-/

@[expose] public section

universe u v

variable {E : Type u} {B : Type v}
variable [TopologicalSpace E] [TopologicalSpace B]

namespace ContinuousMap.HomotopyFiber

/-- A homotopy fiber is nonempty exactly when some source point has image joined to
its basepoint. The source point is retained, even if the map misses the basepoint. -/
theorem nonempty_iff_exists_joined (f : C(E, B)) (b : B) :
    Nonempty (ContinuousMap.HomotopyFiber f b) ↔
      ∃ e : E, Joined b (f e) := by
  constructor
  · rintro ⟨z⟩
    exact ⟨point z, ⟨Path.mk (path z) (path_zero z) (path_one z)⟩⟩
  · rintro ⟨e, ⟨γ⟩⟩
    exact ⟨mk e γ.toContinuousMap γ.source γ.target⟩

end ContinuousMap.HomotopyFiber

namespace ZerothHomotopy

/-- The induced map on path components is surjective exactly when every ordinary
homotopy fiber is nonempty. -/
theorem surjective_map_iff_nonempty_homotopyFiber (f : C(E, B)) :
    Function.Surjective (ZerothHomotopy.map f) ↔
      ∀ b : B, Nonempty (ContinuousMap.HomotopyFiber f b) := by
  constructor
  · intro h b
    exact (ContinuousMap.HomotopyFiber.nonempty_iff_exists_joined f b).2
      ((mem_range_map_iff f b).1 (h (mk b)))
  · intro h q
    obtain ⟨b, rfl⟩ := mk_surjective q
    exact (mem_range_map_iff f b).2
      ((ContinuousMap.HomotopyFiber.nonempty_iff_exists_joined f b).1 (h b))

/-- A source point's component is in the image of the homotopy-fiber point
projection exactly when its image can be joined to the basepoint. -/
theorem mem_range_map_homotopyFiber_point_iff
    (f : C(E, B)) (b : B) (e : E) :
    ZerothHomotopy.mk e ∈
        Set.range
          (ZerothHomotopy.map
            (ContinuousMap.HomotopyFiber.point (f := f) (b := b))) ↔
      Joined b (f e) := by
  rw [mem_range_map_iff]
  constructor
  · rintro ⟨z, hz⟩
    have hb : Joined b (f (ContinuousMap.HomotopyFiber.point z)) :=
      ⟨Path.mk (ContinuousMap.HomotopyFiber.path z)
        (ContinuousMap.HomotopyFiber.path_zero z)
        (ContinuousMap.HomotopyFiber.path_one z)⟩
    exact hb.trans (hz.map f.continuous).symm
  · rintro ⟨γ⟩
    refine ⟨ContinuousMap.HomotopyFiber.mk e γ.toContinuousMap γ.source γ.target, ?_⟩
    simpa only [ContinuousMap.HomotopyFiber.point_mk] using Joined.refl e

/-- The image on path components of the homotopy-fiber point projection consists
exactly of the source components sent to the basepoint's component. -/
theorem range_map_homotopyFiber_point (f : C(E, B)) (b : B) :
    Set.range
        (ZerothHomotopy.map
          (ContinuousMap.HomotopyFiber.point (f := f) (b := b))) =
      (ZerothHomotopy.map f) ⁻¹' {ZerothHomotopy.mk b} := by
  ext q
  obtain ⟨e, rfl⟩ := mk_surjective q
  rw [mem_range_map_homotopyFiber_point_iff, Set.mem_preimage,
    map_mk, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Quotient.eq.mpr h.symm
  · intro h
    exact Joined.symm (Quotient.eq.mp h)

end ZerothHomotopy
