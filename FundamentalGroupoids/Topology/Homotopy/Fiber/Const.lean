/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber
public import Mathlib.Topology.Path

/-!
# Homotopy fibers of constant maps

The homotopy fiber of the constant map with value `c` over `b` retains an arbitrary
source point together with a path from `b` to `c`. Its comparison with the product
uses Mathlib's existing `Path b c`, with the topology induced from compact-open
continuous maps. In particular, the source point is not recovered from the path.

The comparison is natural in arbitrary continuous maps of source spaces. It also
characterizes nonemptiness: both a source point and a path from `b` to `c` are
needed. When `b = c`, the entire loop-space factor is retained.

## Implementation notes

Continuity uses the existing coordinate criterion for homotopy fibers and the
topology on `Path b c` induced from `C(I, X)`. Only ordinary product, subspace and
compact-open topologies are used; no separation or local compactness of either
space is required. The source may be empty.

## References

* Mathlib, `Mathlib.Topology.Path`, for Patrick Massot's fixed-endpoint paths and
  their induced topology, and its product and induced-topology continuity APIs.
* Mathlib's compact-open continuous-map API, due to Reid Barton.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

universe uE uX uF

variable {E : Type uE} {X : Type uX}
variable [TopologicalSpace E] [TopologicalSpace X]
variable {b c : X}

/-- The homotopy fiber of the constant map with value `c` over `b` is the product
of its source with the fixed-endpoint path space from `b` to `c`. -/
noncomputable def constHomeomorph (E : Type uE) [TopologicalSpace E] (b c : X) :
    HomotopyFiber (ContinuousMap.const E c) b ≃ₜ E × Path b c where
  toFun z :=
    (point z,
      { toContinuousMap := path z
        source' := path_zero z
        target' := path_one z })
  invFun z := mk z.1 z.2.toContinuousMap z.2.source z.2.target
  left_inv := by
    intro z
    exact mk_point_path z
  right_inv := by
    intro z
    exact Prod.ext rfl (Path.ext rfl)
  continuous_toFun := by
    refine point.continuous.prodMk ?_
    exact continuous_induced_rng.2 path.continuous
  continuous_invFun := by
    apply continuous_iff.2
    exact ⟨continuous_fst,
      (continuous_induced_dom :
        Continuous (fun γ : Path b c => γ.toContinuousMap)).comp continuous_snd⟩

/-- The forward comparison retains the source point. -/
@[simp]
theorem constHomeomorph_fst (z : HomotopyFiber (ContinuousMap.const E c) b) :
    (constHomeomorph E b c z).1 = point z :=
  rfl

/-- The forward comparison retains the path at every time, with its original direction. -/
@[simp]
theorem constHomeomorph_snd_apply (z : HomotopyFiber (ContinuousMap.const E c) b)
    (t : I) : (constHomeomorph E b c z).2 t = path z t :=
  rfl

/-- The inverse comparison retains the specified source point. -/
@[simp]
theorem constHomeomorph_symm_point (z : E × Path b c) :
    point ((constHomeomorph E b c).symm z) = z.1 :=
  rfl

/-- The inverse comparison retains the specified path at every time. -/
@[simp]
theorem constHomeomorph_symm_path_apply (z : E × Path b c) (t : I) :
    path ((constHomeomorph E b c).symm z) t = z.2 t :=
  rfl

/-- A continuous map of source spaces acts only on the source factor of the
constant-map comparison, through the existing map of homotopy fibers. -/
theorem constHomeomorph_naturality {F : Type uF} [TopologicalSpace F]
    (u : C(E, F)) (b c : X) (z : HomotopyFiber (ContinuousMap.const E c) b) :
    constHomeomorph F b c
        (map (f := ContinuousMap.const E c) (f' := ContinuousMap.const F c)
          u (ContinuousMap.id X) (fun _ => rfl) (b := b) (b' := b) rfl z) =
      Prod.map u id (constHomeomorph E b c z) := by
  apply Prod.ext
  · exact point_map (f := ContinuousMap.const E c) (f' := ContinuousMap.const F c)
      (b := b) (b' := b) u (ContinuousMap.id X) (fun _ => rfl) rfl z
  · apply Path.ext
    funext t
    exact DFunLike.congr_fun
      ((path_map (f := ContinuousMap.const E c) (f' := ContinuousMap.const F c)
        (b := b) (b' := b) u (ContinuousMap.id X) (fun _ => rfl) rfl z).trans
        (ContinuousMap.id_comp (path z))) t

/-- A constant-map homotopy fiber is inhabited exactly when its source and its
fixed-endpoint path space are inhabited. Neither condition is assumed. -/
theorem nonempty_const_iff (E : Type uE) [TopologicalSpace E] (b c : X) :
    Nonempty (HomotopyFiber (ContinuousMap.const E c) b) ↔
      Nonempty E ∧ Nonempty (Path b c) := by
  constructor
  · rintro ⟨z⟩
    exact ⟨⟨(constHomeomorph E b c z).1⟩, ⟨(constHomeomorph E b c z).2⟩⟩
  · rintro ⟨⟨e⟩, ⟨γ⟩⟩
    exact ⟨(constHomeomorph E b c).symm (e, γ)⟩

end ContinuousMap.HomotopyFiber
