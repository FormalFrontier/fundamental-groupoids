/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber
public import FundamentalGroupoids.Topology.Path
public import Mathlib.Topology.Path

/-!
# Homotopy fibers of constant maps

The homotopy fiber of the constant map with value `c` over `b` retains an arbitrary
source point together with a path from `b` to `c`. Its comparison with the product
uses Mathlib's existing `Path b c`, with the topology induced from compact-open
continuous maps. In particular, the source point is not recovered from the path.

The comparison is natural in arbitrary continuous maps of source and target
spaces, as an equality of bundled continuous maps. Target maps postcompose the
entire path without changing its time parameter. The comparison also characterizes
nonemptiness: both a source point and a path from `b` to `c` are needed. When
`b = c`, the entire loop-space factor is retained.

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

universe uE uX uF uX'

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

/-- The constant-map comparison commutes with simultaneous continuous maps of
source and target spaces, with postcomposition on the fixed-endpoint path factor. -/
theorem constHomeomorph_naturality_map {E' : Type uF} {X' : Type uX'}
    [TopologicalSpace E'] [TopologicalSpace X']
    (F : C(E, E')) (G : C(X, X')) (b b0 : X) :
    (constHomeomorph E' (G b) (G b0) :
        C(HomotopyFiber (ContinuousMap.const E' (G b0)) (G b),
          E' × Path (G b) (G b0))).comp
      (map (f := ContinuousMap.const E b0) (f' := ContinuousMap.const E' (G b0))
        (b := b) (b' := G b) F G (fun _ => rfl) rfl) =
      (F.prodMap (Path.mapContinuousMap G b b0)).comp
        (constHomeomorph E b b0 :
          C(HomotopyFiber (ContinuousMap.const E b0) b, E × Path b b0)) := by
  apply ContinuousMap.ext
  intro z
  apply Prod.ext
  · exact point_map (f := ContinuousMap.const E b0)
      (f' := ContinuousMap.const E' (G b0))
      (b := b) (b' := G b) F G (fun _ => rfl) rfl z
  · apply Path.ext
    funext t
    exact DFunLike.congr_fun
      (path_map (f := ContinuousMap.const E b0)
        (f' := ContinuousMap.const E' (G b0))
        (b := b) (b' := G b) F G (fun _ => rfl) rfl z) t

/-- A continuous map of source spaces acts on the source factor of the
constant-map comparison and leaves the fixed-endpoint path factor unchanged. -/
theorem constHomeomorph_naturality_source {E' : Type uF} [TopologicalSpace E']
    (F : C(E, E')) (b b0 : X) :
    (constHomeomorph E' b b0 :
        C(HomotopyFiber (ContinuousMap.const E' b0) b, E' × Path b b0)).comp
      (map (f := ContinuousMap.const E b0) (f' := ContinuousMap.const E' b0)
        (b := b) (b' := b) F (ContinuousMap.id X) (fun _ => rfl) rfl) =
      (F.prodMap (ContinuousMap.id (Path b b0))).comp
        (constHomeomorph E b b0 :
          C(HomotopyFiber (ContinuousMap.const E b0) b, E × Path b b0)) := by
  apply ContinuousMap.ext
  intro z
  simpa only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
    ContinuousMap.coe_id, ContinuousMap.coe_coe] using constHomeomorph_naturality F b b0 z

/-- A continuous map of target spaces acts by postcomposition on the
fixed-endpoint path factor of the constant-map comparison. -/
theorem constHomeomorph_naturality_target {X' : Type uX'} [TopologicalSpace X']
    (G : C(X, X')) (b b0 : X) :
    (constHomeomorph E (G b) (G b0) :
        C(HomotopyFiber (ContinuousMap.const E (G b0)) (G b),
          E × Path (G b) (G b0))).comp
      (map (f := ContinuousMap.const E b0) (f' := ContinuousMap.const E (G b0))
        (b := b) (b' := G b) (ContinuousMap.id E) G (fun _ => rfl) rfl) =
      ((ContinuousMap.id E).prodMap (Path.mapContinuousMap G b b0)).comp
        (constHomeomorph E b b0 :
          C(HomotopyFiber (ContinuousMap.const E b0) b, E × Path b b0)) := by
  exact constHomeomorph_naturality_map (ContinuousMap.id E) G b b0

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
