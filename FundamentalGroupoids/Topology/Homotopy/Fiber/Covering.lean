/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber
public import FundamentalGroupoids.Topology.Covering.Lifting
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Covering fibers and ordinary homotopy fibers

The inclusion uses the original constant-path point at an arbitrary specified
strict-fiber equality and does not require a covering hypothesis. For a covering,
`reversePathLift` is the jointly continuous lift of the reversed retained
path, starting at the original retained source point. Its terminal point gives
`fiberRetraction`. At time `u`, `fiberDeformation` retains the lifted point at
`unitInterval.symm u` and the entire original path restricted by `s ↦ u * s`.

All spaces have their original product, subspace, and compact-open topologies.
The source and target have independent universes and need no separation or
local-compactness assumptions.

For the two-sheet projection `Bool × ℝ → ℝ`, at base point `0`, the point
`((true, 1), s ↦ s)` is sent by the retraction to `(true, 0)`. The deformation
has point `(true, u)` and entire retained path `s ↦ u * s`. Thus the construction
retains both the sheet and the whole path, rather than just an image endpoint.
-/

@[expose] public section

noncomputable section

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

universe uE uB

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]

variable {f : C(E, B)} {b : B}

/-- Joint evaluation of the reversed original retained path. -/
def reversePathFamily (f : C(E, B)) (b : B) : C(I × HomotopyFiber f b, B) where
  toFun tz := path tz.2 (unitInterval.symm tz.1)
  continuous_toFun :=
    ((path (f := f) (b := b)).continuous.comp continuous_snd).eval
      (continuous_symm.comp continuous_fst)

@[simp]
theorem reversePathFamily_apply (t : I) (z : HomotopyFiber f b) :
    reversePathFamily f b (t, z) = path z (unitInterval.symm t) :=
  rfl

/-- The reversed family starts at the image of the original retained point. -/
theorem reversePathFamily_zero (z : HomotopyFiber f b) :
    reversePathFamily f b (0, z) = f (point z) := by
  simp only [reversePathFamily_apply, symm_zero, path_one]

/-- The jointly continuous lift, starting at the original retained point. -/
def reversePathLift (cov : IsCoveringMap f) : C(I × HomotopyFiber f b, E) :=
  cov.liftHomotopy (reversePathFamily f b) point reversePathFamily_zero

/-- Projection of the lift recovers every time of the original reversed path. -/
theorem reversePathLift_lifts (cov : IsCoveringMap f) (t : I)
    (z : HomotopyFiber f b) :
    f (reversePathLift cov (t, z)) = path z (unitInterval.symm t) := by
  exact congr_fun
    (cov.liftHomotopy_lifts (reversePathFamily f b) point reversePathFamily_zero) (t, z)

@[simp]
theorem reversePathLift_zero (cov : IsCoveringMap f) (z : HomotopyFiber f b) :
    reversePathLift cov (0, z) = point z := by
  exact cov.liftHomotopy_zero (reversePathFamily f b) point reversePathFamily_zero z

/-- The terminal lifted point belongs to the original strict fiber. -/
theorem reversePathLift_one_mem (cov : IsCoveringMap f) (z : HomotopyFiber f b) :
    f (reversePathLift cov (1, z)) = b := by
  simpa only [symm_one, path_zero] using reversePathLift_lifts cov 1 z

/-- Retract to the strict fiber by lifting the entire reversed retained path. -/
def fiberRetraction (cov : IsCoveringMap f) :
    C(HomotopyFiber f b, {e : E // f e = b}) where
  toFun z := ⟨reversePathLift cov (1, z), reversePathLift_one_mem cov z⟩
  continuous_toFun :=
    ((reversePathLift cov).continuous.comp
      (continuous_const.prodMk continuous_id)).subtype_mk _

/-- The retraction retains the terminal point of the reversed-path lift. -/
@[simp]
theorem fiberRetraction_coe (cov : IsCoveringMap f) (z : HomotopyFiber f b) :
    (fiberRetraction cov z : E) = reversePathLift cov (1, z) :=
  rfl

/-- The retained path ends at the image of the corresponding lifted point. -/
theorem initialSegment_one_eq_reversePathLift (cov : IsCoveringMap f) (u : I)
    (z : HomotopyFiber f b) :
    initialSegment u z 1 = f (reversePathLift cov (unitInterval.symm u, z)) := by
  simpa only [initialSegment_one, symm_symm] using
    (reversePathLift_lifts cov (unitInterval.symm u) z).symm

/-- Joint deformation with the original lifted point and the entire initial
segment of the original retained path. -/
def fiberDeformation (cov : IsCoveringMap f) :
    C(I × HomotopyFiber f b, HomotopyFiber f b) where
  toFun uz := mk (reversePathLift cov (unitInterval.symm uz.1, uz.2))
    (initialSegment uz.1 uz.2) (initialSegment_zero uz.1 uz.2)
    (initialSegment_one_eq_reversePathLift cov uz.1 uz.2)
  continuous_toFun := by
    apply continuous_iff.2
    constructor
    · simpa only [point_mk, Function.comp_def] using
        (reversePathLift cov).continuous.comp
          ((continuous_symm.comp continuous_fst).prodMk continuous_snd)
    · simpa only [path_mk] using
        (continuous_initialSegment (f := f) (b := b))

/-- The point characteristic of the jointly continuous deformation. -/
@[simp]
theorem point_fiberDeformation (cov : IsCoveringMap f) (u : I)
    (z : HomotopyFiber f b) :
    point (fiberDeformation cov (u, z)) =
      reversePathLift cov (unitInterval.symm u, z) :=
  point_mk (reversePathLift cov (unitInterval.symm u, z)) (initialSegment u z)
    (initialSegment_zero u z) (initialSegment_one_eq_reversePathLift cov u z)

/-- The whole-path characteristic, as an equality of compact-open continuous maps. -/
@[simp]
theorem path_fiberDeformation (cov : IsCoveringMap f) (u : I)
    (z : HomotopyFiber f b) :
    path (fiberDeformation cov (u, z)) = initialSegment u z :=
  path_mk (reversePathLift cov (unitInterval.symm u, z)) (initialSegment u z)
    (initialSegment_zero u z) (initialSegment_one_eq_reversePathLift cov u z)

/-- Evaluation of the entire path characteristic at an arbitrary inner time. -/
theorem path_fiberDeformation_apply (cov : IsCoveringMap f) (u s : I)
    (z : HomotopyFiber f b) :
    path (fiberDeformation cov (u, z)) s = path z (u * s) := by
  rw [path_fiberDeformation, initialSegment_apply]

/-- Restricting the whole joint lift to the original inclusion gives the
constant-in-time strict-fiber point. -/
theorem reversePathLift_comp_fiberInclusion (cov : IsCoveringMap f) :
    (reversePathLift cov).comp
        ((ContinuousMap.id I).prodMap (fiberInclusion f b)) =
      (ContinuousMap.subtypeVal {e : E | f e = b}).comp ContinuousMap.snd := by
  rw [reversePathLift, ← cov.liftHomotopy_comp_prodMap]
  symm
  apply (cov.eq_liftHomotopy_iff'
    (H := (reversePathFamily f b).comp
      ((ContinuousMap.id I).prodMap (fiberInclusion f b)))
    (f := point.comp (fiberInclusion f b))
    (fun e => reversePathFamily_zero (fiberInclusion f b e)) _).2
  constructor
  · funext x
    rcases x with ⟨t, e⟩
    simpa only [Function.comp_apply, ContinuousMap.comp_apply,
      ContinuousMap.snd_apply, ContinuousMap.subtypeVal_apply,
      ContinuousMap.prodMap_apply, Prod.map_apply, ContinuousMap.id_apply,
      reversePathFamily_apply, path_fiberInclusion, ContinuousMap.const_apply] using e.property
  · intro e
    simp only [ContinuousMap.comp_apply, ContinuousMap.snd_apply,
      ContinuousMap.subtypeVal_apply, point_fiberInclusion]

/-- The reversed-path lift fixes every original constant-path point. -/
theorem reversePathLift_fiberInclusion (cov : IsCoveringMap f) (t : I)
    (e : E) (h : f e = b) :
    reversePathLift cov (t, fiberInclusion f b ⟨e, h⟩) = e := by
  simpa only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
    Prod.map_apply, ContinuousMap.id_apply, ContinuousMap.snd_apply,
    ContinuousMap.subtypeVal_apply] using
    ContinuousMap.congr_fun (reversePathLift_comp_fiberInclusion cov) (t, ⟨e, h⟩)

/-- The canonical retraction is a left inverse of the original inclusion at every
independently specified strict-fiber equality. -/
theorem fiberRetraction_fiberInclusion (cov : IsCoveringMap f)
    (e : E) (h : f e = b) :
    fiberRetraction cov (fiberInclusion f b ⟨e, h⟩) = ⟨e, h⟩ := by
  apply Subtype.ext
  rw [fiberRetraction_coe]
  exact reversePathLift_fiberInclusion cov 1 e h

/-- The deformation starts at inclusion after retraction, as an equality in
the original homotopy fiber. -/
theorem fiberDeformation_zero (cov : IsCoveringMap f) (z : HomotopyFiber f b) :
    fiberDeformation cov (0, z) = fiberInclusion f b (fiberRetraction cov z) := by
  apply ext
  · simp only [point_fiberDeformation, symm_zero, point_fiberInclusion,
      fiberRetraction_coe]
  · apply ContinuousMap.ext
    intro s
    simp only [path_fiberDeformation_apply, zero_mul, path_zero,
      path_fiberInclusion, ContinuousMap.const_apply]

/-- The deformation ends at the identity, including the entire original
retained path. -/
theorem fiberDeformation_one (cov : IsCoveringMap f) (z : HomotopyFiber f b) :
    fiberDeformation cov (1, z) = z := by
  apply ext
  · simp only [point_fiberDeformation, symm_one, reversePathLift_zero]
  · apply ContinuousMap.ext
    intro s
    simp only [path_fiberDeformation_apply, one_mul]

/-- Every original included strict-fiber point is fixed at every time, without
replacing its specified equality witness. -/
theorem fiberDeformation_fixed (cov : IsCoveringMap f) (u : I)
    (e : E) (h : f e = b) :
    fiberDeformation cov (u, fiberInclusion f b ⟨e, h⟩) =
      fiberInclusion f b ⟨e, h⟩ := by
  apply ext
  · simp only [point_fiberDeformation, reversePathLift_fiberInclusion,
      point_fiberInclusion]
  · apply ContinuousMap.ext
    intro s
    simp only [path_fiberDeformation_apply, path_fiberInclusion, ContinuousMap.const_apply]

/-- The canonical homotopy equivalence from the strict fiber to the
original homotopy fiber, using the inclusion and reversed-path retraction. -/
def fiberHomotopyEquiv (cov : IsCoveringMap f) :
    ContinuousMap.HomotopyEquiv {e : E // f e = b} (HomotopyFiber f b) where
  toFun := fiberInclusion f b
  invFun := fiberRetraction cov
  left_inv := by
    have hi : (fiberRetraction cov).comp (fiberInclusion f b) =
        ContinuousMap.id {e : E // f e = b} := by
      apply ContinuousMap.ext
      intro e
      exact fiberRetraction_fiberInclusion cov e.1 e.2
    simpa only [hi] using
      ContinuousMap.Homotopic.refl (ContinuousMap.id {e : E // f e = b})
  right_inv := ⟨{
    toContinuousMap := fiberDeformation cov
    map_zero_left := fiberDeformation_zero cov
    map_one_left := fiberDeformation_one cov }⟩

@[simp]
theorem fiberHomotopyEquiv_apply (cov : IsCoveringMap f) (e : {e : E // f e = b}) :
    fiberHomotopyEquiv cov e = fiberInclusion f b e :=
  rfl

@[simp]
theorem fiberHomotopyEquiv_symm_apply (cov : IsCoveringMap f) (z : HomotopyFiber f b) :
    (fiberHomotopyEquiv cov).symm z = fiberRetraction cov z :=
  rfl

/-- A homotopy equivalence with the canonical maps in both
directions. -/
theorem exists_fiberHomotopyEquiv (cov : IsCoveringMap f) :
    ∃ h : ContinuousMap.HomotopyEquiv {e : E // f e = b} (HomotopyFiber f b),
      (∀ e, h e = fiberInclusion f b e) ∧
      ∀ z, h.symm z = fiberRetraction cov z := by
  exact ⟨fiberHomotopyEquiv cov, fun _ => rfl, fun _ => rfl⟩

end ContinuousMap.HomotopyFiber
