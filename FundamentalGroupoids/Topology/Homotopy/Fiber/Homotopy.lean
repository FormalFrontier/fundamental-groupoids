/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber
public import FundamentalGroupoids.Topology.Path
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path
import Mathlib.Tactic.NormNum

/-!
# Homotopy invariance of ordinary homotopy fibers

For a specified homotopy `H` between continuous maps `f g : C(E, B)`,
`homotopyMap H b` keeps the point `e` in a homotopy-fiber point `(e, γ)` and
appends the path traced by `H` at `e` after the whole supplied path `γ`.
Thus the path still starts at `b` and now ends at `g e`. The reverse map is
the same construction for `H.symm`.

The named left and right inverse homotopies retain `e` at every time. Their
path families reassociate concatenation, cancel the appended homotopy path
with its reverse, and remove the right unit. The resulting `homotopyEquiv`
is an unbased homotopy equivalence, not a strict inverse or a homeomorphism.
The target point `b` is arbitrary and does not select a point of the fiber;
preservation of arbitrarily chosen fiber-basepoints is not asserted.

## Implementation notes

The carrier and path direction are those of `ContinuousMap.HomotopyFiber`:
a retained point `e` and a path from `b` to `f e`. Only ordinary product,
subspace, and compact-open topologies are used. The spaces `E` and `B` have
independent universes, with no separation or local-compactness assumptions;
only the interval is used as a locally compact evaluation domain. May's
standing weak-Hausdorff/k-space conventions are not identified with these
ordinary topologies.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, for homotopy fibers
  and their homotopy invariance.
* `FundamentalGroupoids.Topology.Homotopy.Fiber`, for the carrier and path
  orientation of the ordinary homotopy fiber.
* Mathlib's path-homotopy association, cancellation, and right-unit constructions.
-/

@[expose] public section

noncomputable section

open unitInterval
open scoped Topology ContinuousMap

namespace ContinuousMap.HomotopyFiber

universe uE uB

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]
variable {f g : C(E, B)}

/-- The entire supplied path, viewed as a homotopy from the constant base map to
`f` composed with the retained-point projection. -/
def pathHomotopy (f : C(E, B)) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.const (HomotopyFiber f b) b)
      (f.comp (point (f := f) (b := b))) where
  toContinuousMap := (path (f := f) (b := b)).uncurry.comp
    (ContinuousMap.prodSwap :
      C(I × HomotopyFiber f b, HomotopyFiber f b × I))
  map_zero_left z := path_zero (f := f) (b := b) z
  map_one_left z := path_one (f := f) (b := b) z

@[simp]
theorem pathHomotopy_apply (f : C(E, B)) (b : B) (t : I)
    (z : HomotopyFiber f b) :
    pathHomotopy f b (t, z) = path (f := f) (b := b) z t :=
  rfl

/-- Append the path traced by the supplied homotopy at the retained point. -/
private def appendedPathHomotopy (H : ContinuousMap.Homotopy f g) (b : B) :
    ContinuousMap.Homotopy (ContinuousMap.const (HomotopyFiber f b) b)
      (g.comp (point (f := f) (b := b))) :=
  (pathHomotopy f b).trans
    (H.compContinuousMap (point (f := f) (b := b)))

/-- Curry in the path parameter, without a local-compactness assumption on the fiber. -/
private def appendedPaths (H : ContinuousMap.Homotopy f g) (b : B) :
    C(HomotopyFiber f b, C(I, B)) :=
  ((appendedPathHomotopy (f := f) (g := g) H b).toContinuousMap.comp
    (ContinuousMap.prodSwap :
      C(HomotopyFiber f b × I, I × HomotopyFiber f b))).curry

/-- The continuous map of ordinary homotopy fibers induced by the specified homotopy.
It keeps the source point and appends the homotopy path to the entire supplied path. -/
@[no_expose]
def homotopyMap (H : ContinuousMap.Homotopy f g) (b : B) :
    C(HomotopyFiber f b, HomotopyFiber g b) where
  toFun z := mk (f := g) (b := b) (point (f := f) (b := b) z)
    (appendedPaths (f := f) (g := g) H b z)
    ((appendedPathHomotopy (f := f) (g := g) H b).map_zero_left z)
    ((appendedPathHomotopy (f := f) (g := g) H b).map_one_left z)
  continuous_toFun := by
    apply continuous_iff.2
    exact ⟨(point (f := f) (b := b)).continuous,
      (appendedPaths (f := f) (g := g) H b).continuous⟩

private theorem point_homotopyMap_eq (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    point (f := g) (b := b) (homotopyMap (f := f) (g := g) H b z) =
      point (f := f) (b := b) z :=
  rfl

/-- The forward map retains the original source point. -/
@[simp]
theorem point_homotopyMap (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    point (f := g) (b := b) (homotopyMap (f := f) (g := g) H b z) =
      point (f := f) (b := b) z :=
  point_homotopyMap_eq (f := f) (g := g) H b z

private theorem path_homotopyMap_eq (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    path (f := g) (b := b) (homotopyMap (f := f) (g := g) H b z) =
      ((⟨path (f := f) (b := b) z, path_zero (f := f) (b := b) z,
          path_one (f := f) (b := b) z⟩ :
          Path b (f (point (f := f) (b := b) z))).trans
        (H.evalAt (point (f := f) (b := b) z))).toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The complete forward path is the supplied path first, then the path traced by `H`. -/
theorem path_homotopyMap (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    path (f := g) (b := b) (homotopyMap (f := f) (g := g) H b z) =
      ((⟨path (f := f) (b := b) z, path_zero (f := f) (b := b) z,
          path_one (f := f) (b := b) z⟩ :
          Path b (f (point (f := f) (b := b) z))).trans
        (H.evalAt (point (f := f) (b := b) z))).toContinuousMap := by
  exact path_homotopyMap_eq (f := f) (g := g) H b z

/-- The retained-point projection commutes with the whole forward continuous map. -/
theorem point_comp_homotopyMap (H : ContinuousMap.Homotopy f g) (b : B) :
    (point (f := g) (b := b)).comp (homotopyMap (f := f) (g := g) H b) =
      point (f := f) (b := b) :=
  ContinuousMap.ext (point_homotopyMap (f := f) (g := g) H b)

private theorem path_comp_homotopyMap_eq (H : ContinuousMap.Homotopy f g) (b : B) :
    (path (f := g) (b := b)).comp (homotopyMap (f := f) (g := g) H b) =
      ((((pathHomotopy f b).trans
          (H.compContinuousMap (point (f := f) (b := b)))).toContinuousMap).comp
        (ContinuousMap.prodSwap :
          C(HomotopyFiber f b × I, I × HomotopyFiber f b))).curry :=
  rfl

/-- The whole compact-open path projection is the curried concatenated family. -/
theorem path_comp_homotopyMap (H : ContinuousMap.Homotopy f g) (b : B) :
    (path (f := g) (b := b)).comp (homotopyMap (f := f) (g := g) H b) =
      ((((pathHomotopy f b).trans
          (H.compContinuousMap (point (f := f) (b := b)))).toContinuousMap).comp
        (ContinuousMap.prodSwap :
          C(HomotopyFiber f b × I, I × HomotopyFiber f b))).curry :=
  path_comp_homotopyMap_eq (f := f) (g := g) H b

/-- Evaluation observes the full concatenated forward path at its new time parameter. -/
theorem eval_homotopyMap (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) (t : I) :
    eval (f := g) (b := b) t (homotopyMap (f := f) (g := g) H b z) =
      ((⟨path (f := f) (b := b) z, path_zero (f := f) (b := b) z,
          path_one (f := f) (b := b) z⟩ :
          Path b (f (point (f := f) (b := b) z))).trans
        (H.evalAt (point (f := f) (b := b) z))) t := by
  exact congrArg (fun γ : C(I, B) => γ t)
    (path_homotopyMap (f := f) (g := g) H b z)

/-- The reverse map is the same construction for `H.symm` and retains the point. -/
theorem point_homotopyMap_symm (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber g b) :
    point (f := f) (b := b) (homotopyMap (f := g) (g := f) H.symm b z) =
      point (f := g) (b := b) z :=
  point_homotopyMap (f := g) (g := f) H.symm b z

/-- The reverse map appends the reversed `H`-path to the entire supplied target path. -/
theorem path_homotopyMap_symm (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber g b) :
    path (f := f) (b := b) (homotopyMap (f := g) (g := f) H.symm b z) =
      ((⟨path (f := g) (b := b) z, path_zero (f := g) (b := b) z,
          path_one (f := g) (b := b) z⟩ :
          Path b (g (point (f := g) (b := b) z))).trans
        (H.evalAt (point (f := g) (b := b) z)).symm).toContinuousMap := by
  exact path_homotopyMap (f := g) (g := f) H.symm b z

/-- Evaluation of the reverse map uses the concatenated supplied path and reversed `H`. -/
theorem eval_homotopyMap_symm (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber g b) (t : I) :
    eval (f := f) (b := b) t (homotopyMap (f := g) (g := f) H.symm b z) =
      ((⟨path (f := g) (b := b) z, path_zero (f := g) (b := b) z,
          path_one (f := g) (b := b) z⟩ :
          Path b (g (point (f := g) (b := b) z))).trans
        (H.evalAt (point (f := g) (b := b) z)).symm) t := by
  exact congrArg (fun γ : C(I, B) => γ t)
    (path_homotopyMap_symm (f := f) (g := g) H b z)

/-- Bundle the original retained continuous map as a path, without changing it. -/
private def retainedPath {f : C(E, B)} {b : B} (z : HomotopyFiber f b) :
    Path b (f (point (f := f) (b := b) z)) :=
  ⟨path (f := f) (b := b) z, path_zero (f := f) (b := b) z,
    path_one (f := f) (b := b) z⟩

/-- Associate the appended path, cancel its reversed tail, then remove the right unit. -/
private def leftPathHomotopy (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    Path.Homotopy
      (((retainedPath z).trans (H.evalAt (point z))).trans
        (H.evalAt (point z)).symm) (retainedPath z) :=
  (Path.Homotopy.transAssoc (retainedPath z) (H.evalAt (point z))
      (H.evalAt (point z)).symm).trans
    (((Path.Homotopy.refl (retainedPath z)).hcomp
        (Path.Homotopy.reflTransSymm (H.evalAt (point z))).symm).trans
      (Path.Homotopy.transRefl (retainedPath z)))

private theorem leftPathHomotopy_continuous (H : ContinuousMap.Homotopy f g) (b : B) :
    Continuous (fun v : HomotopyFiber f b × I × I =>
      leftPathHomotopy H b v.1 (v.2.1, v.2.2)) := by
  let p := fun z : HomotopyFiber f b => retainedPath z
  let q := fun z : HomotopyFiber f b => H.evalAt (point z)
  have hp : Continuous (fun v : HomotopyFiber f b × I => p v.1 v.2) :=
    (path (f := f) (b := b)).uncurry.continuous
  have hq : Continuous (fun v : HomotopyFiber f b × I => q v.1 v.2) :=
    H.continuous.comp
      (continuous_snd.prodMk ((point (f := f) (b := b)).continuous.comp continuous_fst))
  have hqs : Continuous (fun v : HomotopyFiber f b × I => (q v.1).symm v.2) :=
    Path.symm_continuous_family q hq
  have hA := Path.Homotopy.transAssoc_continuous_family
    p q (fun z => (q z).symm) hp hq hqs
  have hRefl : Continuous (fun v : HomotopyFiber f b × I × I =>
      Path.Homotopy.refl (p v.1) (v.2.1, v.2.2)) :=
    hp.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hCancel := Path.Homotopy.reflTransSymm_continuous_family q hq
  have hCancelSymm : Continuous (fun v : HomotopyFiber f b × I × I =>
      (Path.Homotopy.reflTransSymm (q v.1)).symm (v.2.1, v.2.2)) :=
    hCancel.comp (continuous_fst.prodMk
      ((unitInterval.continuous_symm.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd)))
  have hB := Path.Homotopy.hcomp_continuous_family
    (fun z => Path.Homotopy.refl (p z))
    (fun z => (Path.Homotopy.reflTransSymm (q z)).symm) hRefl hCancelSymm
  have hC := Path.Homotopy.transRefl_continuous_family p hp
  have hBC := ContinuousMap.Homotopy.trans_continuous_family
    (fun z => ((Path.Homotopy.refl (p z)).hcomp
      (Path.Homotopy.reflTransSymm (q z)).symm).toHomotopy)
    (fun z => (Path.Homotopy.transRefl (p z)).toHomotopy) hB hC
  exact ContinuousMap.Homotopy.trans_continuous_family
    (fun z => (Path.Homotopy.transAssoc (p z) (q z) (q z).symm).toHomotopy)
    (fun z => (((Path.Homotopy.refl (p z)).hcomp
      (Path.Homotopy.reflTransSymm (q z)).symm).trans
        (Path.Homotopy.transRefl (p z))).toHomotopy) hA hBC

/-- Curry only the inner interval coordinate of the jointly continuous family. -/
private def leftHomotopyPaths (H : ContinuousMap.Homotopy f g) (b : B) :
    C(I × HomotopyFiber f b, C(I, B)) :=
  let joint : C(HomotopyFiber f b × I × I, B) :=
    { toFun := fun v => leftPathHomotopy H b v.1 (v.2.1, v.2.2)
      continuous_toFun := leftPathHomotopy_continuous H b }
  let reindex :
      C((I × HomotopyFiber f b) × I, HomotopyFiber f b × I × I) :=
    { toFun := fun v => (v.1.2, (v.1.1, v.2))
      continuous_toFun := (continuous_snd.comp continuous_fst).prodMk
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd) }
  (joint.comp reindex).curry

/-- The inverse-homotopy family before identifying its endpoint continuous maps. -/
private def leftHomotopyFamily (H : ContinuousMap.Homotopy f g) (b : B) :
    C(I × HomotopyFiber f b, HomotopyFiber f b) where
  toFun v := mk (f := f) (b := b) (point v.2) (leftHomotopyPaths H b v)
    ((leftPathHomotopy H b v.2).eval v.1).source
    ((leftPathHomotopy H b v.2).eval v.1).target
  continuous_toFun := by
    have hp : Continuous (fun v : I × HomotopyFiber f b => point v.2) :=
      (point (f := f) (b := b)).continuous.comp continuous_snd
    have hγ : Continuous (fun v : I × HomotopyFiber f b => leftHomotopyPaths H b v) :=
      (leftHomotopyPaths H b).continuous
    apply continuous_iff.2
    constructor
    · exact Eq.mpr (congrArg Continuous (funext fun v : I × HomotopyFiber f b =>
        point_mk (f := f) (b := b) (point v.2) (leftHomotopyPaths H b v)
          ((leftPathHomotopy H b v.2).eval v.1).source
          ((leftPathHomotopy H b v.2).eval v.1).target)) hp
    · exact Eq.mpr (congrArg Continuous (funext fun v : I × HomotopyFiber f b =>
        path_mk (f := f) (b := b) (point v.2) (leftHomotopyPaths H b v)
          ((leftPathHomotopy H b v.2).eval v.1).source
          ((leftPathHomotopy H b v.2).eval v.1).target)) hγ

private theorem leftHomotopyFamily_zero (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    leftHomotopyFamily H b (0, z) =
      ((homotopyMap H.symm b).comp (homotopyMap H b)) z := by
  apply ext
  · change point z = point (homotopyMap H.symm b (homotopyMap H b z))
    simp only [point_homotopyMap]
  · apply ContinuousMap.ext
    intro t
    change leftPathHomotopy H b z (0, t) =
      path (homotopyMap H.symm b (homotopyMap H b z)) t
    exact (leftPathHomotopy H b z).toHomotopy.map_zero_left t

private theorem leftHomotopyFamily_one (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    leftHomotopyFamily H b (1, z) = ContinuousMap.id (HomotopyFiber f b) z := by
  apply ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    change leftPathHomotopy H b z (1, t) = path z t
    exact (leftPathHomotopy H b z).toHomotopy.map_one_left t

/-- The left inverse homotopy associates and cancels the appended homotopy path,
then removes the right unit. It keeps the original point at every time. -/
@[no_expose]
def homotopyMapLeftHomotopy (H : ContinuousMap.Homotopy f g) (b : B) :
    ContinuousMap.Homotopy ((homotopyMap H.symm b).comp (homotopyMap H b))
      (ContinuousMap.id (HomotopyFiber f b)) where
  toContinuousMap := leftHomotopyFamily H b
  map_zero_left := leftHomotopyFamily_zero H b
  map_one_left := leftHomotopyFamily_one H b

/-- The right inverse homotopy is the left inverse homotopy for the reversed
supplied homotopy; the cast changes only its boundary map identification. -/
def homotopyMapRightHomotopy (H : ContinuousMap.Homotopy f g) (b : B) :
    ContinuousMap.Homotopy ((homotopyMap H b).comp (homotopyMap H.symm b))
      (ContinuousMap.id (HomotopyFiber g b)) :=
  (homotopyMapLeftHomotopy H.symm b).cast
    (congrArg (fun J : ContinuousMap.Homotopy f g =>
      (homotopyMap J b).comp (homotopyMap H.symm b))
      (ContinuousMap.Homotopy.symm_symm H)) rfl

/-- The homotopy equivalence of ordinary homotopy fibers supplied by `H`.
Its maps append the supplied homotopy path and its reverse, respectively.

This is the ordinary-topology, unbased form of homotopy invariance of the
homotopy fiber in J. P. May's *A Concise Course in Algebraic Topology*.
Preservation of an arbitrarily chosen point of the fiber is not asserted. -/
def homotopyEquiv (H : ContinuousMap.Homotopy f g) (b : B) :
    HomotopyFiber f b ≃ₕ HomotopyFiber g b where
  toFun := homotopyMap H b
  invFun := homotopyMap H.symm b
  left_inv := ⟨homotopyMapLeftHomotopy H b⟩
  right_inv := ⟨homotopyMapRightHomotopy H b⟩

private theorem point_homotopyMapLeftHomotopy_eq (H : ContinuousMap.Homotopy f g) (b : B)
    (s : I) (z : HomotopyFiber f b) :
    point (homotopyMapLeftHomotopy H b (s, z)) = point z :=
  rfl

/-- Every stage of the left inverse homotopy retains the original point. -/
@[simp]
theorem point_homotopyMapLeftHomotopy (H : ContinuousMap.Homotopy f g) (b : B)
    (s : I) (z : HomotopyFiber f b) :
    point (homotopyMapLeftHomotopy H b (s, z)) = point z :=
  point_homotopyMapLeftHomotopy_eq (f := f) (g := g) H b s z

private theorem path_homotopyMapLeftHomotopy_eq (H : ContinuousMap.Homotopy f g) (b : B)
    (s : I) (z : HomotopyFiber f b) :
    path (homotopyMapLeftHomotopy H b (s, z)) =
      let p : Path b (f (point z)) :=
        ⟨path z, path_zero z, path_one z⟩
      let q := H.evalAt (point z)
      (((Path.Homotopy.transAssoc p q q.symm).trans
        (((Path.Homotopy.refl p).hcomp (Path.Homotopy.reflTransSymm q).symm).trans
          (Path.Homotopy.transRefl p))).eval s).toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The full compact-open path at every stage of the left inverse homotopy is
specified by the standard association, cancellation, and right-unit homotopies. -/
theorem path_homotopyMapLeftHomotopy (H : ContinuousMap.Homotopy f g) (b : B)
    (s : I) (z : HomotopyFiber f b) :
    path (homotopyMapLeftHomotopy H b (s, z)) =
      let p : Path b (f (point z)) :=
        ⟨path z, path_zero z, path_one z⟩
      let q := H.evalAt (point z)
      (((Path.Homotopy.transAssoc p q q.symm).trans
        (((Path.Homotopy.refl p).hcomp (Path.Homotopy.reflTransSymm q).symm).trans
          (Path.Homotopy.transRefl p))).eval s).toContinuousMap :=
  path_homotopyMapLeftHomotopy_eq (f := f) (g := g) H b s z

/-- Evaluation of the left inverse homotopy observes the specified entire path. -/
theorem eval_homotopyMapLeftHomotopy (H : ContinuousMap.Homotopy f g) (b : B)
    (s t : I) (z : HomotopyFiber f b) :
    eval t (homotopyMapLeftHomotopy H b (s, z)) =
      let p : Path b (f (point z)) :=
        ⟨path z, path_zero z, path_one z⟩
      let q := H.evalAt (point z)
      ((Path.Homotopy.transAssoc p q q.symm).trans
        (((Path.Homotopy.refl p).hcomp (Path.Homotopy.reflTransSymm q).symm).trans
          (Path.Homotopy.transRefl p))) (s, t) := by
  exact congrArg (fun γ : C(I, B) => γ t)
    (path_homotopyMapLeftHomotopy (f := f) (g := g) H b s z)

/-- At the first joining time, association has finished and the original path
is followed by the homotopy path and its reverse grouped as a single tail. -/
theorem path_homotopyMapLeftHomotopy_half (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    path (homotopyMapLeftHomotopy H b (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩, z)) =
      let p : Path b (f (point z)) :=
        ⟨path z, path_zero z, path_one z⟩
      let q := H.evalAt (point z)
      (p.trans (q.trans q.symm)).toContinuousMap := by
  let p : Path b (f (point z)) := ⟨path z, path_zero z, path_one z⟩
  let q := H.evalAt (point z)
  rw [path_homotopyMapLeftHomotopy]
  apply ContinuousMap.ext
  intro t
  change
    ((Path.Homotopy.transAssoc p q q.symm).trans
      (((Path.Homotopy.refl p).hcomp (Path.Homotopy.reflTransSymm q).symm).trans
        (Path.Homotopy.transRefl p)))
      (⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩, t) =
        (p.trans (q.trans q.symm)) t
  rw [Path.Homotopy.trans_apply]
  norm_num

private theorem point_homotopyMapRightHomotopy_eq (H : ContinuousMap.Homotopy f g) (b : B)
    (s : I) (z : HomotopyFiber g b) :
    point (homotopyMapRightHomotopy H b (s, z)) = point z :=
  rfl

/-- Every stage of the right inverse homotopy retains the original point. -/
@[simp]
theorem point_homotopyMapRightHomotopy (H : ContinuousMap.Homotopy f g) (b : B)
    (s : I) (z : HomotopyFiber g b) :
    point (homotopyMapRightHomotopy H b (s, z)) = point z :=
  point_homotopyMapRightHomotopy_eq (f := f) (g := g) H b s z

private theorem path_homotopyMapRightHomotopy_eq (H : ContinuousMap.Homotopy f g) (b : B)
    (s : I) (z : HomotopyFiber g b) :
    path (homotopyMapRightHomotopy H b (s, z)) =
      let p : Path b (g (point z)) :=
        ⟨path z, path_zero z, path_one z⟩
      let q := (H.evalAt (point z)).symm
      (((Path.Homotopy.transAssoc p q q.symm).trans
        (((Path.Homotopy.refl p).hcomp (Path.Homotopy.reflTransSymm q).symm).trans
          (Path.Homotopy.transRefl p))).eval s).toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The complete path at every right-inverse stage uses the same association,
cancellation, and right-unit homotopies with the reversed supplied homotopy path. -/
theorem path_homotopyMapRightHomotopy (H : ContinuousMap.Homotopy f g) (b : B)
    (s : I) (z : HomotopyFiber g b) :
    path (homotopyMapRightHomotopy H b (s, z)) =
      let p : Path b (g (point z)) :=
        ⟨path z, path_zero z, path_one z⟩
      let q := (H.evalAt (point z)).symm
      (((Path.Homotopy.transAssoc p q q.symm).trans
        (((Path.Homotopy.refl p).hcomp (Path.Homotopy.reflTransSymm q).symm).trans
          (Path.Homotopy.transRefl p))).eval s).toContinuousMap :=
  path_homotopyMapRightHomotopy_eq (f := f) (g := g) H b s z

/-- Evaluation of the right inverse homotopy observes the specified entire path. -/
theorem eval_homotopyMapRightHomotopy (H : ContinuousMap.Homotopy f g) (b : B)
    (s t : I) (z : HomotopyFiber g b) :
    eval t (homotopyMapRightHomotopy H b (s, z)) =
      let p : Path b (g (point z)) :=
        ⟨path z, path_zero z, path_one z⟩
      let q := (H.evalAt (point z)).symm
      ((Path.Homotopy.transAssoc p q q.symm).trans
        (((Path.Homotopy.refl p).hcomp (Path.Homotopy.reflTransSymm q).symm).trans
          (Path.Homotopy.transRefl p))) (s, t) := by
  exact congrArg (fun γ : C(I, B) => γ t)
    (path_homotopyMapRightHomotopy (f := f) (g := g) H b s z)

/-- The forward continuous map of the homotopy equivalence is the append map. -/
theorem homotopyEquiv_toFun (H : ContinuousMap.Homotopy f g) (b : B) :
    (homotopyEquiv H b).toFun = homotopyMap H b :=
  rfl

/-- The inverse continuous map is the same append construction for `H.symm`. -/
theorem homotopyEquiv_symm_toFun (H : ContinuousMap.Homotopy f g) (b : B) :
    (homotopyEquiv H b).symm.toFun = homotopyMap H.symm b :=
  rfl

/-- The equivalence retains the point in the forward direction. -/
@[simp]
theorem point_homotopyEquiv (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    point (homotopyEquiv H b z) = point z :=
  point_homotopyMap H b z

/-- Its complete forward path is the original path followed by the `H`-path. -/
theorem path_homotopyEquiv (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber f b) :
    path (homotopyEquiv H b z) =
      ((⟨path z, path_zero z, path_one z⟩ : Path b (f (point z))).trans
        (H.evalAt (point z))).toContinuousMap :=
  path_homotopyMap H b z

/-- The equivalence retains the point in the inverse direction. -/
@[simp]
theorem point_homotopyEquiv_symm (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber g b) :
    point ((homotopyEquiv H b).symm z) = point z :=
  point_homotopyMap_symm H b z

/-- Its complete inverse path is the original path followed by the reversed
supplied homotopy path, not an unspecified inverse path. -/
theorem path_homotopyEquiv_symm (H : ContinuousMap.Homotopy f g) (b : B)
    (z : HomotopyFiber g b) :
    path ((homotopyEquiv H b).symm z) =
      ((⟨path z, path_zero z, path_one z⟩ : Path b (g (point z))).trans
        (H.evalAt (point z)).symm).toContinuousMap :=
  path_homotopyMap_symm H b z

end ContinuousMap.HomotopyFiber
