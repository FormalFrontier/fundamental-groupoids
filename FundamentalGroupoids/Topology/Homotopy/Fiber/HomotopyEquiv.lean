/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Equiv
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Homotopy
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Homeomorph

/-!
# Domain homotopy equivalences of ordinary homotopy fibers

Precomposition by a homotopy equivalence induces a homotopy equivalence on the
ordinary homotopy fibers. The forward map is the map of a commutative square.
The inverse retains the incoming path and appends the reversed image of the
right inverse homotopy. The left inverse homotopy uses the endpoint-relative
triangle for `ContinuousMap.Homotopy.adjointifyLeft`; both inverse homotopies
finish with the right-unit homotopy of paths.

Only the original subspace and compact-open topologies are used. All path
families are jointly continuous; no topology on path homotopies is required.
Concatenation is not identified with a strictly unital operation.

## References

* Mathlib's continuous-map homotopies and homotopy equivalences.
* `ContinuousMap.Homotopy.adjointifyLeftTriangle`, for the coherent left trace.
* `Path.Homotopy.transRefl_continuous_family` and
  `ContinuousMap.initialSegment`, for varying paths and their right units.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

universe uD uE uB uZ

variable {D : Type uD} {E : Type uE} {B : Type uB}
variable [TopologicalSpace D] [TopologicalSpace E] [TopologicalSpace B]

noncomputable section

/-- Bundle the incoming path without changing its parametrization. -/
private def incoming {f : C(E, B)} {b : B} (z : HomotopyFiber f b) :
    Path b (f (point z)) :=
  ⟨path z, path_zero z, path_one z⟩

/-- Package a jointly continuous family of paths into the original fiber. -/
private def ofPathFamily {Z : Type uZ} [TopologicalSpace Z]
    {f : C(E, B)} {b : B} (x : C(Z, E))
    (p : ∀ z, Path b (f (x z)))
    (hp : Continuous (fun v : Z × I => p v.1 v.2)) :
    C(Z, HomotopyFiber f b) where
  toFun z := mk (x z) (p z).toContinuousMap (p z).source (p z).target
  continuous_toFun := by
    apply continuous_iff.2
    exact ⟨x.continuous,
      ({ toFun := fun v : Z × I => p v.1 v.2
         continuous_toFun := hp } : C(Z × I, B)).curry.continuous⟩

private def timeSlice {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (H : C(I × X, Y)) (s : I) : C(X, Y) :=
  H.comp ((ContinuousMap.const X s).prodMk (ContinuousMap.id X))

private theorem timeSlice_apply {X : Type*} {Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (H : C(I × X, Y)) (s : I) (x : X) : timeSlice H s x = H (s, x) := rfl

/-- The initial segment of the reversed trace is the reversed remaining tail. -/
private def reverseTail {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B)
    (v : I × HomotopyFiber f b) :
    Path (f (point v.2)) (f (H (v.1, point v.2))) :=
  ⟨ContinuousMap.initialSegment
      (unitInterval.symm v.1,
        (((H.evalAt (point v.2)).map f.continuous).symm).toContinuousMap),
    by
      change f (H (unitInterval.symm (unitInterval.symm v.1 * 0), point v.2)) = _
      simp,
    by
      change f (H (unitInterval.symm (unitInterval.symm v.1 * 1), point v.2)) = _
      simp⟩

private theorem reverseTail_apply {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B)
    (v : I × HomotopyFiber f b) (r : I) :
    reverseTail f H b v r =
      f (H (unitInterval.symm (unitInterval.symm v.1 * r), point v.2)) := rfl

private def tailPath {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B)
    (v : I × HomotopyFiber f b) : Path b (f (H (v.1, point v.2))) :=
  (incoming v.2).trans (reverseTail f H b v)

private def tailFamily {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B) :
    C(I × HomotopyFiber f b, HomotopyFiber f b) :=
  ofPathFamily
    (H.toContinuousMap.comp
      ((_root_.ContinuousMap.fst : C(I × HomotopyFiber f b, I)).prodMk
        ((point (f := f) (b := b)).comp (_root_.ContinuousMap.snd : C(I × HomotopyFiber f b,
          HomotopyFiber f b)))))
    (tailPath f H b) (by
      have hγ : Continuous (fun v : (I × HomotopyFiber f b) × I =>
          incoming v.1.2 v.2) :=
        (path (f := f) (b := b)).uncurry.continuous.comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
      have hmulReal : Continuous (fun v : (I × HomotopyFiber f b) × I =>
          ((unitInterval.symm v.1.1 : I) : ℝ) * (v.2 : ℝ)) := by
        fun_prop
      have hmul : Continuous (fun v : (I × HomotopyFiber f b) × I =>
          unitInterval.symm v.1.1 * v.2) :=
        hmulReal.subtype_mk (fun v => (unitInterval.symm v.1.1 * v.2 : I).2)
      have htime : Continuous (fun v : (I × HomotopyFiber f b) × I =>
          (unitInterval.symm (unitInterval.symm v.1.1 * v.2), point v.1.2)) :=
        (unitInterval.continuous_symm.comp hmul).prodMk
          ((point (f := f) (b := b)).continuous.comp
            (continuous_snd.comp continuous_fst))
      have hδ : Continuous (fun v : (I × HomotopyFiber f b) × I =>
          reverseTail f H b v.1 v.2) :=
        f.continuous.comp (H.continuous.comp htime)
      exact Path.trans_continuous_family
        (fun v : I × HomotopyFiber f b => incoming v.2) hγ
        (reverseTail f H b) hδ)

private def unitorFamily (f : C(E, B)) (b : B) :
    C(I × HomotopyFiber f b, HomotopyFiber f b) :=
  ofPathFamily ((point (f := f) (b := b)).comp (_root_.ContinuousMap.snd : C(I × HomotopyFiber
    f b, HomotopyFiber f b)))
    (fun v => (Path.Homotopy.transRefl (incoming v.2)).eval v.1) (by
      have hp : Continuous (fun v : HomotopyFiber f b × I => incoming v.1 v.2) :=
        (path (f := f) (b := b)).uncurry.continuous
      have hperm : Continuous (fun v : (I × HomotopyFiber f b) × I =>
          (v.1.2, (v.1.1, v.2))) :=
        (continuous_snd.comp continuous_fst).prodMk
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
      exact (Path.Homotopy.transRefl_continuous_family
        (fun z : HomotopyFiber f b => incoming z) hp).comp hperm)

private theorem point_tailFamily {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B) (v : I × HomotopyFiber f b) :
    point (tailFamily f H b v) = H (v.1, point v.2) := rfl

private theorem path_tailFamily {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B) (v : I × HomotopyFiber f b) :
    path (tailFamily f H b v) = (tailPath f H b v).toContinuousMap := rfl

private theorem point_unitorFamily (f : C(E, B)) (b : B) (v : I × HomotopyFiber f b) :
    point (unitorFamily f b v) = point v.2 := rfl

private theorem path_unitorFamily (f : C(E, B)) (b : B) (v : I × HomotopyFiber f b) :
    path (unitorFamily f b v) =
      ((Path.Homotopy.transRefl (incoming v.2)).eval v.1).toContinuousMap := rfl

private theorem trans_path_congr {a a' c c' d d' : B}
    (p : Path a c) (p' : Path a' c') (q : Path c d) (q' : Path c' d')
    (hp : p.toContinuousMap = p'.toContinuousMap)
    (hq : q.toContinuousMap = q'.toContinuousMap) :
    (p.trans q).toContinuousMap = (p'.trans q').toContinuousMap := by
  apply ContinuousMap.ext
  intro t
  refine (Path.trans_apply p q t).trans (Eq.trans ?_ (Path.trans_apply p' q' t).symm)
  split_ifs
  · exact congrArg (fun γ : C(I, B) => γ _) hp
  · exact congrArg (fun γ : C(I, B) => γ _) hq

private def tailPhase {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B) :
    (timeSlice (tailFamily f H b) 0).Homotopy
      (timeSlice (unitorFamily f b) 0) where
  toContinuousMap := tailFamily f H b
  map_zero_left _ := rfl
  map_one_left z := by
    apply ext
    · exact (point_tailFamily f H b (1, z)).trans
        ((H.apply_one (point z)).trans ((point_unitorFamily f b (0, z)).symm.trans
          (congrArg (fun w : HomotopyFiber f b => point w)
            (timeSlice_apply (unitorFamily f b) 0 z)).symm))
    · have ht : (reverseTail f H b (1, z)).toContinuousMap =
          (Path.refl (f (point z))).toContinuousMap := by
        apply ContinuousMap.ext
        intro r
        have ht : reverseTail f H b (1, z) r = f (H (1, point z)) := by
          simpa only [unitInterval.symm_one, zero_mul, unitInterval.symm_zero] using
            reverseTail_apply f H b (1, z) r
        have hc : (reverseTail f H b (1, z)).toContinuousMap r =
            reverseTail f H b (1, z) r := rfl
        have hH : f (H (1, point z)) = f (point z) :=
          congrArg f (H.apply_one (point z))
        have hr : (Path.refl (f (point z))).toContinuousMap r = f (point z) := rfl
        exact hc.trans (ht.trans (hH.trans hr.symm))
      exact (path_tailFamily f H b (1, z)).trans
        ((trans_path_congr (incoming z) (incoming z)
          (reverseTail f H b (1, z)) (Path.refl (f (point z))) rfl ht).trans
            ((ContinuousMap.ext fun t =>
              ((Path.Homotopy.transRefl (incoming z)).apply_zero t).symm).trans
                (path_unitorFamily f b (0, z)).symm))

private def unitorPhase (f : C(E, B)) (b : B) :
    (timeSlice (unitorFamily f b) 0).Homotopy
      (ContinuousMap.id (HomotopyFiber f b)) where
  toContinuousMap := unitorFamily f b
  map_zero_left _ := rfl
  map_one_left z := by
    apply ext
    · exact point_unitorFamily f b (1, z)
    · exact (path_unitorFamily f b (1, z)).trans
        (ContinuousMap.ext fun t => (Path.Homotopy.transRefl (incoming z)).apply_one t)

private theorem tailPhase_apply {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B) (v : I × HomotopyFiber f b) :
    tailPhase f H b v = tailFamily f H b v := rfl

private theorem point_tailPhase {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B) (v : I × HomotopyFiber f b) :
    point (tailPhase f H b v) = H (v.1, point v.2) :=
  (congrArg (fun z : HomotopyFiber f b => point z) (tailPhase_apply f H b v)).trans
    (point_tailFamily f H b v)

private theorem path_tailPhase {k : C(E, E)} (f : C(E, B))
    (H : k.Homotopy (ContinuousMap.id E)) (b : B) (v : I × HomotopyFiber f b) :
    path (tailPhase f H b v) = (tailPath f H b v).toContinuousMap :=
  (congrArg (fun z : HomotopyFiber f b => path z) (tailPhase_apply f H b v)).trans
    (path_tailFamily f H b v)

private theorem unitorPhase_apply (f : C(E, B)) (b : B) (v : I × HomotopyFiber f b) :
    unitorPhase f b v = unitorFamily f b v := rfl

private theorem point_unitorPhase (f : C(E, B)) (b : B) (v : I × HomotopyFiber f b) :
    point (unitorPhase f b v) = point v.2 :=
  (congrArg (fun z : HomotopyFiber f b => point z) (unitorPhase_apply f b v)).trans
    (point_unitorFamily f b v)

private theorem path_unitorPhase (f : C(E, B)) (b : B) (v : I × HomotopyFiber f b) :
    path (unitorPhase f b v) =
      ((Path.Homotopy.transRefl (incoming v.2)).eval v.1).toContinuousMap :=
  (congrArg (fun z : HomotopyFiber f b => path z) (unitorPhase_apply f b v)).trans
    (path_unitorFamily f b v)

/-- Append the reversed counit, then apply the inverse to the source point. -/
private def precompInverse (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    C(HomotopyFiber f b, HomotopyFiber (f.comp e.toFun) b) :=
  let ε : (e.toFun.comp e.invFun).Homotopy (ContinuousMap.id E) :=
    Classical.choice e.right_inv
  let H : ((f.comp e.toFun).comp e.invFun).Homotopy f :=
    (ContinuousMap.Homotopy.refl f).comp ε
  (map (f := (f.comp e.toFun).comp e.invFun) (f' := f.comp e.toFun)
      (b := b) (b' := b) e.invFun (ContinuousMap.id B) (fun _ => rfl) rfl).comp
    (homotopyMap (f := f) (g := (f.comp e.toFun).comp e.invFun) H.symm b)

private theorem point_precompInverse (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) (z : HomotopyFiber f b) :
    point (precompInverse f e b z) = e.invFun (point z) := by
  let ε : (e.toFun.comp e.invFun).Homotopy (ContinuousMap.id E) :=
    Classical.choice e.right_inv
  let H : ((f.comp e.toFun).comp e.invFun).Homotopy f :=
    (ContinuousMap.Homotopy.refl f).comp ε
  exact (point_map (f := (f.comp e.toFun).comp e.invFun) (f' := f.comp e.toFun)
    (b := b) (b' := b) e.invFun (ContinuousMap.id B) (fun _ => rfl) rfl
    (homotopyMap (f := f) (g := (f.comp e.toFun).comp e.invFun) H.symm b z)).trans
      (congrArg (fun y : E => e.invFun y)
        (point_homotopyMap (f := f) (g := (f.comp e.toFun).comp e.invFun) H.symm b z))

private theorem path_precompInverse (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) (z : HomotopyFiber f b) :
    path (precompInverse f e b z) =
      ((incoming z).trans
        ((((Classical.choice e.right_inv).evalAt (point z)).map f.continuous).symm)
        ).toContinuousMap := by
  let ε : (e.toFun.comp e.invFun).Homotopy (ContinuousMap.id E) :=
    Classical.choice e.right_inv
  let H : ((f.comp e.toFun).comp e.invFun).Homotopy f :=
    (ContinuousMap.Homotopy.refl f).comp ε
  have htrace : H.evalAt (point z) = (ε.evalAt (point z)).map f.continuous := by
    apply Path.ext
    funext t
    rfl
  have hp := path_homotopyMap_symm
    (f := (f.comp e.toFun).comp e.invFun) (g := f) H b z
  have hq := congrArg
    (fun q : Path (((f.comp e.toFun).comp e.invFun) (point z)) (f (point z)) =>
      ((incoming z).trans q.symm).toContinuousMap) htrace
  exact (path_map (f := (f.comp e.toFun).comp e.invFun) (f' := f.comp e.toFun)
    (b := b) (b' := b) e.invFun (ContinuousMap.id B) (fun _ => rfl) rfl
    (homotopyMap (f := f) (g := (f.comp e.toFun).comp e.invFun) H.symm b z)).trans
      ((ContinuousMap.id_comp _).trans (hp.trans hq))

private def triangleTrace (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (v : I × HomotopyFiber (f.comp e.toFun) b) :
    Path (f (e.toFun (point v.2)))
      (f (e.toFun (e.invFun (e.toFun (point v.2))))) :=
  let η := Classical.choice e.left_inv
  let ε := Classical.choice e.right_inv
  let K := ContinuousMap.Homotopy.adjointifyLeftTriangle η ε
  ⟨{ toFun := fun t => f (K (unitInterval.symm v.1, (unitInterval.symm t, point v.2)))
     continuous_toFun := f.continuous.comp (K.continuous.comp (by fun_prop)) },
    by
      exact (congrArg (fun r : I => f (K (unitInterval.symm v.1, (r, point v.2))))
        unitInterval.symm_zero).trans
          (congrArg f (ContinuousMap.Homotopy.adjointifyLeftTriangle_target
            η ε (unitInterval.symm v.1) (point v.2))),
    by
      exact (congrArg (fun r : I => f (K (unitInterval.symm v.1, (r, point v.2))))
        unitInterval.symm_one).trans
          (congrArg f (ContinuousMap.Homotopy.adjointifyLeftTriangle_source
            η ε (unitInterval.symm v.1) (point v.2)))⟩

private theorem triangleTrace_apply (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (v : I × HomotopyFiber (f.comp e.toFun) b) (r : I) :
    triangleTrace f e b v r = f (ContinuousMap.Homotopy.adjointifyLeftTriangle
      (Classical.choice e.left_inv) (Classical.choice e.right_inv)
        (unitInterval.symm v.1, (unitInterval.symm r, point v.2))) := rfl

private def trianglePath (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (v : I × HomotopyFiber (f.comp e.toFun) b) :
    Path b (f (e.toFun (e.invFun (e.toFun (point v.2))))) :=
  (incoming v.2).trans (triangleTrace f e b v)

private def triangleFamily (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    C(I × HomotopyFiber (f.comp e.toFun) b, HomotopyFiber (f.comp e.toFun) b) :=
  ofPathFamily
    (e.invFun.comp (e.toFun.comp
      ((point (f := f.comp e.toFun) (b := b)).comp (_root_.ContinuousMap.snd :
        C(I × HomotopyFiber (f.comp e.toFun) b, HomotopyFiber (f.comp e.toFun) b)))))
    (trianglePath f e b) (by
      have hγ : Continuous (fun v : (I × HomotopyFiber (f.comp e.toFun) b) × I =>
          incoming v.1.2 v.2) :=
        (path (f := f.comp e.toFun) (b := b)).uncurry.continuous.comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
      have htime : Continuous (fun v : (I × HomotopyFiber (f.comp e.toFun) b) × I =>
          (unitInterval.symm v.1.1, (unitInterval.symm v.2, point v.1.2))) := by
        fun_prop
      have hδ : Continuous (fun v : (I × HomotopyFiber (f.comp e.toFun) b) × I =>
          triangleTrace f e b v.1 v.2) :=
        f.continuous.comp
          ((ContinuousMap.Homotopy.adjointifyLeftTriangle
            (Classical.choice e.left_inv) (Classical.choice e.right_inv)).continuous.comp htime)
      exact Path.trans_continuous_family
        (fun v : I × HomotopyFiber (f.comp e.toFun) b => incoming v.2) hγ
        (triangleTrace f e b) hδ)

private theorem point_triangleFamily (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (v : I × HomotopyFiber (f.comp e.toFun) b) :
    point (triangleFamily f e b v) = e.invFun (e.toFun (point v.2)) := rfl

private theorem path_triangleFamily (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (v : I × HomotopyFiber (f.comp e.toFun) b) :
    path (triangleFamily f e b v) = (trianglePath f e b v).toContinuousMap := rfl

private def trianglePhase (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    ((precompInverse f e b).comp
      (map (f := f.comp e.toFun) (f' := f) e.toFun
        (ContinuousMap.id B) (fun _ => rfl) rfl)).Homotopy
      (timeSlice (tailFamily (f.comp e.toFun)
        (ContinuousMap.Homotopy.adjointifyLeft
          (Classical.choice e.left_inv) (Classical.choice e.right_inv)) b) 0) where
  toContinuousMap := triangleFamily f e b
  map_zero_left z := by
    let η : (e.invFun.comp e.toFun).Homotopy (ContinuousMap.id D) :=
      Classical.choice e.left_inv
    let ε : (e.toFun.comp e.invFun).Homotopy (ContinuousMap.id E) :=
      Classical.choice e.right_inv
    let F := map (f := f.comp e.toFun) (f' := f) (b := b) (b' := b)
      e.toFun (ContinuousMap.id B) (fun _ => rfl) rfl
    have hpoint : point (F z) = e.toFun (point z) :=
      point_map (f := f.comp e.toFun) (f' := f) (b := b) (b' := b)
        e.toFun (ContinuousMap.id B) (fun _ => rfl) rfl z
    apply ext
    · exact (point_triangleFamily f e b (0, z)).trans
        ((congrArg (fun y : E => e.invFun y) hpoint).symm.trans
          (point_precompInverse f e b (F z)).symm)
    · have hin : (incoming z).toContinuousMap = (incoming (F z)).toContinuousMap :=
        ((path_map (f := f.comp e.toFun) (f' := f) (b := b) (b' := b)
          e.toFun (ContinuousMap.id B) (fun _ => rfl) rfl z).trans
            (ContinuousMap.id_comp _)).symm
      have htrace : (triangleTrace f e b (0, z)).toContinuousMap =
          (((ε.evalAt (point (F z))).map f.continuous).symm).toContinuousMap := by
        apply ContinuousMap.ext
        intro r
        calc
          triangleTrace f e b (0, z) r =
              f (ε (unitInterval.symm r, e.toFun (point z))) :=
            (triangleTrace_apply f e b (0, z) r).trans (by
              simpa only [unitInterval.symm_zero] using congrArg f
                (ContinuousMap.Homotopy.adjointifyLeftTriangle_one η ε
                  (unitInterval.symm r) (point z)))
          _ = f (ε (unitInterval.symm r, point (F z))) :=
            congrArg (fun y : E => f (ε (unitInterval.symm r, y))) hpoint.symm
      exact (path_triangleFamily f e b (0, z)).trans
        ((trans_path_congr (incoming z) (incoming (F z))
          (triangleTrace f e b (0, z))
          (((ε.evalAt (point (F z))).map f.continuous).symm) hin htrace).trans
            (path_precompInverse f e b (F z)).symm)
  map_one_left z := by
    let η : (e.invFun.comp e.toFun).Homotopy (ContinuousMap.id D) :=
      Classical.choice e.left_inv
    let ε : (e.toFun.comp e.invFun).Homotopy (ContinuousMap.id E) :=
      Classical.choice e.right_inv
    let η' := ContinuousMap.Homotopy.adjointifyLeft η ε
    apply ext
    · exact (point_triangleFamily f e b (1, z)).trans
        ((η'.apply_zero (point z)).symm.trans
          (point_tailFamily (f.comp e.toFun) η' b (0, z)).symm)
    · have htrace : (triangleTrace f e b (1, z)).toContinuousMap =
          (reverseTail (f.comp e.toFun) η' b (0, z)).toContinuousMap := by
        apply ContinuousMap.ext
        intro r
        calc
          triangleTrace f e b (1, z) r = f (e.toFun (η' (unitInterval.symm r, point z))) := by
            exact (triangleTrace_apply f e b (1, z) r).trans (by
              simpa only [unitInterval.symm_one] using congrArg f
                (ContinuousMap.Homotopy.adjointifyLeftTriangle_zero η ε
                  (unitInterval.symm r) (point z)))
          _ = reverseTail (f.comp e.toFun) η' b (0, z) r := by
            symm
            simpa only [unitInterval.symm_zero, one_mul, ContinuousMap.comp_apply] using
              reverseTail_apply (f.comp e.toFun) η' b (0, z) r
      exact (path_triangleFamily f e b (1, z)).trans
        ((trans_path_congr (incoming z) (incoming z)
          (triangleTrace f e b (1, z)) (reverseTail (f.comp e.toFun) η' b (0, z)) rfl
          htrace).trans (path_tailFamily (f.comp e.toFun) η' b (0, z)).symm)

private theorem trianglePhase_apply (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (v : I × HomotopyFiber (f.comp e.toFun) b) :
    trianglePhase f e b v = triangleFamily f e b v := rfl

private theorem point_trianglePhase (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (v : I × HomotopyFiber (f.comp e.toFun) b) :
    point (trianglePhase f e b v) = e.invFun (e.toFun (point v.2)) :=
  (congrArg (fun z : HomotopyFiber (f.comp e.toFun) b => point z)
    (trianglePhase_apply f e b v)).trans (point_triangleFamily f e b v)

private theorem path_trianglePhase (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (v : I × HomotopyFiber (f.comp e.toFun) b) :
    path (trianglePhase f e b v) = (trianglePath f e b v).toContinuousMap :=
  (congrArg (fun z : HomotopyFiber (f.comp e.toFun) b => path z)
    (trianglePhase_apply f e b v)).trans (path_triangleFamily f e b v)

private def precompLeftFamily (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    ((precompInverse f e b).comp
      (map (f := f.comp e.toFun) (f' := f) e.toFun
        (ContinuousMap.id B) (fun _ => rfl) rfl)).Homotopy
      (ContinuousMap.id (HomotopyFiber (f.comp e.toFun) b)) :=
  (trianglePhase f e b).trans
    ((tailPhase (f.comp e.toFun)
      (ContinuousMap.Homotopy.adjointifyLeft
        (Classical.choice e.left_inv) (Classical.choice e.right_inv)) b).trans
      (unitorPhase (f.comp e.toFun) b))

private def precompRightFamily (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    ((map (f := f.comp e.toFun) (f' := f) e.toFun
      (ContinuousMap.id B) (fun _ => rfl) rfl).comp
        (precompInverse f e b)).Homotopy
      (ContinuousMap.id (HomotopyFiber f b)) := by
  refine ((tailPhase f (Classical.choice e.right_inv) b).trans
    (unitorPhase f b)).cast ?_ rfl
  let ε : (e.toFun.comp e.invFun).Homotopy (ContinuousMap.id E) :=
    Classical.choice e.right_inv
  apply ContinuousMap.ext
  intro z
  apply ext
  · exact (point_tailFamily f ε b (0, z)).trans
      ((ε.apply_zero (point z)).trans
        ((congrArg (fun y : D => e.toFun y) (point_precompInverse f e b z)).symm.trans
          (point_map (f := f.comp e.toFun) (f' := f) (b := b) (b' := b)
            e.toFun (ContinuousMap.id B) (fun _ => rfl) rfl
              (precompInverse f e b z)).symm))
  · have ht : (reverseTail f ε b (0, z)).toContinuousMap =
        (((ε.evalAt (point z)).map f.continuous).symm).toContinuousMap := by
      apply ContinuousMap.ext
      intro r
      have ht : reverseTail f ε b (0, z) r = f (ε (unitInterval.symm r, point z)) := by
        simpa only [unitInterval.symm_zero, one_mul] using reverseTail_apply f ε b (0, z) r
      have hc : (reverseTail f ε b (0, z)).toContinuousMap r =
          reverseTail f ε b (0, z) r := rfl
      have hε : (((ε.evalAt (point z)).map f.continuous).symm).toContinuousMap r =
          f (ε (unitInterval.symm r, point z)) := rfl
      exact hc.trans (ht.trans hε.symm)
    have hp : path (map (f := f.comp e.toFun) (f' := f) (b := b) (b' := b)
        e.toFun (ContinuousMap.id B) (fun _ => rfl) rfl (precompInverse f e b z)) =
        ((incoming z).trans (((ε.evalAt (point z)).map f.continuous).symm)
          ).toContinuousMap :=
      (path_map (f := f.comp e.toFun) (f' := f) (b := b) (b' := b)
        e.toFun (ContinuousMap.id B) (fun _ => rfl) rfl (precompInverse f e b z)).trans
          ((ContinuousMap.id_comp _).trans (path_precompInverse f e b z))
    exact (path_tailFamily f ε b (0, z)).trans
      ((trans_path_congr (incoming z) (incoming z) (reverseTail f ε b (0, z))
        (((ε.evalAt (point z)).map f.continuous).symm) rfl ht).trans hp.symm)

/-- Precomposition by a homotopy equivalence induces a homotopy equivalence
between the ordinary homotopy fibers, retaining the whole incoming path. -/
@[no_expose]
noncomputable def precompHomotopyEquiv (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (f.comp e.toFun) b) (HomotopyFiber f b) where
  toFun := map e.toFun (ContinuousMap.id B) (fun _ => rfl) rfl
  invFun := precompInverse f e b
  left_inv := ⟨by exact precompLeftFamily f e b⟩
  right_inv := ⟨by exact precompRightFamily f e b⟩

/-- The left inverse homotopy uses the coherent triangle, the remaining left
trace, and the right-unit homotopy of the incoming path, in that order. -/
@[no_expose]
noncomputable def precompLeftHomotopy (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    ((precompHomotopyEquiv f e b).symm.toFun.comp
      (precompHomotopyEquiv f e b).toFun).Homotopy
      (ContinuousMap.id (HomotopyFiber (f.comp e.toFun) b)) :=
  precompLeftFamily f e b

/-- The right inverse homotopy follows the remaining counit trace and then
removes the right unit from the incoming path. -/
@[no_expose]
noncomputable def precompRightHomotopy (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    ((precompHomotopyEquiv f e b).toFun.comp
      (precompHomotopyEquiv f e b).symm.toFun).Homotopy
      (ContinuousMap.id (HomotopyFiber f b)) :=
  precompRightFamily f e b

private theorem precompLeftHomotopy_apply (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (v : I × HomotopyFiber (f.comp e.toFun) b) :
    precompLeftHomotopy f e b v =
      ((trianglePhase f e b).trans
        ((tailPhase (f.comp e.toFun) (ContinuousMap.Homotopy.adjointifyLeft
          (Classical.choice e.left_inv) (Classical.choice e.right_inv)) b).trans
            (unitorPhase (f.comp e.toFun) b))) v := rfl

private theorem precompRightHomotopy_apply (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) (v : I × HomotopyFiber f b) :
    precompRightHomotopy f e b v =
      ((tailPhase f (Classical.choice e.right_inv) b).trans (unitorPhase f b)) v := rfl

private theorem precompHomotopyEquiv_toFun_eq (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    (precompHomotopyEquiv f e b).toFun =
      map (f := f.comp e.toFun) (f' := f) e.toFun
        (ContinuousMap.id B) (fun _ => rfl) rfl := rfl

/-- The forward map is the map of the precomposition square. -/
theorem precompHomotopyEquiv_toFun (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) :
    (precompHomotopyEquiv f e b).toFun =
      map (f := f.comp e.toFun) (f' := f) e.toFun
        (ContinuousMap.id B) (fun _ => rfl) rfl := by
  exact precompHomotopyEquiv_toFun_eq f e b

/-- The forward source point follows the supplied equivalence. -/
theorem point_precompHomotopyEquiv (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber (f.comp e.toFun) b) :
    point (precompHomotopyEquiv f e b z) = e.toFun (point z) := by
  exact (congrArg
    (fun F : C(HomotopyFiber (f.comp e.toFun) b, HomotopyFiber f b) => point (F z))
      (precompHomotopyEquiv_toFun f e b)).trans
        (point_map (f := f.comp e.toFun) (f' := f) (b := b) (b' := b)
          e.toFun (ContinuousMap.id B) (fun _ => rfl) rfl z)

/-- The forward map retains the entire incoming compact-open path. -/
theorem path_precompHomotopyEquiv (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber (f.comp e.toFun) b) :
    path (precompHomotopyEquiv f e b z) = path z := by
  exact (congrArg
    (fun F : C(HomotopyFiber (f.comp e.toFun) b, HomotopyFiber f b) => path (F z))
      (precompHomotopyEquiv_toFun f e b)).trans
        ((path_map (f := f.comp e.toFun) (f' := f) (b := b) (b' := b)
          e.toFun (ContinuousMap.id B) (fun _ => rfl) rfl z).trans
            (ContinuousMap.id_comp _))

/-- Every path coordinate of the forward map is unchanged. -/
theorem eval_precompHomotopyEquiv (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber (f.comp e.toFun) b) (t : I) :
    eval t (precompHomotopyEquiv f e b z) = eval t z := by
  exact congrArg (fun γ : C(I, B) => γ t) (path_precompHomotopyEquiv f e b z)

/-- The inverse source point follows the supplied inverse. -/
theorem point_precompHomotopyEquiv_symm (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber f b) :
    point ((precompHomotopyEquiv f e b).symm z) = e.invFun (point z) := by
  exact point_precompInverse f e b z

/-- The inverse appends the reversed image of the complete counit trace. -/
theorem path_precompHomotopyEquiv_symm (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber f b) :
    path ((precompHomotopyEquiv f e b).symm z) =
      ((⟨path z, path_zero z, path_one z⟩ : Path b (f (point z))).trans
        ((((Classical.choice e.right_inv).evalAt (point z)).map f.continuous).symm)
        ).toContinuousMap := by
  exact path_precompInverse f e b z

/-- Every coordinate of the inverse is the corresponding concatenated-path value. -/
theorem eval_precompHomotopyEquiv_symm (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber f b) (t : I) :
    eval t ((precompHomotopyEquiv f e b).symm z) =
      ((⟨path z, path_zero z, path_one z⟩ : Path b (f (point z))).trans
        ((((Classical.choice e.right_inv).evalAt (point z)).map f.continuous).symm)) t :=
  congrArg (fun γ : C(I, B) => γ t) (path_precompHomotopyEquiv_symm f e b z)

/-- The source point throughout the left inverse homotopy, with its concatenation clocks. -/
theorem point_precompLeftHomotopy (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) (s : I)
    (z : HomotopyFiber (f.comp e.toFun) b) :
    point (precompLeftHomotopy f e b (s, z)) =
    let η := Classical.choice e.left_inv
    let ε := Classical.choice e.right_inv
    let η' := ContinuousMap.Homotopy.adjointifyLeft η ε
    if hs : (s : ℝ) ≤ 1 / 2 then e.invFun (e.toFun (point z))
    else let u := (⟨2 * (s : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le,
      s.2.2⟩⟩ : I)
         if hu : (u : ℝ) ≤ 1 / 2 then η' ((⟨2 * (u : ℝ), (unitInterval.mul_pos_mem_iff
           zero_lt_two).2 ⟨u.2.1, hu⟩⟩ : I), point z)
         else point z := by
  rw [precompLeftHomotopy_apply, ContinuousMap.Homotopy.trans_apply]
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · simpa only [dite_eq_left hs] using point_trianglePhase f e b
      ((⟨2 * (s : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩ : I), z)
  · simp only [dite_eq_right hs]
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact point_tailPhase (f.comp e.toFun)
        (ContinuousMap.Homotopy.adjointifyLeft
          (Classical.choice e.left_inv) (Classical.choice e.right_inv)) b _
    · exact point_unitorPhase (f.comp e.toFun) b _

/-- The entire path throughout the left inverse homotopy, including both inner branches. -/
theorem path_precompLeftHomotopy (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) (s : I)
    (z : HomotopyFiber (f.comp e.toFun) b) :
    (path (precompLeftHomotopy f e b (s, z)) : I → B) =
    let η := Classical.choice e.left_inv
    let ε := Classical.choice e.right_inv
    let η' := ContinuousMap.Homotopy.adjointifyLeft η ε
    let K := ContinuousMap.Homotopy.adjointifyLeftTriangle η ε
    fun (t : I) =>
      if hs : (s : ℝ) ≤ 1 / 2 then
        if ht : (t : ℝ) ≤ 1 / 2 then path z (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff
          zero_lt_two).2 ⟨t.2.1, ht⟩⟩ : I)
        else f (K (unitInterval.symm (⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff
          zero_lt_two).2 ⟨s.2.1, hs⟩⟩ : I),
          (unitInterval.symm (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, t.2.2⟩⟩ : I), point z)))
      else let u := (⟨2 * (s : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1
        hs).le, s.2.2⟩⟩ : I)
           if hu : (u : ℝ) ≤ 1 / 2 then
             if ht : (t : ℝ) ≤ 1 / 2 then path z (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff
               zero_lt_two).2 ⟨t.2.1, ht⟩⟩ : I)
             else f (e.toFun (η'
               (unitInterval.symm ((unitInterval.symm (⟨2 * (u : ℝ),
                 (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨u.2.1,
                 hu⟩⟩ : I)) * (⟨2 * (t : ℝ) - 1,
                   unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le,
                     t.2.2⟩⟩ : I)), point z)))
           else Path.Homotopy.transRefl
             (⟨path z, path_zero z, path_one z⟩ :
               Path b (f (e.toFun (point z)))) ((⟨2 * (u : ℝ) - 1,
                 unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hu).le, u.2.2⟩⟩ : I), t) := by
  funext t
  rw [precompLeftHomotopy_apply, ContinuousMap.Homotopy.trans_apply]
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · simp only [dite_eq_left hs]
    let v : I := ⟨2 * (s : ℝ),
      (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩
    exact (congrArg (fun γ : C(I, B) => γ t) (path_trianglePhase f e b (v, z))).trans
      (Path.trans_apply (incoming z) (triangleTrace f e b (v, z)) t)
  · simp only [dite_eq_right hs]
    rw [ContinuousMap.Homotopy.trans_apply]
    let u : I := ⟨2 * (s : ℝ) - 1,
      unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩
    by_cases hu : 2 * (s : ℝ) - 1 ≤ 1 / 2
    · simp only [dite_eq_left hu]
      let v : I := ⟨2 * (u : ℝ),
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨u.2.1, hu⟩⟩
      let η' := ContinuousMap.Homotopy.adjointifyLeft
        (Classical.choice e.left_inv) (Classical.choice e.right_inv)
      exact (congrArg (fun γ : C(I, B) => γ t)
        (path_tailPhase (f.comp e.toFun) η' b (v, z))).trans
          (Path.trans_apply (incoming z) (reverseTail (f.comp e.toFun) η' b (v, z)) t)
    · simp only [dite_eq_right hu]
      exact congrArg (fun γ : C(I, B) => γ t)
        (path_unitorPhase (f.comp e.toFun) b
          ((⟨2 * (u : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hu).le, u.2.2⟩⟩ : I), z))

/-- Evaluation at every inner time in the left inverse homotopy. -/
theorem eval_precompLeftHomotopy (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) (s t : I)
    (z : HomotopyFiber (f.comp e.toFun) b) :
    eval t (precompLeftHomotopy f e b (s, z)) =
    let η := Classical.choice e.left_inv
    let ε := Classical.choice e.right_inv
    let η' := ContinuousMap.Homotopy.adjointifyLeft η ε
    let K := ContinuousMap.Homotopy.adjointifyLeftTriangle η ε
      if hs : (s : ℝ) ≤ 1 / 2 then
        if ht : (t : ℝ) ≤ 1 / 2 then path z (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff
          zero_lt_two).2 ⟨t.2.1, ht⟩⟩ : I)
        else f (K (unitInterval.symm (⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff
          zero_lt_two).2 ⟨s.2.1, hs⟩⟩ : I),
          (unitInterval.symm (⟨2 * (t : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 ht).le, t.2.2⟩⟩ : I), point z)))
      else let u := (⟨2 * (s : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1
        hs).le, s.2.2⟩⟩ : I)
           if hu : (u : ℝ) ≤ 1 / 2 then
             if ht : (t : ℝ) ≤ 1 / 2 then path z (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff
               zero_lt_two).2 ⟨t.2.1, ht⟩⟩ : I)
             else f (e.toFun (η'
               (unitInterval.symm ((unitInterval.symm (⟨2 * (u : ℝ),
                 (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨u.2.1,
                 hu⟩⟩ : I)) * (⟨2 * (t : ℝ) - 1,
                   unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le,
                     t.2.2⟩⟩ : I)), point z)))
           else Path.Homotopy.transRefl
             (⟨path z, path_zero z, path_one z⟩ :
               Path b (f (e.toFun (point z)))) ((⟨2 * (u : ℝ) - 1,
                 unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hu).le, u.2.2⟩⟩ : I), t) := by
  exact congrFun (path_precompLeftHomotopy f e b s z) t

/-- The source point throughout the right inverse homotopy, with its concatenation clocks. -/
theorem point_precompRightHomotopy (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) (s : I)
    (z : HomotopyFiber f b) :
    point (precompRightHomotopy f e b (s, z)) =
    let ε := Classical.choice e.right_inv
    if hs : (s : ℝ) ≤ 1 / 2 then ε ((⟨2 * (s : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
      ⟨s.2.1, hs⟩⟩ : I), point z)
    else point z := by
  rw [precompRightHomotopy_apply, ContinuousMap.Homotopy.trans_apply]
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · simp only [dite_eq_left hs]
    exact point_tailPhase f (Classical.choice e.right_inv) b _
  · simp only [dite_eq_right hs]
    exact point_unitorPhase f b _

/-- The entire path throughout the right inverse homotopy, including both inner branches. -/
theorem path_precompRightHomotopy (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) (s : I)
    (z : HomotopyFiber f b) :
    (path (precompRightHomotopy f e b (s, z)) : I → B) =
    let ε := Classical.choice e.right_inv
    fun (t : I) =>
      if hs : (s : ℝ) ≤ 1 / 2 then
        if ht : (t : ℝ) ≤ 1 / 2 then path z (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff
          zero_lt_two).2 ⟨t.2.1, ht⟩⟩ : I)
        else f (ε (unitInterval.symm ((unitInterval.symm (⟨2 * (s : ℝ),
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1,
          hs⟩⟩ : I)) * (⟨2 * (t : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ : I)), point z))
      else Path.Homotopy.transRefl
        (⟨path z, path_zero z, path_one z⟩ : Path b (f (point z))) ((⟨2 * (s : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩ : I), t) := by
  funext t
  rw [precompRightHomotopy_apply, ContinuousMap.Homotopy.trans_apply]
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · simp only [dite_eq_left hs]
    let v : I := ⟨2 * (s : ℝ),
      (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩
    exact (congrArg (fun γ : C(I, B) => γ t)
      (path_tailPhase f (Classical.choice e.right_inv) b (v, z))).trans
        (Path.trans_apply (incoming z)
          (reverseTail f (Classical.choice e.right_inv) b (v, z)) t)
  · simp only [dite_eq_right hs]
    exact congrArg (fun γ : C(I, B) => γ t)
      (path_unitorPhase f b
        ((⟨2 * (s : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩ : I), z))

/-- Evaluation at every inner time in the right inverse homotopy. -/
theorem eval_precompRightHomotopy (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B) (s t : I)
    (z : HomotopyFiber f b) :
    eval t (precompRightHomotopy f e b (s, z)) =
    let ε := Classical.choice e.right_inv
      if hs : (s : ℝ) ≤ 1 / 2 then
        if ht : (t : ℝ) ≤ 1 / 2 then path z (⟨2 * (t : ℝ), (unitInterval.mul_pos_mem_iff
          zero_lt_two).2 ⟨t.2.1, ht⟩⟩ : I)
        else f (ε (unitInterval.symm ((unitInterval.symm (⟨2 * (s : ℝ),
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1,
          hs⟩⟩ : I)) * (⟨2 * (t : ℝ) - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩ : I)), point z))
      else Path.Homotopy.transRefl
        (⟨path z, path_zero z, path_one z⟩ : Path b (f (point z))) ((⟨2 * (s : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩ : I), t) := by
  exact congrFun (path_precompRightHomotopy f e b s z) t

/-- The left homotopy starts at the inverse followed by the forward map. -/
theorem precompLeftHomotopy_zero (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber (f.comp e.toFun) b) :
    precompLeftHomotopy f e b (0, z) =
      (precompHomotopyEquiv f e b).symm (precompHomotopyEquiv f e b z) :=
  (precompLeftHomotopy f e b).apply_zero z

/-- The left homotopy ends at the original fiber point. -/
theorem precompLeftHomotopy_one (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber (f.comp e.toFun) b) :
    precompLeftHomotopy f e b (1, z) = z :=
  (precompLeftHomotopy f e b).apply_one z

/-- The right homotopy starts at the forward map followed by the inverse. -/
theorem precompRightHomotopy_zero (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber f b) :
    precompRightHomotopy f e b (0, z) =
      precompHomotopyEquiv f e b ((precompHomotopyEquiv f e b).symm z) :=
  (precompRightHomotopy f e b).apply_zero z

/-- The right homotopy ends at the original fiber point. -/
theorem precompRightHomotopy_one (f : C(E, B))
    (e : ContinuousMap.HomotopyEquiv D E) (b : B)
    (z : HomotopyFiber f b) :
    precompRightHomotopy f e b (1, z) = z :=
  (precompRightHomotopy f e b).apply_one z

/-- For a homeomorphism the forward map is the square homeomorphism's forward map. -/
theorem precompHomotopyEquiv_toFun_homeomorph (f : C(E, B))
    (a : D ≃ₜ E) (b : B) :
    (precompHomotopyEquiv f a.toHomotopyEquiv b).toFun =
      (homeomorph (f := f.comp (a : C(D, E))) (g := f) (y := b) (y' := b)
        a (Homeomorph.refl B) (fun _ => rfl) rfl :
          C(HomotopyFiber (f.comp (a : C(D, E))) b, HomotopyFiber f b)) := by
  exact (precompHomotopyEquiv_toFun f a.toHomotopyEquiv b).trans
    (homeomorph_toContinuousMap (f := f.comp (a : C(D, E))) (g := f)
      (y := b) (y' := b) a (Homeomorph.refl B) (fun _ => rfl) rfl).symm

/-- For a homeomorphism the inverse is homotopic to the square homeomorphism's
inverse; concatenation units need not be equal as parametrized paths. -/
theorem precompHomotopyEquiv_symm_toFun_homotopic_homeomorph (f : C(E, B))
    (a : D ≃ₜ E) (b : B) :
    ((precompHomotopyEquiv f a.toHomotopyEquiv b).symm.toFun).Homotopic
      ((homeomorph (f := f.comp (a : C(D, E))) (g := f) (y := b) (y' := b)
        a (Homeomorph.refl B) (fun _ => rfl) rfl).symm :
          C(HomotopyFiber f b, HomotopyFiber (f.comp (a : C(D, E))) b)) := by
  let Q := homeomorph (f := f.comp (a : C(D, E))) (g := f) (y := b) (y' := b)
    a (Homeomorph.refl B) (fun _ => rfl) rfl
  let V := precompRightHomotopy f a.toHomotopyEquiv b
  refine ⟨((ContinuousMap.Homotopy.refl
    (Q.symm : C(HomotopyFiber f b, HomotopyFiber (f.comp (a : C(D, E))) b))).comp V).cast
      ?_ rfl⟩
  apply ContinuousMap.ext
  intro z
  exact (congrArg
    (fun k : C(HomotopyFiber (f.comp (a : C(D, E))) b, HomotopyFiber f b) =>
      Q.symm (k ((precompHomotopyEquiv f a.toHomotopyEquiv b).symm z)))
        (precompHomotopyEquiv_toFun_homeomorph f a b)).trans (Q.symm_apply_apply _)

end

end ContinuousMap.HomotopyFiber
