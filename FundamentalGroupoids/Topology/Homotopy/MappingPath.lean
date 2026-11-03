/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.PathSpace
public import FundamentalGroupoids.Topology.Homotopy.Fiber
public import Mathlib.Data.Set.Prod
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Ordinary mapping-path factorization

For a continuous map `f : C(E, B)`, `MappingPathSpace f` is the ordinary pullback
of `f` and initial evaluation on `C(I, B)`. It retains both the source point and
the entire path. The constant-path inclusion and the source projection form
`MappingPathSpace.homotopyEquiv`; the homotopy shortens the path by
`γ(t) ↦ γ((1 - s) * t)` and fixes every constant-path inclusion point.

The shortening construction follows J. P. May, *A Concise Course in Algebraic
Topology*, Chapter 7, §3, p. 50. Here all topologies are the ordinary product,
subspace and compact-open topologies. Unlike May's compactly generated setting,
no CGWH replacement or kification is made or asserted.

`MappingPathSpace.endpointFiberHomeomorph` identifies the strict endpoint fiber
with the original `ContinuousMap.HomotopyFiber`, whose paths run from `b` to
`f e`, by reversing the whole path and retaining `e`. The constant laws require
a separately specified point `e` and equality `f e = b`; an arbitrary endpoint
need not have any fiber points. Both comparisons are natural in continuous
commutative squares. No fibration or lifting assertion is needed here.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap

universe uE uB uE' uB' uT

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]

/-- The ordinary pullback of `f` and initial evaluation on compact-open paths. -/
def MappingPathSpace (f : C(E, B)) :=
  Function.Pullback f (fun p : C(I, B) => p 0)

namespace MappingPathSpace

variable {f : C(E, B)}

/-- The original product/subspace topology of the stock function pullback. -/
instance instTopologicalSpace : TopologicalSpace (MappingPathSpace f) :=
  inferInstanceAs
    (TopologicalSpace (Function.Pullback f (fun p : C(I, B) => p 0)))

/-- The retained source coordinate. -/
def point : C(MappingPathSpace f, E) where
  toFun := fun z : MappingPathSpace f => z.1.1
  continuous_toFun :=
    (continuous_fst : Continuous (Prod.fst : E × C(I, B) → E)).comp
      (continuous_subtype_val :
        Continuous (Subtype.val : MappingPathSpace f → E × C(I, B)))

/-- The entire retained compact-open path. -/
def path : C(MappingPathSpace f, C(I, B)) where
  toFun := fun z : MappingPathSpace f => z.1.2
  continuous_toFun :=
    (continuous_snd : Continuous (Prod.snd : E × C(I, B) → C(I, B))).comp
      (continuous_subtype_val :
        Continuous (Subtype.val : MappingPathSpace f → E × C(I, B)))

/-- Construct a mapping path using its initial endpoint equation. -/
def mk (e : E) (p : C(I, B)) (h : p 0 = f e) : MappingPathSpace f :=
  ⟨(e, p), h.symm⟩

@[simp]
theorem point_mk (e : E) (p : C(I, B)) (h : p 0 = f e) :
    point (mk e p h) = e := by rfl

@[simp]
theorem path_mk (e : E) (p : C(I, B)) (h : p 0 = f e) :
    path (mk e p h) = p := by rfl

@[simp]
theorem mk_point_path (z : MappingPathSpace f) :
    mk (point z) (path z) z.2.symm = z := by rfl

@[ext]
theorem ext {z w : MappingPathSpace f}
    (he : point z = point w) (hp : path z = path w) : z = w :=
  Subtype.ext (Prod.ext he hp)

@[simp]
theorem path_zero (z : MappingPathSpace f) : path z 0 = f (point z) :=
  z.2.symm

/-- A family is continuous exactly when both original coordinates are continuous. -/
theorem continuous_iff {T : Type uT} [TopologicalSpace T]
    {k : T → MappingPathSpace f} :
    Continuous k ↔ Continuous (fun t => point (k t)) ∧
      Continuous (fun t => path (k t)) := by
  constructor
  · intro h
    exact ⟨point.continuous.comp h, path.continuous.comp h⟩
  · rintro ⟨he, hp⟩
    exact continuous_induced_rng.2 (he.prodMk hp)

/-- Evaluate the whole retained path at a specified time. -/
def eval (t : I) : C(MappingPathSpace f, B) where
  toFun z := path z t
  continuous_toFun := (continuous_eval_const t).comp path.continuous

@[simp]
theorem eval_apply (t : I) (z : MappingPathSpace f) : eval t z = path z t := by rfl

theorem eval_zero (z : MappingPathSpace f) : eval 0 z = f (point z) := path_zero z

/-- The endpoint opposite to the prescribed initial endpoint. -/
def endpoint : C(MappingPathSpace f, B) := eval 1

@[simp]
theorem endpoint_apply (z : MappingPathSpace f) : endpoint z = path z 1 := by rfl

/-- The canonical constant-path inclusion. -/
def inclusion (f : C(E, B)) : C(E, MappingPathSpace f) where
  toFun e := mk e (ContinuousMap.const I (f e)) rfl
  continuous_toFun := continuous_iff.mpr
    ⟨continuous_id,
      (ContinuousMap.const' : C(B, C(I, B))).continuous.comp f.continuous⟩

@[simp]
theorem point_inclusion (f : C(E, B)) (e : E) : point (inclusion f e) = e := by rfl

@[simp]
theorem path_inclusion (f : C(E, B)) (e : E) :
    path (inclusion f e) = ContinuousMap.const I (f e) := by rfl

theorem eval_inclusion (f : C(E, B)) (e : E) (t : I) :
    eval t (inclusion f e) = f e := by rfl

@[simp]
theorem point_comp_inclusion (f : C(E, B)) :
    point.comp (inclusion f) = ContinuousMap.id E := by rfl

@[simp]
theorem endpoint_comp_inclusion (f : C(E, B)) :
    endpoint.comp (inclusion f) = f := by rfl

/-- Initial evaluation on the ambient ordinary compact-open path space. -/
def initialEvaluation : C(C(I, B), B) where
  toFun p := p 0
  continuous_toFun := continuous_eval_const 0

@[simp]
theorem initialEvaluation_apply (p : C(I, B)) : initialEvaluation p = p 0 := by rfl

/-- The reverse of the canonical interval prefix homotopy shortens from identity to zero. -/
def intervalShortening :
    (ContinuousMap.id I).Homotopy (ContinuousMap.const I (0 : I)) :=
  unitInterval.initialSegmentHomotopy.symm

@[simp]
theorem intervalShortening_apply (s t : I) :
    intervalShortening (s, t) = Set.Icc.convexComb t 0 s := by
  calc
    intervalShortening (s, t) = unitInterval.symm s * t := rfl
    _ = Set.Icc.convexComb t 0 s := by
      apply Subtype.ext
      simp [Set.Icc.coe_convexComb, unitInterval.coe_symm_eq]

@[simp]
theorem intervalShortening_zero (s : I) : intervalShortening (s, 0) = 0 := by
  rw [intervalShortening_apply]
  exact Set.Icc.convexComb_eq 0 s

/-- The full shortened parameter is `(1 - s) * t`. -/
theorem intervalShortening_formula (s t : I) :
    intervalShortening (s, t) = unitInterval.symm s * t := by rfl

/-- Joint ambient shortening is the actual precomposition homotopy, not separate
fixed-start contractions. Its final map is the constant-path family after initial evaluation. -/
def ambientShortening :
    (ContinuousMap.id C(I, B)).Homotopy
      ((ContinuousMap.const' : C(B, C(I, B))).comp initialEvaluation) :=
  (ContinuousMap.initialSegmentHomotopy (B := B)).symm.cast
    (by
      apply ContinuousMap.ext
      intro p
      apply ContinuousMap.ext
      intro t
      rfl)
    (by
      apply ContinuousMap.ext
      intro p
      apply ContinuousMap.ext
      intro t
      rfl)

@[simp]
theorem ambientShortening_apply (s : I) (p : C(I, B)) (t : I) :
    ambientShortening (s, p) t = p (intervalShortening (s, t)) := by rfl

/-- The full path formula uses the standard shortened parameter. -/
theorem ambientShortening_apply_mul (s : I) (p : C(I, B)) (t : I) :
    ambientShortening (s, p) t = p (unitInterval.symm s * t) := by
  rw [ambientShortening_apply, intervalShortening_formula]

theorem ambientShortening_eval_zero (s : I) (p : C(I, B)) :
    ambientShortening (s, p) 0 = p 0 := by
  rw [ambientShortening_apply, intervalShortening_zero]

@[simp]
theorem ambientShortening_const (s : I) (b : B) :
    ambientShortening (s, ContinuousMap.const I b) = ContinuousMap.const I b := by
  apply ContinuousMap.ext
  intro t
  rfl

/-- The actual ordinary mapping-path deformation, relative to all constant-path points.
It keeps the retained source coordinate fixed and restricts the ambient deformation
using its initial-evaluation preservation. -/
def deformation (f : C(E, B)) :
    (ContinuousMap.id (MappingPathSpace f)).HomotopyRel
      ((inclusion f).comp (point (f := f))) (Set.range (inclusion f)) where
  toFun := fun v : I × MappingPathSpace f =>
    mk (f := f) (point (f := f) v.2)
      (ambientShortening (B := B) (v.1, path (f := f) v.2))
      ((ambientShortening_eval_zero v.1 (path (f := f) v.2)).trans
        (path_zero (f := f) v.2))
  continuous_toFun := (continuous_iff (f := f)).mpr
    ⟨by
      simpa only [point_mk] using
        (point (f := f)).continuous.comp'
          (continuous_snd : Continuous (Prod.snd : I × MappingPathSpace f → MappingPathSpace f)),
      by
        simpa only [path_mk] using
          (ambientShortening (B := B)).continuous.comp'
            ((continuous_fst : Continuous (Prod.fst : I × MappingPathSpace f → I)).prodMk
              ((path (f := f)).continuous.comp'
                (continuous_snd :
                  Continuous (Prod.snd : I × MappingPathSpace f → MappingPathSpace f))))⟩
  map_zero_left z := by
    apply ext (f := f)
    · rfl
    · exact (ambientShortening (B := B)).apply_zero (path (f := f) z)
  map_one_left z := by
    apply ext (f := f)
    · rfl
    · exact ((ambientShortening (B := B)).apply_one (path (f := f) z)).trans
        (congrArg (ContinuousMap.const I) (path_zero (f := f) z))
  prop' := fun (s : I) (z : MappingPathSpace f)
      (hz : z ∈ Set.range (inclusion f)) => by
    rcases hz with ⟨e, rfl⟩
    apply ext (f := f)
    · rfl
    · exact ambientShortening_const s (f e)

theorem deformation_zero (f : C(E, B)) (z : MappingPathSpace f) :
    deformation f (0, z) = z :=
  (deformation f).toHomotopy.apply_zero z

theorem deformation_one (f : C(E, B)) (z : MappingPathSpace f) :
    deformation f (1, z) = inclusion f (point z) :=
  (deformation f).toHomotopy.apply_one z

@[simp]
theorem point_deformation (f : C(E, B)) (s : I) (z : MappingPathSpace f) :
    point (deformation f (s, z)) = point z := by rfl

@[simp]
theorem path_deformation (f : C(E, B)) (s : I) (z : MappingPathSpace f) :
    path (deformation f (s, z)) = ambientShortening (s, path z) := by rfl

theorem eval_deformation (f : C(E, B)) (s : I) (z : MappingPathSpace f) (t : I) :
    eval t (deformation f (s, z)) = path z (intervalShortening (s, t)) := by rfl

theorem eval_deformation_mul (f : C(E, B)) (s : I) (z : MappingPathSpace f) (t : I) :
    eval t (deformation f (s, z)) = path z (unitInterval.symm s * t) := by
  rw [eval_deformation, intervalShortening_formula]

theorem eval_zero_deformation (f : C(E, B)) (s : I) (z : MappingPathSpace f) :
    eval 0 (deformation f (s, z)) = f (point z) :=
  (eval_zero (f := f) (deformation f (s, z))).trans
    (congrArg f (point_deformation f s z))

@[simp]
theorem deformation_inclusion (f : C(E, B)) (s : I) (e : E) :
    deformation f (s, inclusion f e) = inclusion f e :=
  (deformation f).eq_fst s ⟨e, rfl⟩

/-- The canonical homotopy equivalence from the ordinary mapping-path space to its
source. Its inverse is the constant-path inclusion; the left inverse homotopy is the
reverse of `deformation`. -/
def homotopyEquiv (f : C(E, B)) : MappingPathSpace f ≃ₕ E where
  toFun := point
  invFun := inclusion f
  left_inv := ⟨(deformation f).toHomotopy.symm⟩
  right_inv := Homotopic.refl (ContinuousMap.id E)

@[simp]
theorem homotopyEquiv_toFun (f : C(E, B)) :
    (homotopyEquiv f).toFun = point := by rfl

@[simp]
theorem homotopyEquiv_invFun (f : C(E, B)) :
    (homotopyEquiv f).invFun = inclusion f := by rfl

theorem homotopyEquiv_apply (f : C(E, B)) (z : MappingPathSpace f) :
    homotopyEquiv f z = point z := by rfl

/-- The strict endpoint fiber, with its original nested-subspace topology. -/
def EndpointFiber (f : C(E, B)) (b : B) :=
  {z : MappingPathSpace f // endpoint z = b}

instance instTopologicalSpaceEndpointFiber (f : C(E, B)) (b : B) :
    TopologicalSpace (EndpointFiber f b) :=
  inferInstanceAs (TopologicalSpace {z : MappingPathSpace f // endpoint z = b})

/-- A separately specified source point over `b` gives a constant strict-fiber point. -/
def inclusionAt (f : C(E, B)) (b : B) (e : E) (h : f e = b) : EndpointFiber f b :=
  ⟨inclusion f e, h⟩

/-- The stock compact-open homeomorphism induced by interval reversal. -/
def pathReversal : C(I, B) ≃ₜ C(I, B) :=
  Homeomorph.arrowCongr unitInterval.symmHomeomorph (Homeomorph.refl B)

@[simp]
theorem pathReversal_apply (p : C(I, B)) (t : I) :
    pathReversal p t = p (unitInterval.symm t) := by rfl

@[simp]
theorem pathReversal_symm_apply (p : C(I, B)) (t : I) :
    pathReversal.symm p t = p (unitInterval.symm t) := by rfl

/-- The continuous forward comparison to the original oppositely directed homotopy fiber.
-/
def toHomotopyFiber (f : C(E, B)) (b : B) :
    C(EndpointFiber f b, HomotopyFiber f b) where
  toFun z := HomotopyFiber.mk (point z.1) (pathReversal (path z.1))
    (by simpa only [pathReversal_apply, unitInterval.symm_zero, endpoint_apply] using z.2)
    (by simpa only [pathReversal_apply, unitInterval.symm_one] using path_zero z.1)
  continuous_toFun := HomotopyFiber.continuous_iff.mpr
    ⟨point.continuous.comp continuous_subtype_val,
      pathReversal.continuous.comp (path.continuous.comp continuous_subtype_val)⟩

/-- The continuous backward comparison, retaining the original source point.
-/
def fromHomotopyFiber (f : C(E, B)) (b : B) :
    C(HomotopyFiber f b, EndpointFiber f b) where
  toFun z := ⟨mk (HomotopyFiber.point z) (pathReversal.symm (HomotopyFiber.path z))
    (by simpa only [pathReversal_symm_apply, unitInterval.symm_zero] using
      HomotopyFiber.path_one z),
    by simpa only [endpoint_apply, path_mk, pathReversal_symm_apply,
      unitInterval.symm_one] using HomotopyFiber.path_zero z⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_iff.mpr
      ⟨HomotopyFiber.point.continuous,
        pathReversal.symm.continuous.comp HomotopyFiber.path.continuous⟩

@[simp]
theorem point_toHomotopyFiber (f : C(E, B)) (b : B) (z : EndpointFiber f b) :
    HomotopyFiber.point (toHomotopyFiber f b z) = point z.1 := by rfl

@[simp]
theorem path_toHomotopyFiber (f : C(E, B)) (b : B) (z : EndpointFiber f b) :
    HomotopyFiber.path (toHomotopyFiber f b z) = pathReversal (path z.1) := by rfl

theorem eval_toHomotopyFiber (f : C(E, B)) (b : B) (z : EndpointFiber f b) (t : I) :
    HomotopyFiber.eval t (toHomotopyFiber f b z) = path z.1 (unitInterval.symm t) := by rfl

@[simp]
theorem point_fromHomotopyFiber (f : C(E, B)) (b : B) (z : HomotopyFiber f b) :
    point (fromHomotopyFiber f b z).1 = HomotopyFiber.point z := by rfl

@[simp]
theorem path_fromHomotopyFiber (f : C(E, B)) (b : B) (z : HomotopyFiber f b) :
    path (fromHomotopyFiber f b z).1 = pathReversal.symm (HomotopyFiber.path z) := by rfl

theorem eval_fromHomotopyFiber (f : C(E, B)) (b : B)
    (z : HomotopyFiber f b) (t : I) :
    eval t (fromHomotopyFiber f b z).1 = HomotopyFiber.path z (unitInterval.symm t) := by rfl

/-- Reversing the entire path in both directions recovers the original strict-fiber point. -/
@[simp]
theorem fromHomotopyFiber_toHomotopyFiber (f : C(E, B)) (b : B)
    (z : EndpointFiber f b) :
    fromHomotopyFiber f b (toHomotopyFiber f b z) = z := by
  apply Subtype.ext
  apply ext (f := f)
  · rfl
  · exact (pathReversal (B := B)).symm_apply_apply (path z.1)

/-- Reversing the entire path in both directions recovers the original homotopy-fiber point. -/
@[simp]
theorem toHomotopyFiber_fromHomotopyFiber (f : C(E, B)) (b : B)
    (z : HomotopyFiber f b) :
    toHomotopyFiber f b (fromHomotopyFiber f b z) = z := by
  apply HomotopyFiber.ext
  · rfl
  · exact (pathReversal (B := B)).apply_symm_apply (HomotopyFiber.path z)

/-- The strict endpoint fiber is homeomorphic to the original homotopy fiber.
Both maps retain the source point and reverse the whole compact-open path. -/
def endpointFiberHomeomorph (f : C(E, B)) (b : B) :
    EndpointFiber f b ≃ₜ HomotopyFiber f b where
  toEquiv :=
    { toFun := toHomotopyFiber f b
      invFun := fromHomotopyFiber f b
      left_inv := fromHomotopyFiber_toHomotopyFiber f b
      right_inv := toHomotopyFiber_fromHomotopyFiber f b }
  continuous_toFun := (toHomotopyFiber f b).continuous
  continuous_invFun := (fromHomotopyFiber f b).continuous

@[simp]
theorem endpointFiberHomeomorph_toContinuousMap (f : C(E, B)) (b : B) :
    (endpointFiberHomeomorph f b : C(EndpointFiber f b, HomotopyFiber f b)) =
      toHomotopyFiber f b := by rfl

@[simp]
theorem endpointFiberHomeomorph_symm_toContinuousMap (f : C(E, B)) (b : B) :
    ((endpointFiberHomeomorph f b).symm : C(HomotopyFiber f b, EndpointFiber f b)) =
      fromHomotopyFiber f b := by rfl

@[simp]
theorem endpointFiberHomeomorph_apply (f : C(E, B)) (b : B) (z : EndpointFiber f b) :
    endpointFiberHomeomorph f b z = toHomotopyFiber f b z := by rfl

@[simp]
theorem endpointFiberHomeomorph_symm_apply (f : C(E, B)) (b : B)
    (z : HomotopyFiber f b) :
    (endpointFiberHomeomorph f b).symm z = fromHomotopyFiber f b z := by rfl

/-- The forward comparison preserves the constant point specified by `e` and `h`. -/
@[simp]
theorem toHomotopyFiber_inclusionAt (f : C(E, B)) (b : B) (e : E) (h : f e = b) :
    toHomotopyFiber f b (inclusionAt f b e h) = HomotopyFiber.const e h := by
  apply HomotopyFiber.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    exact h

/-- The inverse comparison preserves the same specified constant point. -/
@[simp]
theorem fromHomotopyFiber_const (f : C(E, B)) (b : B) (e : E) (h : f e = b) :
    fromHomotopyFiber f b (HomotopyFiber.const e h) = inclusionAt f b e h := by
  apply Subtype.ext
  apply ext (f := f)
  · rfl
  · apply ContinuousMap.ext
    intro t
    exact h.symm

/-- The homeomorphism preserves each separately specified constant fiber point. -/
theorem endpointFiberHomeomorph_inclusionAt (f : C(E, B)) (b : B) (e : E)
    (h : f e = b) :
    endpointFiberHomeomorph f b (inclusionAt f b e h) = HomotopyFiber.const e h :=
  toHomotopyFiber_inclusionAt f b e h

/-- Its inverse preserves the same separately specified constant fiber point. -/
theorem endpointFiberHomeomorph_symm_const (f : C(E, B)) (b : B) (e : E)
    (h : f e = b) :
    (endpointFiberHomeomorph f b).symm (HomotopyFiber.const e h) = inclusionAt f b e h :=
  fromHomotopyFiber_const f b e h

section Squares

variable {E' : Type uE'} {B' : Type uB'}
variable [TopologicalSpace E'] [TopologicalSpace B']
variable {f' : C(E', B')}

/-- The stock pullback map for a continuous commutative square. -/
def map (F : C(E, E')) (G : C(B, B')) (w : ∀ e, f' (F e) = G (f e)) :
    C(MappingPathSpace f, MappingPathSpace f') where
  toFun := Function.mapPullback
    (f₁ := (f : E → B)) (g₁ := fun p : C(I, B) => p 0)
    (f₂ := (f' : E' → B')) (g₂ := fun p : C(I, B') => p 0)
    (F : E → E') (G : B → B') (fun p : C(I, B) => G.comp p)
    (by funext e; exact w e) (by rfl)
  continuous_toFun := continuous_iff.mpr
    ⟨F.continuous.comp point.continuous,
      (ContinuousMap.continuous_postcomp G).comp path.continuous⟩

@[simp]
theorem point_map (F : C(E, E')) (G : C(B, B')) (w : ∀ e, f' (F e) = G (f e))
    (z : MappingPathSpace f) : point (map F G w z) = F (point z) := by rfl

@[simp]
theorem path_map (F : C(E, E')) (G : C(B, B')) (w : ∀ e, f' (F e) = G (f e))
    (z : MappingPathSpace f) : path (map F G w z) = G.comp (path z) := by rfl

theorem endpoint_map (F : C(E, E')) (G : C(B, B')) (w : ∀ e, f' (F e) = G (f e))
    (z : MappingPathSpace f) : endpoint (map F G w z) = G (endpoint z) := by rfl

/-- The induced continuous map of strict endpoint fibers at specified related endpoints. -/
def mapEndpointFiber (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (b : B) (b' : B') (hb : G b = b') :
    C(EndpointFiber f b, EndpointFiber f' b') where
  toFun := fun z : EndpointFiber f b =>
    ⟨map (f := f) (f' := f') F G w z.1,
      (endpoint_map (f := f) (f' := f') F G w z.1).trans
        ((congrArg G z.2).trans hb)⟩
  continuous_toFun :=
    ((map (f := f) (f' := f') F G w).continuous.comp
      (continuous_subtype_val :
        Continuous (Subtype.val : EndpointFiber f b → MappingPathSpace f))).subtype_mk _

@[simp]
theorem coe_mapEndpointFiber (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (b : B) (b' : B') (hb : G b = b')
    (z : EndpointFiber f b) :
    (mapEndpointFiber F G w b b' hb z).1 = map F G w z.1 := by rfl

/-- The complete reversed-path comparison is natural in a commutative square. -/
@[simp]
theorem toHomotopyFiber_mapEndpointFiber (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (b : B) (b' : B') (hb : G b = b')
    (z : EndpointFiber f b) :
    toHomotopyFiber f' b' (mapEndpointFiber F G w b b' hb z) =
      HomotopyFiber.map F G w hb (toHomotopyFiber f b z) := by
  apply HomotopyFiber.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

/-- Naturality as an equality of the entire continuous comparison maps. -/
theorem toHomotopyFiber_comp_mapEndpointFiber (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (b : B) (b' : B') (hb : G b = b') :
    (toHomotopyFiber f' b').comp (mapEndpointFiber F G w b b' hb) =
      (HomotopyFiber.map F G w hb).comp (toHomotopyFiber f b) := by
  apply ContinuousMap.ext
  exact toHomotopyFiber_mapEndpointFiber F G w b b' hb

/-- The inverse comparison is natural on whole homotopy-fiber points as well. -/
@[simp]
theorem fromHomotopyFiber_map (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (b : B) (b' : B') (hb : G b = b')
    (z : HomotopyFiber f b) :
    fromHomotopyFiber f' b' (HomotopyFiber.map F G w hb z) =
      mapEndpointFiber F G w b b' hb (fromHomotopyFiber f b z) := by
  apply Subtype.ext
  apply ext (f := f')
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

/-- Naturality as an equality of the entire continuous inverse maps. -/
theorem fromHomotopyFiber_comp_map (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (b : B) (b' : B') (hb : G b = b') :
    (fromHomotopyFiber f' b').comp (HomotopyFiber.map F G w hb) =
      (mapEndpointFiber F G w b b' hb).comp (fromHomotopyFiber f b) := by
  apply ContinuousMap.ext
  exact fromHomotopyFiber_map F G w b b' hb

/-- A commutative square preserves the actual constant-path inclusion. -/
@[simp]
theorem map_inclusion (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (e : E) :
    map F G w (inclusion f e) = inclusion f' (F e) := by
  apply ext (f := f')
  · rfl
  · apply ContinuousMap.ext
    intro t
    exact (w e).symm

/-- Inclusion naturality as an equality of continuous maps. -/
theorem map_comp_inclusion (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) :
    (map F G w).comp (inclusion f) = (inclusion f').comp F := by
  apply ContinuousMap.ext
  exact map_inclusion F G w

/-- The forward maps of the canonical homotopy equivalences are natural. -/
theorem homotopyEquiv_naturality (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) :
    (homotopyEquiv f').toFun.comp (map F G w) = F.comp (homotopyEquiv f).toFun := by
  apply ContinuousMap.ext
  intro z
  rfl

/-- Their specified inverse maps are natural under the same square. -/
theorem homotopyEquiv_invFun_naturality (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) :
    (map F G w).comp (homotopyEquiv f).invFun = (homotopyEquiv f').invFun.comp F :=
  map_comp_inclusion F G w

/-- The endpoint-fiber homeomorphisms intertwine the square-induced continuous maps. -/
theorem endpointFiberHomeomorph_naturality (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (b : B) (b' : B') (hb : G b = b') :
    (endpointFiberHomeomorph f' b' : C(EndpointFiber f' b', HomotopyFiber f' b')).comp
        (mapEndpointFiber F G w b b' hb) =
      (HomotopyFiber.map F G w hb).comp
        (endpointFiberHomeomorph f b : C(EndpointFiber f b, HomotopyFiber f b)) :=
  toHomotopyFiber_comp_mapEndpointFiber F G w b b' hb

/-- The inverse homeomorphisms intertwine those same square-induced maps. -/
theorem endpointFiberHomeomorph_symm_naturality (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (b : B) (b' : B') (hb : G b = b') :
    ((endpointFiberHomeomorph f' b').symm :
        C(HomotopyFiber f' b', EndpointFiber f' b')).comp (HomotopyFiber.map F G w hb) =
      (mapEndpointFiber F G w b b' hb).comp
        ((endpointFiberHomeomorph f b).symm : C(HomotopyFiber f b, EndpointFiber f b)) :=
  fromHomotopyFiber_comp_map F G w b b' hb

/-- Shortening commutes with every continuous commutative square. -/
theorem map_deformation (F : C(E, E')) (G : C(B, B'))
    (w : ∀ e, f' (F e) = G (f e)) (s : I) (z : MappingPathSpace f) :
    map F G w (deformation f (s, z)) = deformation f' (s, map F G w z) := by
  apply ext (f := f')
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

end Squares

@[simp]
theorem map_id (f : C(E, B)) :
    map (f := f) (f' := f) (ContinuousMap.id E) (ContinuousMap.id B) (fun _ => rfl) =
      ContinuousMap.id (MappingPathSpace f) := by
  apply ContinuousMap.ext
  intro z
  apply ext (f := f)
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

/-- The square-induced mapping-path maps respect composition. -/
theorem map_comp {E'' : Type*} {B'' : Type*} [TopologicalSpace E''] [TopologicalSpace B'']
    {E' : Type uE'} {B' : Type uB'} [TopologicalSpace E'] [TopologicalSpace B']
    {f' : C(E', B')} {f'' : C(E'', B'')}
    (F : C(E, E')) (G : C(B, B')) (w : ∀ e, f' (F e) = G (f e))
    (F' : C(E', E'')) (G' : C(B', B'')) (w' : ∀ e, f'' (F' e) = G' (f' e)) :
    map (F'.comp F) (G'.comp G)
        (fun e => (w' (F e)).trans (congrArg G' (w e))) =
      (map F' G' w').comp (map F G w) := by
  apply ContinuousMap.ext
  intro z
  apply ext (f := f'')
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

@[simp]
theorem mapEndpointFiber_id (f : C(E, B)) (b : B) :
    mapEndpointFiber (f := f) (f' := f) (ContinuousMap.id E) (ContinuousMap.id B)
        (fun _ => rfl) b b rfl = ContinuousMap.id (EndpointFiber f b) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply ext (f := f)
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

/-- The strict-fiber maps respect composition, including the specified endpoint equalities. -/
theorem mapEndpointFiber_comp {E'' : Type*} {B'' : Type*}
    [TopologicalSpace E''] [TopologicalSpace B'']
    {E' : Type uE'} {B' : Type uB'} [TopologicalSpace E'] [TopologicalSpace B']
    {f' : C(E', B')} {f'' : C(E'', B'')}
    (F : C(E, E')) (G : C(B, B')) (w : ∀ e, f' (F e) = G (f e))
    (F' : C(E', E'')) (G' : C(B', B'')) (w' : ∀ e, f'' (F' e) = G' (f' e))
    (b : B) (b' : B') (b'' : B'') (hb : G b = b') (hb' : G' b' = b'') :
    mapEndpointFiber (F'.comp F) (G'.comp G)
        (fun e => (w' (F e)).trans (congrArg G' (w e))) b b''
        ((congrArg G' hb).trans hb') =
      (mapEndpointFiber F' G' w' b' b'' hb').comp
        (mapEndpointFiber F G w b b' hb) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  apply ext (f := f'')
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

end MappingPathSpace
end ContinuousMap
