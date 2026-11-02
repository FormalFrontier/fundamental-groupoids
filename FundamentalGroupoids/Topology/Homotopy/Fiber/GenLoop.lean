/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map

/-!
# Generalized loops in ordinary homotopy fibers

Generalized loops commute with the retained-point, compact-open-path model of
ordinary homotopy fibers. The forward map evaluates the point loop at the cube
parameter and transposes the entire path of loops. The inverse retains the whole
point loop and transposes the whole family of retained paths back.

The continuous maps, their cube-boundary conditions and their path endpoints are
constructed directly. Only the interval and cube evaluation APIs are used; there
are no local compactness or separation assumptions on the ambient spaces.

The homeomorphism `genLoopHomeomorph` preserves the specified constant points.
The point and whole-path application lemmas characterize both directions.

## References

* The ordinary homotopy-fiber coordinate and continuity API in
  `FundamentalGroupoids.Topology.Homotopy.Fiber`.
* Mathlib's generalized-loop subtype, joint evaluation and compact-open currying.
* The based postcomposition action in
  `FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map`.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

universe uN uE uB

variable {N : Type uN} {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]
variable (f : C(E, B)) {e₀ : E} {b : B} (h : f e₀ = b)

/-- The whole path obtained by evaluating a path of generalized loops at one
cube parameter, continuously in both the fiber datum and cube parameter. -/
def genLoopForwardPath :
    C(HomotopyFiber
        (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
          C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const × (N → I), C(I, B)) where
  toFun zs := ⟨fun t => path zs.1 t zs.2,
    (path zs.1).continuous.eval continuous_const⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((path.continuous.comp continuous_fst.fst).eval continuous_snd).eval
      continuous_fst.snd

/-- Evaluation of the transposed whole path. -/
@[simp]
theorem genLoopForwardPath_apply
    (z : HomotopyFiber
      (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
        C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const)
    (s : N → I) (t : I) : genLoopForwardPath f h (z, s) t = path z t s :=
  rfl

/-- Joint evaluation into the original homotopy fiber, retaining both coordinates. -/
def genLoopForwardValue :
    C(HomotopyFiber
        (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
          C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const × (N → I),
      HomotopyFiber f b) where
  toFun zs := mk (point zs.1 zs.2) (genLoopForwardPath f h zs)
    (by
      change path zs.1 0 zs.2 = b
      rw [path_zero]
      rfl)
    (by
      change path zs.1 1 zs.2 = f (point zs.1 zs.2)
      rw [path_one]
      rfl)
  continuous_toFun := by
    apply continuous_iff.2
    exact ⟨(point.continuous.comp continuous_fst).eval continuous_snd,
      (genLoopForwardPath f h).continuous⟩

/-- The retained point of joint forward evaluation. -/
@[simp]
theorem point_genLoopForwardValue
    (zs : HomotopyFiber
      (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
        C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const × (N → I)) :
    point (genLoopForwardValue f h zs) = point zs.1 zs.2 :=
  rfl

/-- The whole retained path of joint forward evaluation. -/
@[simp]
theorem path_genLoopForwardValue
    (zs : HomotopyFiber
      (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
        C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const × (N → I)) :
    path (genLoopForwardValue f h zs) = genLoopForwardPath f h zs :=
  rfl

/-- Evaluate a fiber of based postcomposition at every cube point, keeping the
point value and the entire transposed path in the original homotopy fiber. -/
def genLoopForward :
    C(HomotopyFiber
        (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
          C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const,
      GenLoop N (HomotopyFiber f b) (const e₀ h)) where
  toFun z := ⟨⟨fun s => genLoopForwardValue f h (z, s),
    (genLoopForwardValue f h).continuous.comp
      (continuous_const.prodMk continuous_id)⟩, by
    intro s hs
    apply ext
    · exact GenLoop.boundary (point z) s hs
    · apply ContinuousMap.ext
      intro t
      exact GenLoop.boundary (path z t) s hs⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (genLoopForwardValue f h).continuous

/-- The retained point after forward transposition. -/
@[simp]
theorem point_genLoopForward
    (z : HomotopyFiber
      (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
        C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const)
    (s : N → I) : point (genLoopForward f h z s) = point z s :=
  rfl

/-- The entire retained path after forward transposition. -/
@[simp]
theorem path_genLoopForward
    (z : HomotopyFiber
      (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
        C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const)
    (s : N → I) : path (genLoopForward f h z s) = genLoopForwardPath f h (z, s) :=
  rfl

/-- Every time value of the retained path after forward transposition. -/
@[simp]
theorem path_genLoopForward_apply
    (z : HomotopyFiber
      (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
        C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const)
    (s : N → I) (t : I) : path (genLoopForward f h z s) t = path z t s :=
  rfl

/-- The whole point loop of a generalized loop in the homotopy fiber. -/
def genLoopInversePoint :
    C(GenLoop N (HomotopyFiber f b) (const e₀ h), GenLoop N E e₀) where
  toFun ell := ⟨⟨fun s => point (ell s),
    point.continuous.comp ell.1.continuous⟩, by
    intro s hs
    change point (ell s) = e₀
    rw [GenLoop.boundary ell s hs]
    rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact point.continuous.comp (continuous_fst.eval continuous_snd)

/-- Evaluation of the point loop retained by inverse transposition. -/
@[simp]
theorem genLoopInversePoint_apply
    (ell : GenLoop N (HomotopyFiber f b) (const e₀ h)) (s : N → I) :
    genLoopInversePoint f h ell s = point (ell s) :=
  rfl

/-- At each time, the whole loop of retained path values, jointly continuous in
the given loop and time. -/
def genLoopInversePathValue :
    C(GenLoop N (HomotopyFiber f b) (const e₀ h) × I, GenLoop N B b) where
  toFun lt := ⟨⟨fun s => path (lt.1 s) lt.2,
    (path.continuous.comp lt.1.1.continuous).eval continuous_const⟩, by
    intro s hs
    change path (lt.1 s) lt.2 = b
    rw [GenLoop.boundary lt.1 s hs]
    rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (path.continuous.comp (continuous_fst.fst.eval continuous_snd)).eval
      continuous_fst.snd

/-- Every cube value of joint inverse-path evaluation. -/
@[simp]
theorem genLoopInversePathValue_apply
    (lt : GenLoop N (HomotopyFiber f b) (const e₀ h) × I) (s : N → I) :
    genLoopInversePathValue f h lt s = path (lt.1 s) lt.2 :=
  rfl

/-- The entire path of generalized loops obtained by transposing all the retained
paths, continuously in the original generalized loop. -/
def genLoopInversePath :
    C(GenLoop N (HomotopyFiber f b) (const e₀ h), C(I, GenLoop N B b)) where
  toFun ell := ⟨fun t => genLoopInversePathValue f h (ell, t),
    (genLoopInversePathValue f h).continuous.comp
      (continuous_const.prodMk continuous_id)⟩
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (genLoopInversePathValue f h).continuous

/-- Every cube and time value in the whole inverse path. -/
@[simp]
theorem genLoopInversePath_apply
    (ell : GenLoop N (HomotopyFiber f b) (const e₀ h)) (t : I) (s : N → I) :
    genLoopInversePath f h ell t s = path (ell s) t :=
  rfl

/-- Retain the whole point loop and the entire path of loops in the original
homotopy fiber of based postcomposition. -/
def genLoopInverse :
    C(GenLoop N (HomotopyFiber f b) (const e₀ h),
      HomotopyFiber
        (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
          C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const) where
  toFun ell := mk (genLoopInversePoint f h ell) (genLoopInversePath f h ell)
    (by
      apply GenLoop.ext
      intro s
      exact path_zero (ell s))
    (by
      apply GenLoop.ext
      intro s
      exact path_one (ell s))
  continuous_toFun := by
    apply continuous_iff.2
    exact ⟨(genLoopInversePoint f h).continuous, (genLoopInversePath f h).continuous⟩

/-- The entire retained point loop after inverse transposition. -/
@[simp]
theorem point_genLoopInverse
    (ell : GenLoop N (HomotopyFiber f b) (const e₀ h)) :
    point (genLoopInverse f h ell) = genLoopInversePoint f h ell :=
  rfl

/-- The entire retained path of loops after inverse transposition. -/
@[simp]
theorem path_genLoopInverse
    (ell : GenLoop N (HomotopyFiber f b) (const e₀ h)) :
    path (genLoopInverse f h ell) = genLoopInversePath f h ell :=
  rfl

/-- Evaluation of the point retained by inverse transposition. -/
@[simp]
theorem point_genLoopInverse_apply
    (ell : GenLoop N (HomotopyFiber f b) (const e₀ h)) (s : N → I) :
    point (genLoopInverse f h ell) s = point (ell s) :=
  rfl

/-- Every time and cube value of the path retained by inverse transposition. -/
@[simp]
theorem path_genLoopInverse_apply
    (ell : GenLoop N (HomotopyFiber f b) (const e₀ h)) (t : I) (s : N → I) :
    path (genLoopInverse f h ell) t s = path (ell s) t :=
  rfl

private theorem genLoop_leftInverse :
    Function.LeftInverse (genLoopInverse (N := N) f h) (genLoopForward f h) := by
  intro z
  apply ext
  · apply GenLoop.ext
    intro s
    rw [point_genLoopInverse_apply, point_genLoopForward]
  · apply ContinuousMap.ext
    intro t
    apply GenLoop.ext
    intro s
    rw [path_genLoopInverse_apply, path_genLoopForward_apply]

private theorem genLoop_rightInverse :
    Function.RightInverse (genLoopInverse (N := N) f h) (genLoopForward f h) := by
  intro ell
  apply GenLoop.ext
  intro s
  apply ext
  · rw [point_genLoopForward, point_genLoopInverse_apply]
  · apply ContinuousMap.ext
    intro t
    rw [path_genLoopForward_apply, path_genLoopInverse_apply]

/-- The forward comparison preserves the specified constant point and its whole
constant path. -/
@[simp]
theorem genLoopForward_const :
    genLoopForward (N := N) f h
        (const (GenLoop.const : GenLoop N E e₀) (GenLoop.map_const f h)) =
      (GenLoop.const : GenLoop N (HomotopyFiber f b) (const e₀ h)) := by
  apply GenLoop.ext
  intro s
  simp only [GenLoop.const_apply]
  apply ext
  · simp only [point_genLoopForward, point_const, GenLoop.const_apply]
  · apply ContinuousMap.ext
    intro t
    simp only [path_genLoopForward_apply, path_const, ContinuousMap.const_apply,
      GenLoop.const_apply]

/-- The inverse comparison preserves the specified constant loop and the source
constant-path point. -/
@[simp]
theorem genLoopInverse_const :
    genLoopInverse (N := N) f h
        (GenLoop.const : GenLoop N (HomotopyFiber f b) (const e₀ h)) =
      const (GenLoop.const : GenLoop N E e₀) (GenLoop.map_const f h) := by
  apply ext
  · apply GenLoop.ext
    intro s
    simp only [point_genLoopInverse_apply, GenLoop.const_apply, point_const]
  · apply ContinuousMap.ext
    intro t
    apply GenLoop.ext
    intro s
    simp only [path_genLoopInverse_apply, GenLoop.const_apply, path_const,
      ContinuousMap.const_apply]

/-- Generalized loops commute with ordinary homotopy fibers by transposing the
whole retained path and retaining the point coordinate. -/
@[no_expose]
def genLoopHomeomorph :
    HomotopyFiber
        (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
          C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const ≃ₜ
      GenLoop N (HomotopyFiber f b) (const e₀ h) where
  toFun := genLoopForward f h
  invFun := genLoopInverse f h
  left_inv := genLoop_leftInverse f h
  right_inv := genLoop_rightInverse f h
  continuous_toFun := (genLoopForward f h).continuous
  continuous_invFun := (genLoopInverse f h).continuous

private theorem genLoopHomeomorph_apply_eq
    (z : HomotopyFiber
      (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
        C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const) :
    genLoopHomeomorph f h z = genLoopForward f h z :=
  rfl

/-- The forward homeomorphism is the constructed continuous forward map. -/
@[simp]
theorem genLoopHomeomorph_apply
    (z : HomotopyFiber
      (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
        C(GenLoop N E e₀, GenLoop N B b)) GenLoop.const) :
    genLoopHomeomorph f h z = genLoopForward f h z :=
  genLoopHomeomorph_apply_eq f h z

private theorem genLoopHomeomorph_symm_apply_eq
    (ell : GenLoop N (HomotopyFiber f b) (const e₀ h)) :
    (genLoopHomeomorph f h).symm ell = genLoopInverse f h ell :=
  rfl

/-- The inverse homeomorphism is the constructed continuous inverse map. -/
@[simp]
theorem genLoopHomeomorph_symm_apply
    (ell : GenLoop N (HomotopyFiber f b) (const e₀ h)) :
    (genLoopHomeomorph f h).symm ell = genLoopInverse f h ell :=
  genLoopHomeomorph_symm_apply_eq f h ell

/-- Preservation of the specified constant-path point and its whole constant path. -/
theorem genLoopHomeomorph_const :
    genLoopHomeomorph (N := N) f h
        (const (GenLoop.const : GenLoop N E e₀) (GenLoop.map_const f h)) =
      (GenLoop.const : GenLoop N (HomotopyFiber f b) (const e₀ h)) :=
  genLoopForward_const f h

/-- The inverse sends the constant loop to the specified source constant-path point. -/
theorem genLoopHomeomorph_symm_const :
    (genLoopHomeomorph (N := N) f h).symm
        (GenLoop.const : GenLoop N (HomotopyFiber f b) (const e₀ h)) =
      const (GenLoop.const : GenLoop N E e₀) (GenLoop.map_const f h) :=
  genLoopInverse_const f h

section Naturality

universe uE' uB'

variable {E' : Type uE'} {B' : Type uB'}
variable [TopologicalSpace E'] [TopologicalSpace B']

/-- Transposition commutes with a continuous commutative square preserving the specified
points. Both sides are bundled continuous maps; at cube parameter `s` they retain point
`a (point z s)` and the whole path `t ↦ c (path z t s)`. The vertical maps use the
homotopy-fiber square map and based postcomposition of generalized loops. The target
loop is based at the specified constant `const e₀' h'`. -/
theorem genLoopHomeomorph_naturality
    (f : C(E, B)) (f' : C(E', B'))
    {e₀ : E} {b : B} {e₀' : E'} {b' : B'}
    (h : f e₀ = b) (h' : f' e₀' = b')
    (a : C(E, E')) (c : C(B, B'))
    (w : ∀ e, f' (a e) = c (f e))
    (he : a e₀ = e₀') (hb : c b = b') :
    let g : C(GenLoop N E e₀, GenLoop N B b) :=
      ⟨GenLoop.map f h, GenLoop.continuous_map f h⟩
    let g' : C(GenLoop N E' e₀', GenLoop N B' b') :=
      ⟨GenLoop.map f' h', GenLoop.continuous_map f' h'⟩
    let A : C(GenLoop N E e₀, GenLoop N E' e₀') :=
      ⟨GenLoop.map a he, GenLoop.continuous_map a he⟩
    let D : C(GenLoop N B b, GenLoop N B' b') :=
      ⟨GenLoop.map c hb, GenLoop.continuous_map c hb⟩
    let W : ∀ p, g' (A p) = D (g p) := by
      intro p
      apply GenLoop.ext
      intro s
      change GenLoop.map f' h' (GenLoop.map a he p) s =
        GenLoop.map c hb (GenLoop.map f h p) s
      simpa only [GenLoop.map_apply] using w (p s)
    let H : C(HomotopyFiber f b, HomotopyFiber f' b') :=
      map a c w hb
    let κ : H (const e₀ h) = const e₀' h' := by
      exact map_const_of_point_eq a c w hb e₀ e₀' h h' he
    let U : C(HomotopyFiber g GenLoop.const,
        HomotopyFiber g' GenLoop.const) :=
      map A D W (GenLoop.map_const c hb)
    let L : C(GenLoop N (HomotopyFiber f b) (const e₀ h),
        GenLoop N (HomotopyFiber f' b') (const e₀' h')) :=
      ⟨GenLoop.map H κ, GenLoop.continuous_map H κ⟩
    (genLoopHomeomorph (N := N) f' h' :
        C(HomotopyFiber g' GenLoop.const,
          GenLoop N (HomotopyFiber f' b') (const e₀' h'))).comp U =
      L.comp (genLoopHomeomorph (N := N) f h :
        C(HomotopyFiber g GenLoop.const,
          GenLoop N (HomotopyFiber f b) (const e₀ h))) := by
  dsimp only
  apply ContinuousMap.ext
  intro z
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_apply, genLoopHomeomorph_apply]
  apply GenLoop.ext
  intro s
  apply ContinuousMap.HomotopyFiber.ext
  · simp only [point_genLoopForward, point_map, ContinuousMap.coe_mk, GenLoop.map_apply]
  · apply ContinuousMap.ext
    intro t
    simp only [path_genLoopForward_apply, path_map, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, GenLoop.map_apply]

end Naturality

end ContinuousMap.HomotopyFiber
