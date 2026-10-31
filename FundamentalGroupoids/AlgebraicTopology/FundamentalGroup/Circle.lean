/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.ZMultiples

/-!
# Integer coordinates for circle fundamental groups

`AddCircle.fundamentalGroupEquivInt` identifies the fundamental group of `AddCircle T`
at zero with `Multiplicative ℤ` for every nonzero real period `T`. Its normalization
is signed: `AddCircle.loop T n` projects the real segment from zero to `T * n`,
and its integer coordinate is `n`. The endpoint of any lift starting at zero is
`T` times the integer coordinate.

`Circle.fundamentalGroupEquivInt` transports this coordinate to the complex unit
circle, based at one. The homeomorphism `AddCircle.homeomorphCircle hT` respects
the coordinates for every nonzero `T`, including negative periods. It sends the
prescribed one-turn loop to the counterclockwise complex loop, even when its
real lift is decreasing. This does not identify the signed generators for `T`
and `-T`: keeping a quotient loop fixed while reversing the signed period reverses
its integer coordinate.

## Implementation notes

The covering, lifting and simply-connectedness results are supplied by Mathlib.
The only use of `T ≠ 0` in the core construction is the identification of the
period subgroup with `ℤ`. The covering exists also at `T = 0`, when every loop
in the displayed integer family is constant and the fundamental group is trivial.
The commutative equivalence from the opposite period subgroup is used without
inversion, so it does not reverse winding. `Circle.exp` takes radians: its lifted
endpoint is `2 * π * n`, whereas the period-one parametrization has endpoint `n`.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §5,
  pp. 8–9, for the circle calculation, integer loops and lifted-endpoint coordinate.
  The signed-period `AddCircle` formulation generalizes that positive normalization.
* Mathlib's covering and monodromy formalization by Junyan Xu, its `AddCircle`
  and complex-circle formalizations, and its path, contractibility and group
  equivalence APIs provide the constructions reused here.
* The signed-period and complex-circle coordinates were formalized by Formal Frontier
  Agents in [Sphere Topology](https://github.com/FormalFrontier/sphere-topology/blob/4a2b822f12e7f2b4255dfea5363265277defa35e/SphereTopology/Homotopy/Circle.lean).
-/

@[expose] public section

noncomputable section

open scoped unitInterval

private def periodEquiv (T : ℝ) (hT : T ≠ 0) : ℤ ≃+ AddSubgroup.zmultiples T :=
  AddMonoidHom.ofInjective (f := zmultiplesHom ℝ T) (smul_left_injective ℤ hT)

private def fundamentalGroupEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {x : X} {y : Y} (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  let E : CategoryTheory.Equivalence (FundamentalGroupoid X) (FundamentalGroupoid Y) :=
    FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv
  let e₀ : FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
    E.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk x)
  e₀.trans (CategoryTheory.eqToIso (C := FundamentalGroupoid Y)
    (congrArg FundamentalGroupoid.mk h)).conj

private theorem fundamentalGroupEquivOfHomeomorph_apply
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {x : X} {y : Y} (h : e x = y) (γ : FundamentalGroup X x) :
    fundamentalGroupEquivOfHomeomorph e h γ =
      FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h γ := rfl

namespace AddCircle

/-- The signed `n`-turn loop, obtained by projecting the real segment from `0` to `T * n`.
It is defined also for zero period, when it is constant. -/
def loop (T : ℝ) (n : ℤ) : Path (0 : AddCircle T) 0 :=
  ((Path.segment (0 : ℝ) (T * (n : ℝ))).map (AddCircle.continuous_mk' T)).cast
    rfl (by
      symm
      apply (AddCircle.coe_eq_zero_iff T).mpr
      exact ⟨n, by simp [zsmul_eq_mul, mul_comm]⟩)

/-- Evaluation of the signed integer loop on the unit interval. -/
@[simp] theorem loop_apply (T : ℝ) (n : ℤ) (t : I) :
    loop T n t = ((T * (n : ℝ) * (t : ℝ) : ℝ) : AddCircle T) := by
  change (((Path.segment (0 : ℝ) (T * (n : ℝ))) t : ℝ) : AddCircle T) = _
  simp [Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul, mul_comm]

/-- The underlying function of the signed integer loop. -/
theorem coe_loop (T : ℝ) (n : ℤ) :
    (loop T n : I → AddCircle T) = fun t : I ↦ ((T * (n : ℝ) * (t : ℝ) : ℝ) : AddCircle T) := by
  funext t
  exact loop_apply T n t

/-- The zero-turn loop is constant. -/
@[simp] theorem loop_zero (T : ℝ) : loop T 0 = Path.refl 0 := by
  ext t
  simp

/-- At zero period the whole integer loop family is constant. -/
@[simp] theorem loop_zero_period (n : ℤ) : loop 0 n = Path.refl 0 := by
  ext t
  simp

/-- The lift of the signed integer loop starting at zero is its defining real segment.
No nonzero-period assumption is needed for this lifting formula. -/
theorem liftPath_loop (T : ℝ) (n : ℤ) :
    (isCoveringMap_coe T).liftPath (loop T n).toContinuousMap 0 (loop T n).source =
      (Path.segment (0 : ℝ) (T * (n : ℝ))).toContinuousMap := by
  symm
  apply ((isCoveringMap_coe T).eq_liftPath_iff' (loop T n).source).mpr
  constructor
  · ext t
    simp [Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul, mul_comm]
  · exact (Path.segment (0 : ℝ) (T * (n : ℝ))).source

/-- Integer coordinates on the fundamental group of a real additive circle, normalized
by the signed period `T`. This generalizes May's Chapter 1, §5 circle calculation.
The covering equivalence is followed by commutative unop, not by inversion. -/
def fundamentalGroupEquivInt {T : ℝ} (hT : T ≠ 0) :
    FundamentalGroup (AddCircle T) 0 ≃* Multiplicative ℤ :=
  ((isAddQuotientCoveringMap_coe T).fundamentalGroupEquiv
      (x := (0 : AddCircle T)) ⟨(0 : ℝ), rfl⟩).trans
    (MulOpposite.opMulEquiv.symm.trans
      (AddMonoidHom.ofInjective (f := zmultiplesHom ℝ T)
        (smul_left_injective ℤ hT)).symm.toMultiplicative)

private theorem fundamentalGroupEquivInt_eq_iff_liftPath {T : ℝ} (hT : T ≠ 0)
    (γ : Path (0 : AddCircle T) 0) (n : ℤ) :
    fundamentalGroupEquivInt hT (FundamentalGroup.fromPath ⟦γ⟧) = Multiplicative.ofAdd n ↔
      (isCoveringMap_coe T).liftPath γ.toContinuousMap 0 γ.source 1 = T * (n : ℝ) := by
  let hp := isAddQuotientCoveringMap_coe T
  let c := hp.fundamentalGroupToMulOpposite ⟨(0 : ℝ), rfl⟩
    (FundamentalGroup.fromPath ⟦γ⟧)
  have hc : fundamentalGroupEquivInt hT (FundamentalGroup.fromPath ⟦γ⟧) =
      Multiplicative.ofAdd n ↔
      c = MulOpposite.op (Multiplicative.ofAdd (periodEquiv T hT n)) := by
    change Multiplicative.ofAdd ((periodEquiv T hT).symm c.unop.toAdd) =
      Multiplicative.ofAdd n ↔ _
    rw [Multiplicative.ofAdd.injective.eq_iff, (periodEquiv T hT).symm_apply_eq]
    constructor
    · intro h
      exact MulOpposite.unop_injective (Multiplicative.toAdd.injective h)
    · intro h
      exact congrArg (fun z : (Multiplicative (AddSubgroup.zmultiples T))ᵐᵒᵖ ↦
        z.unop.toAdd) h
  rw [hc, IsAddQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff]
  change (n • T) + 0 =
    (isCoveringMap_coe T).liftPath γ.toContinuousMap 0 γ.source 1 ↔ _
  simp only [add_zero, zsmul_eq_mul, mul_comm (n : ℝ) T, eq_comm]

/-- A signed `n`-turn loop has integer coordinate `n`. -/
@[simp↓] theorem fundamentalGroupEquivInt_loop {T : ℝ} (hT : T ≠ 0) (n : ℤ) :
    fundamentalGroupEquivInt hT (FundamentalGroup.fromPath ⟦loop T n⟧) =
      Multiplicative.ofAdd n := by
  apply (fundamentalGroupEquivInt_eq_iff_liftPath hT (loop T n) n).mpr
  rw [liftPath_loop]
  exact (Path.segment (0 : ℝ) (T * (n : ℝ))).target

/-- The inverse calculator constructs the class of the signed integer loop. -/
@[simp] theorem fundamentalGroupEquivInt_symm_apply {T : ℝ} (hT : T ≠ 0) (n : ℤ) :
    (fundamentalGroupEquivInt hT).symm (Multiplicative.ofAdd n) =
      FundamentalGroup.fromPath ⟦loop T n⟧ := by
  exact (fundamentalGroupEquivInt hT).symm_apply_eq.mpr
    (fundamentalGroupEquivInt_loop hT n).symm

/-- Every fundamental-group element is the signed integer loop in its computed coordinate. -/
theorem eq_loop_fundamentalGroupEquivInt {T : ℝ} (hT : T ≠ 0)
    (γ : FundamentalGroup (AddCircle T) 0) :
    γ = FundamentalGroup.fromPath ⟦loop T (fundamentalGroupEquivInt hT γ).toAdd⟧ := by
  exact ((fundamentalGroupEquivInt hT).symm_apply_apply γ).symm.trans
    (fundamentalGroupEquivInt_symm_apply hT _)

/-- The integer-loop normalization uniquely determines the calculator. -/
theorem fundamentalGroupEquivInt_unique {T : ℝ} (hT : T ≠ 0)
    (e : FundamentalGroup (AddCircle T) 0 ≃* Multiplicative ℤ)
    (he : ∀ n : ℤ, e (FundamentalGroup.fromPath ⟦loop T n⟧) = Multiplicative.ofAdd n) :
    e = fundamentalGroupEquivInt hT := by
  ext γ
  rw [eq_loop_fundamentalGroupEquivInt hT γ, he, fundamentalGroupEquivInt_loop]

/-- The endpoint of Mathlib's lift from zero is the signed period times the computed integer. -/
theorem liftPath_apply_one {T : ℝ} (hT : T ≠ 0) (γ : Path (0 : AddCircle T) 0) :
    (isCoveringMap_coe T).liftPath γ.toContinuousMap 0 γ.source 1 =
      T * ((fundamentalGroupEquivInt hT (FundamentalGroup.fromPath ⟦γ⟧)).toAdd : ℝ) := by
  exact (fundamentalGroupEquivInt_eq_iff_liftPath hT γ _).mp rfl

/-- Any real lift starting at zero computes the integer coordinate by its endpoint.
This is the signed-period form of May's lifted-endpoint description in Chapter 1, §5. -/
theorem fundamentalGroupEquivInt_apply_eq_iff {T : ℝ} (hT : T ≠ 0)
    (γ : Path (0 : AddCircle T) 0) (Γ : C(I, ℝ)) (hΓ₀ : Γ 0 = 0)
    (hΓ : ∀ t, (Γ t : AddCircle T) = γ t) (n : ℤ) :
    fundamentalGroupEquivInt hT (FundamentalGroup.fromPath ⟦γ⟧) = Multiplicative.ofAdd n ↔
      Γ 1 = T * (n : ℝ) := by
  have hl : Γ = (isCoveringMap_coe T).liftPath γ.toContinuousMap 0 γ.source :=
    ((isCoveringMap_coe T).eq_liftPath_iff' γ.source).mpr ⟨funext hΓ, hΓ₀⟩
  rw [fundamentalGroupEquivInt_eq_iff_liftPath hT γ n, ← hl]

/-- The prescribed one-turn loop is not the identity class for a nonzero period. -/
theorem loop_one_ne_one {T : ℝ} (hT : T ≠ 0) :
    FundamentalGroup.fromPath ⟦loop T 1⟧ ≠ (1 : FundamentalGroup (AddCircle T) 0) := by
  intro h
  have h' := congrArg (fundamentalGroupEquivInt hT) h
  rw [fundamentalGroupEquivInt_loop, map_one (fundamentalGroupEquivInt hT)] at h'
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (congrArg Multiplicative.toAdd h')

end AddCircle

namespace Circle

/-- The complex `n`-turn loop based at one, transported from the period-one additive circle. -/
def loop (n : ℤ) : Path (1 : Circle) 1 :=
  ((AddCircle.loop 1 n).map AddCircle.continuous_toCircle).cast
    AddCircle.toCircle_zero.symm AddCircle.toCircle_zero.symm

/-- The complex integer loop in radians; positive one is counterclockwise. -/
@[simp] theorem loop_apply (n : ℤ) (t : I) :
    loop n t = Circle.exp (2 * Real.pi * (n : ℝ) * (t : ℝ)) := by
  simp only [loop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    AddCircle.loop_apply, AddCircle.toCircle_apply_mk]
  congr 1
  ring

/-- The complex value of the integer loop is May's `exp(2πint)` parametrization. -/
theorem coe_loop_apply (n : ℤ) (t : I) :
    (loop n t : ℂ) = Complex.exp ((2 * Real.pi * (n : ℝ) * (t : ℝ) : ℝ) * Complex.I) := by
  rw [loop_apply, Circle.coe_exp]

/-- The zero-turn complex loop is constant. -/
@[simp] theorem loop_zero : loop 0 = Path.refl 1 := by
  ext t
  simp

end Circle

namespace AddCircle

/-- The signed-period homeomorphism sends every prescribed integer loop to the complex
integer loop, also for negative periods. -/
theorem homeomorphCircle_loop {T : ℝ} (hT : T ≠ 0) (n : ℤ) (t : I) :
    homeomorphCircle hT (loop T n t) = Circle.loop n t := by
  rw [homeomorphCircle_apply, loop_apply, toCircle_apply_mk, Circle.loop_apply]
  congr 1
  field_simp [hT]

end AddCircle

namespace Circle

/-- The integer calculator on the complex unit circle, transported from `AddCircle 1`.
It is normalized by May's counterclockwise generator in Chapter 1, §5. -/
def fundamentalGroupEquivInt : FundamentalGroup Circle 1 ≃* Multiplicative ℤ :=
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  let h : e 0 = 1 :=
    (AddCircle.homeomorphCircle_apply one_ne_zero 0).trans AddCircle.toCircle_zero
  let E : CategoryTheory.Equivalence
      (FundamentalGroupoid (AddCircle (1 : ℝ))) (FundamentalGroupoid Circle) :=
    FundamentalGroupoidFunctor.equivOfHomotopyEquiv e.toHomotopyEquiv
  let e₀ : FundamentalGroup (AddCircle (1 : ℝ)) 0 ≃* FundamentalGroup Circle (e 0) :=
    E.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk 0)
  (e₀.trans (CategoryTheory.eqToIso (C := FundamentalGroupoid Circle)
    (congrArg FundamentalGroupoid.mk h)).conj).symm.trans
      (AddCircle.fundamentalGroupEquivInt (T := (1 : ℝ)) one_ne_zero)

/-- The complex `n`-turn loop has integer coordinate `n`, with no sign reversal. -/
@[simp↓] theorem fundamentalGroupEquivInt_loop (n : ℤ) :
    fundamentalGroupEquivInt (FundamentalGroup.fromPath ⟦loop n⟧) =
      Multiplicative.ofAdd n := by
  let e := fundamentalGroupEquivOfHomeomorph
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero)
    (x := 0) (y := 1)
    ((AddCircle.homeomorphCircle_apply one_ne_zero 0).trans AddCircle.toCircle_zero)
  have he : e (FundamentalGroup.fromPath ⟦AddCircle.loop 1 n⟧) =
      FundamentalGroup.fromPath ⟦loop n⟧ := by
    simp only [e, fundamentalGroupEquivOfHomeomorph_apply, FundamentalGroup.mapOfEq_apply]
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk (loop n)
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    exact AddCircle.homeomorphCircle_loop one_ne_zero n t
  change AddCircle.fundamentalGroupEquivInt one_ne_zero
    (e.symm (FundamentalGroup.fromPath ⟦loop n⟧)) = _
  rw [← he, e.symm_apply_apply, AddCircle.fundamentalGroupEquivInt_loop]

/-- The inverse complex-circle calculator constructs the class of the integer loop. -/
@[simp] theorem fundamentalGroupEquivInt_symm_apply (n : ℤ) :
    fundamentalGroupEquivInt.symm (Multiplicative.ofAdd n) =
      FundamentalGroup.fromPath ⟦loop n⟧ := by
  exact fundamentalGroupEquivInt.symm_apply_eq.mpr
    (fundamentalGroupEquivInt_loop n).symm

/-- The integer-loop group law in the complex-circle fundamental group, as in May, §5. -/
theorem fromPath_loop_add (m n : ℤ) :
    FundamentalGroup.fromPath ⟦loop (m + n)⟧ =
      FundamentalGroup.fromPath ⟦loop m⟧ * FundamentalGroup.fromPath ⟦loop n⟧ := by
  apply fundamentalGroupEquivInt.injective
  simp only [map_mul, fundamentalGroupEquivInt_loop, ofAdd_add]

private theorem liftPath_loop (n : ℤ) :
    Circle.isCoveringMap_exp.liftPath (loop n).toContinuousMap 0
        ((loop n).source.trans Circle.exp_zero.symm) =
      (Path.segment (0 : ℝ) (2 * Real.pi * (n : ℝ))).toContinuousMap := by
  symm
  apply (Circle.isCoveringMap_exp.eq_liftPath_iff'
    ((loop n).source.trans Circle.exp_zero.symm)).mpr
  constructor
  · ext t
    simp [loop_apply, Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul, mul_comm]
  · exact (Path.segment (0 : ℝ) (2 * Real.pi * (n : ℝ))).source

/-- The endpoint of the zero-start lift through `Circle.exp` is `2π` times the integer
coordinate, because `Circle.exp` uses radians rather than period-one parameters. -/
theorem liftPath_apply_one (γ : Path (1 : Circle) 1) :
    Circle.isCoveringMap_exp.liftPath γ.toContinuousMap 0
        (γ.source.trans Circle.exp_zero.symm) 1 =
      2 * Real.pi * ((fundamentalGroupEquivInt (FundamentalGroup.fromPath ⟦γ⟧)).toAdd : ℝ) := by
  let n := (fundamentalGroupEquivInt (FundamentalGroup.fromPath ⟦γ⟧)).toAdd
  have hc : FundamentalGroup.fromPath ⟦γ⟧ = FundamentalGroup.fromPath ⟦loop n⟧ := by
    exact (fundamentalGroupEquivInt.symm_apply_apply _).symm.trans
      (fundamentalGroupEquivInt_symm_apply n)
  have hh : γ.Homotopic (loop n) := Path.Homotopic.Quotient.eq.mp hc
  rw [Circle.isCoveringMap_exp.liftPath_apply_one_eq_of_homotopicRel hh 0
    (γ.source.trans Circle.exp_zero.symm)
    ((loop n).source.trans Circle.exp_zero.symm), liftPath_loop]
  exact (Path.segment (0 : ℝ) (2 * Real.pi * (n : ℝ))).target

/-- A lift through the period-one exponential computes the integer coordinate directly
by its endpoint, exactly as in May's Chapter 1, §5 description. -/
theorem fundamentalGroupEquivInt_apply_eq_iff
    (γ : Path (1 : Circle) 1) (Γ : C(I, ℝ)) (hΓ₀ : Γ 0 = 0)
    (hΓ : ∀ t, Real.fourierChar (Γ t) = γ t) (n : ℤ) :
    fundamentalGroupEquivInt (FundamentalGroup.fromPath ⟦γ⟧) = Multiplicative.ofAdd n ↔
      Γ 1 = (n : ℝ) := by
  let Γ' : C(I, ℝ) := ⟨fun t ↦ 2 * Real.pi * Γ t, by fun_prop⟩
  have hl : Γ' = Circle.isCoveringMap_exp.liftPath γ.toContinuousMap 0
      (γ.source.trans Circle.exp_zero.symm) := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff'
      (γ.source.trans Circle.exp_zero.symm)).mpr
    exact ⟨funext hΓ, by simp [Γ', hΓ₀]⟩
  have hv : Γ 1 =
      ((fundamentalGroupEquivInt (FundamentalGroup.fromPath ⟦γ⟧)).toAdd : ℝ) := by
    apply mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity)
    exact (congrArg (fun f : C(I, ℝ) ↦ f 1) hl).trans (liftPath_apply_one γ)
  rw [hv]
  constructor
  · intro h
    exact congrArg (fun z : Multiplicative ℤ ↦ (z.toAdd : ℝ)) h
  · intro h
    exact congrArg Multiplicative.ofAdd (Int.cast_injective h)

/-- The standard counterclockwise one-turn loop is not the identity class. -/
theorem loop_one_ne_one :
    FundamentalGroup.fromPath ⟦loop 1⟧ ≠ (1 : FundamentalGroup Circle 1) := by
  intro h
  have h' := congrArg fundamentalGroupEquivInt h
  rw [fundamentalGroupEquivInt_loop, map_one fundamentalGroupEquivInt] at h'
  exact (one_ne_zero : (1 : ℤ) ≠ 0) (congrArg Multiplicative.toAdd h')

end Circle

namespace AddCircle

/-- Agreement of the signed-period and complex-circle calculators under the canonical
homeomorphism. This recovers May's positive normalization, not its negative. -/
theorem fundamentalGroupEquivInt_homeomorphCircle {T : ℝ} (hT : T ≠ 0)
    (γ : FundamentalGroup (AddCircle T) 0) :
    Circle.fundamentalGroupEquivInt
        (FundamentalGroup.mapOfEq ⟨homeomorphCircle hT, (homeomorphCircle hT).continuous⟩
          ((homeomorphCircle_apply hT 0).trans toCircle_zero) γ) =
      fundamentalGroupEquivInt hT γ := by
  rw [eq_loop_fundamentalGroupEquivInt hT γ]
  have hm : FundamentalGroup.mapOfEq
      ⟨homeomorphCircle hT, (homeomorphCircle hT).continuous⟩
      ((homeomorphCircle_apply hT 0).trans toCircle_zero)
      (FundamentalGroup.fromPath ⟦loop T
        (fundamentalGroupEquivInt hT γ).toAdd⟧) =
      FundamentalGroup.fromPath ⟦Circle.loop (fundamentalGroupEquivInt hT γ).toAdd⟧ := by
    rw [FundamentalGroup.mapOfEq_apply]
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    exact homeomorphCircle_loop hT _ t
  rw [hm, Circle.fundamentalGroupEquivInt_loop, fundamentalGroupEquivInt_loop]

end AddCircle

end

end
