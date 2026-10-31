/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Functor
import FundamentalGroupoids.Topology.Covering.Monodromy
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Topology.Homotopy.Lifting

/-!
# Integer coordinates for the fundamental group of the circle

The circle covering equivalence is normalized through its real period lattice.
The formulas include every signed exponential-loop class and the endpoints of
lifts through both the radian and the period-one exponentials.

These equations use the characteristic APIs for quotient-covering equivalences
and monodromy endpoints. Naturality for the real lift `t ↦ n*t` shows that every
integer power map, including the constant power map at zero, induces multiplication
by `n` in these same coordinates.

## References

* Junyan Xu, `Mathlib.Topology.Homotopy.Lifting`, for covering monodromy and lifts.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §§5, 7,
  for signed-loop normalization and the integer power-map computation.
-/

noncomputable section

open CategoryTheory

namespace Circle

private theorem periodHom_injective :
    Function.Injective (zmultiplesHom ℝ (2 * Real.pi)) := by
  intro m n h
  have hc : (2 : ℝ) * Real.pi ≠ 0 :=
    ne_of_gt (mul_pos zero_lt_two Real.pi_pos)
  have h' : (m : ℝ) * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by
    simpa only [zmultiplesHom_apply, zsmul_eq_mul] using h
  exact Int.cast_injective ((mul_left_inj' hc).mp h')

private def periodRangeEquiv : ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi) :=
  AddMonoidHom.ofInjective periodHom_injective

private theorem periodRangeEquiv_coe (n : ℤ) :
    (periodRangeEquiv n : ℝ) = n • (2 * Real.pi) := rfl

private def expOrigin : exp ⁻¹' {(1 : Circle)} := ⟨0, exp_zero⟩

private def integerNormalization :
    FundamentalGroup Circle (1 : Circle) ≃* Multiplicative ℤ :=
  (isAddQuotientCoveringMap_exp.fundamentalGroupEquiv expOrigin).trans
    ((MulOpposite.opMulEquiv :
        Multiplicative (AddSubgroup.zmultiples (2 * Real.pi)) ≃*
          (Multiplicative (AddSubgroup.zmultiples (2 * Real.pi)))ᵐᵒᵖ).symm.trans
      (AddEquiv.toMultiplicative periodRangeEquiv.symm))

private theorem integerNormalization_eq_iff
    (q : FundamentalGroup Circle (1 : Circle)) (n : ℤ) :
    integerNormalization q = Multiplicative.ofAdd n ↔
      (isCoveringMap_exp.monodromy q expOrigin : ℝ) = (n : ℝ) * (2 * Real.pi) := by
  let T : (Multiplicative (AddSubgroup.zmultiples (2 * Real.pi)))ᵐᵒᵖ ≃*
      Multiplicative ℤ :=
    (MulOpposite.opMulEquiv :
        Multiplicative (AddSubgroup.zmultiples (2 * Real.pi)) ≃*
          (Multiplicative (AddSubgroup.zmultiples (2 * Real.pi)))ᵐᵒᵖ).symm.trans
      (AddEquiv.toMultiplicative periodRangeEquiv.symm)
  have hT : T (MulOpposite.op (Multiplicative.ofAdd (periodRangeEquiv n))) =
      Multiplicative.ofAdd n := by
    change Multiplicative.ofAdd (periodRangeEquiv.symm (periodRangeEquiv n)) =
      Multiplicative.ofAdd n
    exact congrArg Multiplicative.ofAdd (periodRangeEquiv.symm_apply_apply n)
  calc
    integerNormalization q = Multiplicative.ofAdd n ↔
        isAddQuotientCoveringMap_exp.fundamentalGroupEquiv expOrigin q =
          MulOpposite.op (Multiplicative.ofAdd (periodRangeEquiv n)) := by
      change T (isAddQuotientCoveringMap_exp.fundamentalGroupEquiv expOrigin q) =
        Multiplicative.ofAdd n ↔ _
      rw [← hT, T.injective.eq_iff]
    _ ↔ (periodRangeEquiv n : ℝ) + 0 =
        (isCoveringMap_exp.monodromy q expOrigin : ℝ) :=
      isAddQuotientCoveringMap_exp.fundamentalGroupEquiv_apply_eq_iff expOrigin q _
    _ ↔ (isCoveringMap_exp.monodromy q expOrigin : ℝ) =
        (n : ℝ) * (2 * Real.pi) := by
      rw [add_zero, periodRangeEquiv_coe, zsmul_eq_mul]
      exact eq_comm

private theorem integerNormalization_lift_endpoint
    (γ : Path (1 : Circle) 1) (Γ : C(unitInterval, ℝ))
    (hΓ : ∀ t, exp (Γ t) = γ t) (h0 : Γ 0 = 0) (n : ℤ) :
    integerNormalization (Path.Homotopic.Quotient.mk γ) = Multiplicative.ofAdd n ↔
      Γ 1 = (n : ℝ) * (2 * Real.pi) := by
  have hend := isCoveringMap_exp.monodromy_mk_apply_eq_of_lift
    γ expOrigin Γ (funext hΓ) h0
  rw [integerNormalization_eq_iff, hend]

private theorem integerNormalization_radian_endpoint_div
    (γ : Path (1 : Circle) 1) (Γ : C(unitInterval, ℝ))
    (hΓ : ∀ t, exp (Γ t) = γ t) (h0 : Γ 0 = 0) (n : ℤ) :
    integerNormalization (Path.Homotopic.Quotient.mk γ) = Multiplicative.ofAdd n ↔
      Γ 1 / (2 * Real.pi) = (n : ℝ) := by
  have hc : (2 : ℝ) * Real.pi ≠ 0 :=
    ne_of_gt (mul_pos zero_lt_two Real.pi_pos)
  rw [integerNormalization_lift_endpoint γ Γ hΓ h0 n, div_eq_iff hc]

private theorem integerNormalization_periodOne_endpoint
    (γ : Path (1 : Circle) 1) (Γ : C(unitInterval, ℝ))
    (hΓ : ∀ t, exp ((2 * Real.pi) * Γ t) = γ t) (h0 : Γ 0 = 0) (n : ℤ) :
    integerNormalization (Path.Homotopic.Quotient.mk γ) = Multiplicative.ofAdd n ↔
      Γ 1 = (n : ℝ) := by
  let Δ : C(unitInterval, ℝ) :=
    ⟨fun t ↦ (2 * Real.pi) * Γ t, continuous_const.mul Γ.continuous⟩
  have hΔ : ∀ t, exp (Δ t) = γ t := hΓ
  have hΔ0 : Δ 0 = 0 := by simp [Δ, h0]
  have hc : (2 : ℝ) * Real.pi ≠ 0 :=
    ne_of_gt (mul_pos zero_lt_two Real.pi_pos)
  calc
    integerNormalization (Path.Homotopic.Quotient.mk γ) = Multiplicative.ofAdd n ↔
        (2 * Real.pi) * Γ 1 = (n : ℝ) * (2 * Real.pi) :=
      integerNormalization_lift_endpoint γ Δ hΔ hΔ0 n
    _ ↔ Γ 1 = (n : ℝ) := by
      rw [mul_comm (2 * Real.pi) (Γ 1)]
      exact mul_left_inj' hc

private def signedExpLoop (n : ℤ) : Path (1 : Circle) 1 :=
  ((Path.segment (0 : ℝ) ((n : ℝ) * (2 * Real.pi))).map exp.continuous).cast
    exp_zero.symm (exp_int_mul_two_pi n).symm

private theorem signedExpLoop_apply (n : ℤ) (t : unitInterval) :
    signedExpLoop n t = exp (2 * Real.pi * (n : ℝ) * (t : ℝ)) := by
  change exp ((Path.segment (0 : ℝ) ((n : ℝ) * (2 * Real.pi))) t) = _
  rw [Path.segment_apply, AffineMap.lineMap_apply_ring', sub_zero, add_zero]
  congr 1
  ac_rfl

private theorem integerNormalization_signedExpLoop (n : ℤ) :
    integerNormalization (Path.Homotopic.Quotient.mk (signedExpLoop n)) =
      Multiplicative.ofAdd n := by
  apply (integerNormalization_lift_endpoint (signedExpLoop n)
    (Path.segment (0 : ℝ) ((n : ℝ) * (2 * Real.pi)))
    (by intro t; rfl) (Path.source _) n).mpr
  exact Path.target _

private theorem integerNormalization_symm (n : ℤ) :
    integerNormalization.symm (Multiplicative.ofAdd n) =
      Path.Homotopic.Quotient.mk (signedExpLoop n) := by
  apply integerNormalization.injective
  rw [integerNormalization.apply_symm_apply, integerNormalization_signedExpLoop]

private theorem signedExpLoop_class_add (m n : ℤ) :
    (· * · : FundamentalGroup Circle 1 → FundamentalGroup Circle 1 →
        FundamentalGroup Circle 1)
      (Path.Homotopic.Quotient.mk (signedExpLoop m))
      (Path.Homotopic.Quotient.mk (signedExpLoop n)) =
      Path.Homotopic.Quotient.mk (signedExpLoop (m + n)) := by
  apply integerNormalization.injective
  simp only [map_mul, integerNormalization_signedExpLoop]
  rfl

/-- The real lift of each integer power map computes its induced map in the existing
integer coordinates. The exponent may be zero or negative; the power map is not assumed
to be a covering. -/
private theorem integerNormalization_map_zpow (n : ℤ)
    (q : FundamentalGroup Circle (1 : Circle)) :
    integerNormalization
        (FundamentalGroup.mapOfEq ⟨fun z : Circle ↦ z ^ n, continuous_zpow n⟩
          (one_zpow n) q) =
      Multiplicative.ofAdd (n * (integerNormalization q).toAdd) := by
  let F : C(ℝ, ℝ) := ⟨fun t ↦ (n : ℝ) * t, continuous_const.mul continuous_id⟩
  let f : C(Circle, Circle) := ⟨fun z ↦ z ^ n, continuous_zpow n⟩
  have hF : exp ∘ F = f ∘ exp := by
    funext t
    change exp ((n : ℝ) * t) = exp t ^ n
    simpa only [zsmul_eq_mul] using exp_zsmul t n
  have hnat := isCoveringMap_exp.monodromy_naturality_map
    isCoveringMap_exp F f hF q expOrigin
  have hend :
      (isCoveringMap_exp.monodromy
        (FundamentalGroup.mapOfEq f (one_zpow n) q) expOrigin : ℝ) =
          (n : ℝ) * (isCoveringMap_exp.monodromy q expOrigin : ℝ) := by
    rw [FundamentalGroup.mapOfEq_apply, isCoveringMap_exp.monodromy_cast]
    simpa [F, expOrigin] using congrArg Subtype.val hnat
  let m : ℤ := (integerNormalization q).toAdd
  have hm : integerNormalization q = Multiplicative.ofAdd m := rfl
  have he := (integerNormalization_eq_iff q m).mp hm
  apply (integerNormalization_eq_iff _ (n * m)).mpr
  change (isCoveringMap_exp.monodromy
    (FundamentalGroup.mapOfEq f (one_zpow n) q) expOrigin : ℝ) = _
  rw [hend, he, Int.cast_mul, mul_assoc]

/-- The based circle squaring map remains different from the identity after applying the
fundamental-group functor on the based-homotopy category. Its action is multiplication by two
in the integer coordinates of `integerNormalization_map_zpow`. -/
private theorem homotopyFunctor_map_square_ne_id :
    FundamentalGroup.homotopyFunctor.map
        (BasedTopCat.homotopyQuotient.map
          (BasedTopCat.ofHom
            (⟨fun z : Circle ↦ z ^ (2 : ℤ), continuous_zpow (2 : ℤ)⟩ : C(Circle, Circle))
            (one_zpow (2 : ℤ)))) ≠
      𝟙 (FundamentalGroup.homotopyFunctor.obj
        (BasedTopCat.homotopyQuotient.obj (BasedTopCat.of Circle (1 : Circle)))) := by
  intro h
  rw [FundamentalGroup.homotopyFunctor_map] at h
  let f : C(Circle, Circle) := ⟨fun z ↦ z ^ (2 : ℤ), continuous_zpow (2 : ℤ)⟩
  have hhom : FundamentalGroup.mapOfEq f (one_zpow (2 : ℤ)) =
      MonoidHom.id (FundamentalGroup Circle (1 : Circle)) := by
    exact (FundamentalGroup.functor_map_ofHom f (one_zpow (2 : ℤ))).symm.trans
      ((congrArg GrpCat.Hom.hom h).trans GrpCat.hom_id)
  have hloop :
      FundamentalGroup.mapOfEq f (one_zpow (2 : ℤ))
          (Path.Homotopic.Quotient.mk (signedExpLoop 1)) =
        Path.Homotopic.Quotient.mk (signedExpLoop 1) :=
    DFunLike.congr_fun hhom (Path.Homotopic.Quotient.mk (signedExpLoop 1))
  have hnorm := congrArg integerNormalization hloop
  have hmap := integerNormalization_map_zpow (2 : ℤ)
    (Path.Homotopic.Quotient.mk (signedExpLoop 1))
  have hgen := integerNormalization_signedExpLoop (1 : ℤ)
  have hcoord : Multiplicative.ofAdd (2 : ℤ) = Multiplicative.ofAdd (1 : ℤ) := by
    calc
      Multiplicative.ofAdd (2 : ℤ) =
          Multiplicative.ofAdd ((2 : ℤ) *
            (integerNormalization (Path.Homotopic.Quotient.mk (signedExpLoop 1))).toAdd) := by
        simpa only [toAdd_ofAdd, mul_one] using
          congrArg (fun x : Multiplicative ℤ ↦
            Multiplicative.ofAdd ((2 : ℤ) * x.toAdd)) hgen.symm
      _ = integerNormalization
          (Path.Homotopic.Quotient.mk (signedExpLoop 1)) := hmap.symm.trans hnorm
      _ = Multiplicative.ofAdd (1 : ℤ) := hgen
  have htwo : (2 : ℤ) = 1 := by
    simpa only [toAdd_ofAdd] using congrArg Multiplicative.toAdd hcoord
  exact (by decide : (2 : ℤ) ≠ 1) htwo

end Circle
