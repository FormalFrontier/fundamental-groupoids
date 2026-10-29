/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

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
and monodromy endpoints.

## References

* Junyan Xu, `Mathlib.Topology.Homotopy.Lifting`, for covering monodromy and lifts.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §5,
  for the signed-loop and lifted-endpoint normalization.
-/

noncomputable section

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

end Circle
