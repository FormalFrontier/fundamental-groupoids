/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Radial
public import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Circles inside punctured complex balls

Positive real scaling identifies `Circle` with a complex sphere. Composing this
identification with radial projection and inclusion gives normalization and the
scaled circle inside a punctured ball. The radial deformation fixes this circle
pointwise. In particular, the inner radius need only be positive and strictly
less than the outer radius; the outer radius need not exceed one.

The sphere identification uses the complex exponential and argument identity
from Mathlib, and its continuity uses the intrinsic compactness of `Circle`.
The deformation is the radial deformation in `Metric`.
-/

@[expose] public section

noncomputable section

namespace Complex

private theorem continuous_circle_coe : Continuous ((↑) : Circle → ℂ) := by
  apply (continuous_id.smul continuous_const :
    Continuous (fun z : Circle => z • (1 : ℂ))).congr
  intro z
  change z • (1 : ℂ) = (z : ℂ)
  simpa only [smul_eq_mul, mul_one] using Circle.smul_def z (1 : ℂ)

private def circleSphereMap (a : ℝ) (ha : 0 < a) :
    Circle → ↥(Metric.sphere (0 : ℂ) a) := by
  intro z
  refine ⟨a • (z : ℂ), ?_⟩
  rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos ha, Circle.norm_coe, mul_one]

private theorem circleSphereMap_bijective (a : ℝ) (ha : 0 < a) :
    Function.Bijective (circleSphereMap a ha) := by
  constructor
  · intro z w h
    apply Circle.coe_injective
    have h' : a • (z : ℂ) = a • (w : ℂ) := congrArg Subtype.val h
    simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using
      congrArg (fun v : ℂ => (a⁻¹ : ℝ) • v) h'
  · intro z
    refine ⟨Circle.exp (Complex.arg (z : ℂ)), ?_⟩
    apply Subtype.ext
    change a • (Circle.exp (Complex.arg (z : ℂ)) : ℂ) = (z : ℂ)
    rw [Circle.coe_exp, Complex.real_smul]
    have hz : ‖(z : ℂ)‖ = a := by
      simpa only [Metric.mem_sphere, dist_zero_right] using z.property
    simpa only [hz] using Complex.norm_mul_exp_arg_mul_I (z : ℂ)

/-- Positive real scaling identifies the unit circle with the complex sphere of radius `a`. -/
def circleHomeomorphSphere (a : ℝ) (ha : 0 < a) :
    Circle ≃ₜ ↥(Metric.sphere (0 : ℂ) a) := by
  let e : Circle ≃ ↥(Metric.sphere (0 : ℂ) a) := Equiv.ofBijective
    (fun z => ⟨a • (z : ℂ), by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos ha, Circle.norm_coe, mul_one]⟩)
    (by exact circleSphereMap_bijective a ha)
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) (by exact (continuous_circle_coe.const_smul a).subtype_mk _)

/-- The sphere identification multiplies the ambient complex number by the positive radius. -/
@[simp]
theorem circleHomeomorphSphere_apply (a : ℝ) (ha : 0 < a) (z : Circle) :
    (circleHomeomorphSphere a ha z : ℂ) = a • (z : ℂ) := by
  rfl

/-- The inverse sphere identification divides the ambient complex number by the radius. -/
@[simp]
theorem circleHomeomorphSphere_symm_apply (a : ℝ) (ha : 0 < a)
    (z : ↥(Metric.sphere (0 : ℂ) a)) :
    ((circleHomeomorphSphere a ha).symm z : ℂ) = (a⁻¹ : ℝ) • (z : ℂ) := by
  have h := congrArg (fun w : ↥(Metric.sphere (0 : ℂ) a) => (w : ℂ))
    ((circleHomeomorphSphere a ha).apply_symm_apply z)
  rw [circleHomeomorphSphere_apply] at h
  calc
    ((circleHomeomorphSphere a ha).symm z : ℂ) =
        (a⁻¹ : ℝ) • (a • ((circleHomeomorphSphere a ha).symm z : ℂ)) := by
      rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul]
    _ = (a⁻¹ : ℝ) • (z : ℂ) := congrArg (fun v : ℂ => (a⁻¹ : ℝ) • v) h

/-- The circle of radius `a` inside the punctured complex ball of radius `r`. -/
def circleToPuncturedBall (a r : ℝ) (ha : 0 < a) (har : a < r) :
    C(Circle, ↥(Metric.ball (0 : ℂ) r \ {0})) := by
  exact (Metric.sphereToPuncturedBall a r ha har).comp
    (circleHomeomorphSphere a ha : C(Circle, ↥(Metric.sphere (0 : ℂ) a)))

/-- Normalization to `Circle`, through radial projection onto the sphere of radius `a`.

The normalization does not require the sphere to lie inside the ball. -/
def puncturedBallToCircle (a r : ℝ) (ha : 0 < a) :
    C(↥(Metric.ball (0 : ℂ) r \ {0}), Circle) := by
  exact ((circleHomeomorphSphere a ha).symm :
    C(↥(Metric.sphere (0 : ℂ) a), Circle)).comp (Metric.puncturedBallRetraction a r ha)

/-- The circle parametrization is positive real scaling in the complex plane. -/
@[simp]
theorem circleToPuncturedBall_apply (a r : ℝ) (ha : 0 < a) (har : a < r)
    (z : Circle) :
    (circleToPuncturedBall a r ha har z : ℂ) = a • (z : ℂ) := by
  change (Metric.sphereToPuncturedBall a r ha har (circleHomeomorphSphere a ha z) : ℂ) = _
  rw [Metric.sphereToPuncturedBall_apply, circleHomeomorphSphere_apply]

/-- Normalization divides the complex number by its norm, independently of the inner radius. -/
@[simp]
theorem puncturedBallToCircle_apply (a r : ℝ) (ha : 0 < a)
    (z : ↥(Metric.ball (0 : ℂ) r \ {0})) :
    (puncturedBallToCircle a r ha z : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) := by
  change ((circleHomeomorphSphere a ha).symm
    (Metric.puncturedBallRetraction a r ha z) : ℂ) = _
  rw [circleHomeomorphSphere_symm_apply, Metric.puncturedBallRetraction_apply, smul_smul]
  have hscale : a⁻¹ * (a / ‖(z : ℂ)‖) = ‖(z : ℂ)‖⁻¹ := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  rw [hscale]
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv, mul_comm]

/-- Normalization is a left inverse to the scaled circle parametrization. -/
@[simp]
theorem puncturedBallToCircle_circleToPuncturedBall
    (a r : ℝ) (ha : 0 < a) (har : a < r) (z : Circle) :
    puncturedBallToCircle a r ha (circleToPuncturedBall a r ha har z) = z := by
  change (circleHomeomorphSphere a ha).symm
    (Metric.puncturedBallRetraction a r ha
      (Metric.sphereToPuncturedBall a r ha har (circleHomeomorphSphere a ha z))) = z
  rw [Metric.puncturedBallRetraction_sphereToPuncturedBall]
  exact (circleHomeomorphSphere a ha).symm_apply_apply z

/-- The composite of scaling and normalization is the identity continuous map on `Circle`. -/
theorem puncturedBallToCircle_comp_circleToPuncturedBall
    (a r : ℝ) (ha : 0 < a) (har : a < r) :
    (puncturedBallToCircle a r ha).comp (circleToPuncturedBall a r ha har) =
      ContinuousMap.id Circle := by
  apply ContinuousMap.ext
  intro z
  exact puncturedBallToCircle_circleToPuncturedBall a r ha har z

/-- The radial deformation ends at scaling after normalization to `Circle`. -/
theorem puncturedBallDeformation_one_circle
    (a r : ℝ) (ha : 0 < a) (har : a < r)
    (z : ↥(Metric.ball (0 : ℂ) r \ {0})) :
    Metric.puncturedBallDeformation a r ha har (1, z) =
      circleToPuncturedBall a r ha har (puncturedBallToCircle a r ha z) := by
  rw [Metric.puncturedBallDeformation_one]
  change Metric.sphereToPuncturedBall a r ha har (Metric.puncturedBallRetraction a r ha z) =
    Metric.sphereToPuncturedBall a r ha har
      (circleHomeomorphSphere a ha
        ((circleHomeomorphSphere a ha).symm (Metric.puncturedBallRetraction a r ha z)))
  rw [Homeomorph.apply_symm_apply]

/-- Every scaled circle point is fixed throughout the radial deformation. -/
theorem puncturedBallDeformation_circle
    (a r : ℝ) (ha : 0 < a) (har : a < r)
    (t : unitInterval) (z : Circle) :
    Metric.puncturedBallDeformation a r ha har
      (t, circleToPuncturedBall a r ha har z) = circleToPuncturedBall a r ha har z := by
  exact Metric.puncturedBallDeformation_fixed a r ha har t _
    ⟨circleHomeomorphSphere a ha z, rfl⟩

/-- In the unit ball the scaled basepoint for the half-radius circle is exactly `1/2`. -/
theorem circleToPuncturedBall_half_unit_one :
    (circleToPuncturedBall (1 / 2) 1 (by norm_num) (by norm_num) 1 : ℂ) = (1 / 2 : ℂ) := by
  rw [circleToPuncturedBall_apply, Circle.coe_one, Complex.real_smul]
  norm_num

end Complex
