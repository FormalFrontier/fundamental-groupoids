/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle
public import FundamentalGroupoids.Topology.Homotopy.ComplexPuncturedBall
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.CategoryTheory.Endomorphism

/-!
# The fundamental group of a punctured complex ball

Normalization to `Circle` classifies the fundamental group of a punctured complex
ball by the integers, at the image of `1 : Circle` on any positive-radius inner
circle. The inverse homomorphism scales circle loops into the ball. In particular,
the scaled class of `Circle.loop n` has index `n`, with the positive loop having
index one.

The construction uses Mathlib's equivalence of fundamental groupoids induced by
a homotopy equivalence, together with the classification of the circle group in
`Circle.fundamentalGroupEquivInt`. The homotopy equivalence is the radial
retraction followed by the positive-scaling sphere identification.
-/

@[expose] public section

noncomputable section

namespace Complex

private theorem puncturedBallCircleHomotopyEquiv_toFun
    (a r : ℝ) (ha : 0 < a) (har : a < r) :
    ((Metric.puncturedBallHomotopyEquivSphere (E := ℂ) a r ha har).trans
      (circleHomeomorphSphere a ha).symm.toHomotopyEquiv).toFun =
        puncturedBallToCircle a r ha := by
  apply ContinuousMap.ext
  intro z
  change (circleHomeomorphSphere a ha).symm
      (Metric.puncturedBallHomotopyEquivSphere (E := ℂ) a r ha har z) =
    (circleHomeomorphSphere a ha).symm (Metric.puncturedBallRetraction a r ha z)
  rw [Metric.puncturedBallHomotopyEquivSphere_apply]

/-- The fundamental group of a punctured complex ball, based on a positive-radius
inner circle, is classified by the integer index of its normalization to `Circle`. -/
def puncturedBallFundamentalGroupEquivInt
    (a r : ℝ) (ha : 0 < a) (har : a < r) :
    FundamentalGroup (↥(Metric.ball (0 : ℂ) r \ {0}))
      (circleToPuncturedBall a r ha har 1) ≃* Multiplicative ℤ := by
  let e : FundamentalGroupoid (↥(Metric.ball (0 : ℂ) r \ {0})) ≌
      FundamentalGroupoid Circle :=
    FundamentalGroupoidFunctor.equivOfHomotopyEquiv
      ((Metric.puncturedBallHomotopyEquivSphere (E := ℂ) a r ha har).trans
        (circleHomeomorphSphere a ha).symm.toHomotopyEquiv)
  have hbase :
      ((Metric.puncturedBallHomotopyEquivSphere (E := ℂ) a r ha har).trans
        (circleHomeomorphSphere a ha).symm.toHomotopyEquiv).toFun
          (circleToPuncturedBall a r ha har 1) = (1 : Circle) := by
    change (circleHomeomorphSphere a ha).symm
      (Metric.puncturedBallHomotopyEquivSphere (E := ℂ) a r ha har
        (circleToPuncturedBall a r ha har 1)) = (1 : Circle)
    rw [Metric.puncturedBallHomotopyEquivSphere_apply]
    exact puncturedBallToCircle_circleToPuncturedBall a r ha har 1
  exact ((e.fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk (circleToPuncturedBall a r ha har 1))).trans
      (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk hbase)).conj).trans
    Circle.fundamentalGroupEquivInt

/-- The classification homomorphism is normalization followed by the circle index. -/
theorem puncturedBallFundamentalGroupEquivInt_toMonoidHom
    (a r : ℝ) (ha : 0 < a) (har : a < r) :
    (puncturedBallFundamentalGroupEquivInt a r ha har).toMonoidHom =
      Circle.fundamentalGroupEquivInt.toMonoidHom.comp
        (FundamentalGroup.mapOfEq (puncturedBallToCircle a r ha)
          (puncturedBallToCircle_circleToPuncturedBall a r ha har 1)) := by
  change Circle.fundamentalGroupEquivInt.toMonoidHom.comp
    (FundamentalGroup.mapOfEq
      (((Metric.puncturedBallHomotopyEquivSphere (E := ℂ) a r ha har).trans
        (circleHomeomorphSphere a ha).symm.toHomotopyEquiv).toFun)
      (by
        rw [puncturedBallCircleHomotopyEquiv_toFun]
        exact puncturedBallToCircle_circleToPuncturedBall a r ha har 1)) = _
  simp only [puncturedBallCircleHomotopyEquiv_toFun]

/-- The index of a punctured-ball loop is the circle index after normalization. -/
theorem puncturedBallFundamentalGroupEquivInt_apply
    (a r : ℝ) (ha : 0 < a) (har : a < r)
    (p : FundamentalGroup (↥(Metric.ball (0 : ℂ) r \ {0}))
      (circleToPuncturedBall a r ha har 1)) :
    puncturedBallFundamentalGroupEquivInt a r ha har p =
      Circle.fundamentalGroupEquivInt
        (FundamentalGroup.mapOfEq (puncturedBallToCircle a r ha)
          (puncturedBallToCircle_circleToPuncturedBall a r ha har 1) p) := by
  exact DFunLike.congr_fun
    (puncturedBallFundamentalGroupEquivInt_toMonoidHom a r ha har) p

private theorem normalization_map_scale
    (a r : ℝ) (ha : 0 < a) (har : a < r) (p : FundamentalGroup Circle 1) :
    FundamentalGroup.mapOfEq (puncturedBallToCircle a r ha)
        (puncturedBallToCircle_circleToPuncturedBall a r ha har 1)
        (FundamentalGroup.map (circleToPuncturedBall a r ha har) (1 : Circle) p) = p := by
  have h := DFunLike.congr_fun
    (FundamentalGroup.mapOfEq_comp (puncturedBallToCircle a r ha)
      (circleToPuncturedBall a r ha har) (rfl :
        circleToPuncturedBall a r ha har 1 = circleToPuncturedBall a r ha har 1)
      (puncturedBallToCircle_circleToPuncturedBall a r ha har 1)) p
  simp only [puncturedBallToCircle_comp_circleToPuncturedBall,
    FundamentalGroup.mapOfEq_rfl, MonoidHom.comp_apply] at h
  exact h.symm.trans (DFunLike.congr_fun
    (FundamentalGroup.mapOfEq_id (1 : Circle)) p)

/-- The inverse classification sends an integer class to the corresponding scaled circle class. -/
theorem puncturedBallFundamentalGroupEquivInt_symm_apply
    (a r : ℝ) (ha : 0 < a) (har : a < r) (k : Multiplicative ℤ) :
    (puncturedBallFundamentalGroupEquivInt a r ha har).symm k =
      FundamentalGroup.map (circleToPuncturedBall a r ha har) (1 : Circle)
        (Circle.fundamentalGroupEquivInt.symm k) := by
  apply (puncturedBallFundamentalGroupEquivInt a r ha har).injective
  rw [MulEquiv.apply_symm_apply, puncturedBallFundamentalGroupEquivInt_apply,
    normalization_map_scale, MulEquiv.apply_symm_apply]

/-- The inverse homomorphism is inverse circle classification followed by scaling. -/
theorem puncturedBallFundamentalGroupEquivInt_symm_toMonoidHom
    (a r : ℝ) (ha : 0 < a) (har : a < r) :
    (puncturedBallFundamentalGroupEquivInt a r ha har).symm.toMonoidHom =
      (FundamentalGroup.map (circleToPuncturedBall a r ha har) (1 : Circle)).comp
        Circle.fundamentalGroupEquivInt.symm.toMonoidHom := by
  apply MonoidHom.ext
  intro k
  exact puncturedBallFundamentalGroupEquivInt_symm_apply a r ha har k

/-- Scaling the circle loop of any integer index preserves that index in the punctured ball. -/
theorem puncturedBallFundamentalGroupEquivInt_loop
    (a r : ℝ) (ha : 0 < a) (har : a < r) (n : ℤ) :
    puncturedBallFundamentalGroupEquivInt a r ha har
      (FundamentalGroup.map (circleToPuncturedBall a r ha har) (1 : Circle)
        (FundamentalGroup.fromPath ⟦Circle.loop n⟧)) = Multiplicative.ofAdd n := by
  rw [puncturedBallFundamentalGroupEquivInt_apply, normalization_map_scale,
    Circle.fundamentalGroupEquivInt_loop]

/-- The inverse image of every integer is the corresponding scaled circle-loop class. -/
theorem puncturedBallFundamentalGroupEquivInt_symm_ofAdd
    (a r : ℝ) (ha : 0 < a) (har : a < r) (n : ℤ) :
    (puncturedBallFundamentalGroupEquivInt a r ha har).symm
        (Multiplicative.ofAdd n) =
      FundamentalGroup.map (circleToPuncturedBall a r ha har) (1 : Circle)
        (FundamentalGroup.fromPath ⟦Circle.loop n⟧) := by
  rw [puncturedBallFundamentalGroupEquivInt_symm_apply,
    Circle.fundamentalGroupEquivInt_symm_apply]

/-- The scaled positive circle loop has positive index one. -/
theorem puncturedBallFundamentalGroupEquivInt_loop_one
    (a r : ℝ) (ha : 0 < a) (har : a < r) :
    puncturedBallFundamentalGroupEquivInt a r ha har
      (FundamentalGroup.map (circleToPuncturedBall a r ha har) (1 : Circle)
        (FundamentalGroup.fromPath ⟦Circle.loop 1⟧)) = Multiplicative.ofAdd (1 : ℤ) := by
  exact puncturedBallFundamentalGroupEquivInt_loop a r ha har 1

/-- The scaled positive circle loop is nontrivial in the punctured complex ball. -/
theorem puncturedBall_loop_one_ne_one
    (a r : ℝ) (ha : 0 < a) (har : a < r) :
    FundamentalGroup.map (circleToPuncturedBall a r ha har) (1 : Circle)
      (FundamentalGroup.fromPath ⟦Circle.loop 1⟧) ≠ 1 := by
  intro h
  have hi := congrArg (puncturedBallFundamentalGroupEquivInt a r ha har) h
  rw [puncturedBallFundamentalGroupEquivInt_loop_one,
    map_one (puncturedBallFundamentalGroupEquivInt a r ha har)] at hi
  have hzero : (1 : ℤ) = 0 := congrArg Multiplicative.toAdd hi
  exact one_ne_zero hzero

/-- The half-radius circle in the unit ball gives a nontrivial positive, not negative,
integer generator under normalization. -/
theorem puncturedBall_half_unit_positive_generator :
    puncturedBallFundamentalGroupEquivInt (1 / 2) 1 (by norm_num) (by norm_num)
        (FundamentalGroup.map
          (circleToPuncturedBall (1 / 2) 1 (by norm_num) (by norm_num)) (1 : Circle)
          (FundamentalGroup.fromPath ⟦Circle.loop 1⟧)) = Multiplicative.ofAdd (1 : ℤ) ∧
      FundamentalGroup.map
          (circleToPuncturedBall (1 / 2) 1 (by norm_num) (by norm_num)) (1 : Circle)
          (FundamentalGroup.fromPath ⟦Circle.loop 1⟧) ≠ 1 ∧
      puncturedBallFundamentalGroupEquivInt (1 / 2) 1 (by norm_num) (by norm_num)
        (FundamentalGroup.map
          (circleToPuncturedBall (1 / 2) 1 (by norm_num) (by norm_num)) (1 : Circle)
          (FundamentalGroup.fromPath ⟦Circle.loop 1⟧)) ≠ Multiplicative.ofAdd (-1 : ℤ) := by
  refine ⟨puncturedBallFundamentalGroupEquivInt_loop_one (1 / 2) 1 (by norm_num) (by norm_num),
    puncturedBall_loop_one_ne_one (1 / 2) 1 (by norm_num) (by norm_num), ?_⟩
  rw [puncturedBallFundamentalGroupEquivInt_loop_one]
  intro h
  have hi : (1 : ℤ) = -1 := congrArg Multiplicative.toAdd h
  norm_num at hi

end Complex
