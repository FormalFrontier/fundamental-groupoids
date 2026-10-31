/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle
import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Products

/-!
# Integer coordinates for the fundamental group of the circle

The public circle coordinates compute every signed exponential-loop class and
endpoints of lifts through both the radian and the period-one exponentials.
The local names below are aliases for `Circle.fundamentalGroupEquivInt` and
`Circle.loop`, not a separate covering or period-lattice construction.

The explicit signed-loop formula shows that every integer power map, including
the constant power map at zero, induces multiplication by its exponent in these
same coordinates. In particular, the squaring map is not the identity after
applying the fundamental-group functor on the based-homotopy category.
For the categorical product of two based circles, the canonical fundamental-group
comparison and its two projections give integer coordinates sending the signed
coordinate loops to their prescribed pair of integers. The empty-product
comparison includes the based one-point space.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §§5, 7,
  for signed-loop normalization and the integer power-map computation.
* The signed-period and complex-circle formalization by Formal Frontier Agents,
  originating in Sphere Topology; see
  `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle`.
* Mathlib's covering and lifting formalization by Junyan Xu.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Circle

private def integerNormalization :
    FundamentalGroup Circle (1 : Circle) ≃* Multiplicative ℤ :=
  Circle.fundamentalGroupEquivInt

private theorem integerNormalization_lift_endpoint
    (γ : Path (1 : Circle) 1) (Γ : C(unitInterval, ℝ))
    (hΓ : ∀ t, exp (Γ t) = γ t) (h0 : Γ 0 = 0) (n : ℤ) :
    integerNormalization (Path.Homotopic.Quotient.mk γ) = Multiplicative.ofAdd n ↔
      Γ 1 = (n : ℝ) * (2 * Real.pi) := by
  have hc : (2 : ℝ) * Real.pi ≠ 0 :=
    ne_of_gt (mul_pos zero_lt_two Real.pi_pos)
  have hl : Γ = isCoveringMap_exp.liftPath γ.toContinuousMap 0
      (γ.source.trans exp_zero.symm) :=
    (isCoveringMap_exp.eq_liftPath_iff' (γ.source.trans exp_zero.symm)).mpr
      ⟨funext hΓ, h0⟩
  have hend : Γ 1 = 2 * Real.pi *
      ((integerNormalization (Path.Homotopic.Quotient.mk γ)).toAdd : ℝ) :=
    (congrArg (fun F : C(unitInterval, ℝ) ↦ F 1) hl).trans (Circle.liftPath_apply_one γ)
  calc
    integerNormalization (Path.Homotopic.Quotient.mk γ) = Multiplicative.ofAdd n ↔
        ((integerNormalization (Path.Homotopic.Quotient.mk γ)).toAdd : ℝ) = (n : ℝ) := by
      constructor
      · intro h
        exact congrArg (fun z : Multiplicative ℤ ↦ (z.toAdd : ℝ)) h
      · intro h
        exact congrArg Multiplicative.ofAdd (Int.cast_injective h)
    _ ↔ Γ 1 = (n : ℝ) * (2 * Real.pi) := by
      rw [hend, mul_comm (n : ℝ) (2 * Real.pi)]
      exact (mul_right_inj' hc).symm

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
      Γ 1 = (n : ℝ) :=
  Circle.fundamentalGroupEquivInt_apply_eq_iff γ Γ h0 hΓ n

private def signedExpLoop (n : ℤ) : Path (1 : Circle) 1 := Circle.loop n

private theorem signedExpLoop_apply (n : ℤ) (t : unitInterval) :
    signedExpLoop n t = exp (2 * Real.pi * (n : ℝ) * (t : ℝ)) :=
  Circle.loop_apply n t

private theorem integerNormalization_signedExpLoop (n : ℤ) :
    integerNormalization (Path.Homotopic.Quotient.mk (signedExpLoop n)) =
      Multiplicative.ofAdd n :=
  Circle.fundamentalGroupEquivInt_loop n

private theorem integerNormalization_symm (n : ℤ) :
    integerNormalization.symm (Multiplicative.ofAdd n) =
      Path.Homotopic.Quotient.mk (signedExpLoop n) :=
  Circle.fundamentalGroupEquivInt_symm_apply n

private theorem signedExpLoop_class_add (m n : ℤ) :
    (· * · : FundamentalGroup Circle 1 → FundamentalGroup Circle 1 →
        FundamentalGroup Circle 1)
      (Path.Homotopic.Quotient.mk (signedExpLoop m))
      (Path.Homotopic.Quotient.mk (signedExpLoop n)) =
      Path.Homotopic.Quotient.mk (signedExpLoop (m + n)) :=
  (Circle.fromPath_loop_add m n).symm

/-- Every integer power map multiplies the public integer coordinate by its exponent.
The exponent may be zero or negative; the power map is not assumed to be a covering. -/
private theorem integerNormalization_map_zpow (n : ℤ)
    (q : FundamentalGroup Circle (1 : Circle)) :
    integerNormalization
        (FundamentalGroup.mapOfEq ⟨fun z : Circle ↦ z ^ n, continuous_zpow n⟩
          (one_zpow n) q) =
      Multiplicative.ofAdd (n * (integerNormalization q).toAdd) := by
  let m : ℤ := (integerNormalization q).toAdd
  have hq : q = Path.Homotopic.Quotient.mk (signedExpLoop m) :=
    (integerNormalization.symm_apply_apply q).symm.trans (integerNormalization_symm m)
  have hmap :
      FundamentalGroup.mapOfEq ⟨fun z : Circle ↦ z ^ n, continuous_zpow n⟩
          (one_zpow n) (Path.Homotopic.Quotient.mk (signedExpLoop m)) =
        Path.Homotopic.Quotient.mk (signedExpLoop (n * m)) := by
    rw [FundamentalGroup.mapOfEq_apply]
    change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    change signedExpLoop m t ^ n = signedExpLoop (n * m) t
    rw [signedExpLoop_apply, signedExpLoop_apply, ← exp_zsmul, zsmul_eq_mul, Int.cast_mul]
    congr 1
    ring
  calc
    integerNormalization
        (FundamentalGroup.mapOfEq ⟨fun z : Circle ↦ z ^ n, continuous_zpow n⟩
          (one_zpow n) q) =
        integerNormalization (Path.Homotopic.Quotient.mk (signedExpLoop (n * m))) := by
      rw [hq, hmap]
    _ = Multiplicative.ofAdd (n * m) := integerNormalization_signedExpLoop _

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

/-- Two circles based at one, with their ordinary categorical product. -/
private abbrev productFamily : Fin 2 → BasedTopCat :=
  fun _ => BasedTopCat.of Circle (1 : Circle)

/-- Integer coordinates obtained from the canonical product comparison and both
chosen group-product projections, using the same circle normalization as above. -/
private def productIntegerCoordinates :
    FundamentalGroup.functor.obj (∏ᶜ productFamily) →*
      Multiplicative ℤ × Multiplicative ℤ :=
  ((integerNormalization.toMonoidHom.comp
      (Pi.π (fun i => FundamentalGroup.functor.obj (productFamily i)) 0).hom).prod
    (integerNormalization.toMonoidHom.comp
      (Pi.π (fun i => FundamentalGroup.functor.obj (productFamily i)) 1).hom)).comp
    (piComparison FundamentalGroup.functor productFamily).hom

/-- The product of two signed exponential loops, transported to the chosen based product. -/
private def productSignedLoopClass (m n : ℤ) :
    FundamentalGroup.functor.obj (∏ᶜ productFamily) :=
  FundamentalGroup.functor.map (BasedTopCat.piIsoPi productFamily).inv
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
      (Path.pi (fun i : Fin 2 => if i = 0 then signedExpLoop m else signedExpLoop n))))

private theorem productIntegerCoordinates_map_piIsoPi_inv
    (q : FundamentalGroup (Fin 2 → Circle) (fun _ => (1 : Circle))) :
    productIntegerCoordinates
        (FundamentalGroup.functor.map (BasedTopCat.piIsoPi productFamily).inv q) =
      (integerNormalization
          (FundamentalGroup.piMulEquiv (fun _ : Fin 2 => (1 : Circle)) q 0),
        integerNormalization
          (FundamentalGroup.piMulEquiv (fun _ : Fin 2 => (1 : Circle)) q 1)) := by
  have h := DFunLike.congr_fun
    (FundamentalGroup.functor_piComparison_eq_piMulEquiv productFamily) q
  exact Prod.ext
    (congrArg integerNormalization (congrFun h 0))
    (congrArg integerNormalization (congrFun h 1))

/-- The two signed coordinate loops form the two distinct nonidentity integer
coordinate classes under the canonical categorical comparison. -/
private theorem productIntegerCoordinates_signedLoops (m n : ℤ) :
    Function.Bijective productIntegerCoordinates ∧
      productIntegerCoordinates (productSignedLoopClass m n) =
        (Multiplicative.ofAdd m, Multiplicative.ofAdd n) ∧
      productSignedLoopClass 1 0 ≠ 1 ∧
      productSignedLoopClass 0 1 ≠ 1 ∧
      productSignedLoopClass 1 0 ≠ productSignedLoopClass 0 1 := by
  let e : FundamentalGroup (Fin 2 → Circle) (fun _ => (1 : Circle)) ≃
      Multiplicative ℤ × Multiplicative ℤ :=
    ((FundamentalGroup.piMulEquiv (fun _ : Fin 2 => (1 : Circle))).toEquiv.trans
      (Equiv.piCongrRight (fun _ : Fin 2 => integerNormalization.toEquiv))).trans
      (piFinTwoEquiv (fun _ : Fin 2 => Multiplicative ℤ))
  have he :
      productIntegerCoordinates ∘
          (FundamentalGroup.functor.map (BasedTopCat.piIsoPi productFamily).inv) =
        e := by
    funext q
    exact productIntegerCoordinates_map_piIsoPi_inv q
  have htransport :
      Function.Bijective
        (FundamentalGroup.functor.map (BasedTopCat.piIsoPi productFamily).inv) :=
    ((FundamentalGroup.functor.mapIso
      (BasedTopCat.piIsoPi productFamily).symm).groupIsoToMulEquiv).bijective
  have hbij : Function.Bijective productIntegerCoordinates := by
    apply (Function.Bijective.of_comp_iff productIntegerCoordinates htransport).mp
    rw [he]
    exact e.bijective
  have hcoords (a b : ℤ) :
      productIntegerCoordinates (productSignedLoopClass a b) =
        (Multiplicative.ofAdd a, Multiplicative.ofAdd b) := by
    let γ : Fin 2 → Path (1 : Circle) 1 :=
      fun i => if i = 0 then signedExpLoop a else signedExpLoop b
    have hγ :
        FundamentalGroup.piMulEquiv (fun _ : Fin 2 => (1 : Circle))
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.pi γ))) =
          fun i => FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ i)) := by
      rw [← FundamentalGroup.piMulEquiv_symm_fromPath
        (fun _ : Fin 2 => (1 : Circle)) γ]
      exact (FundamentalGroup.piMulEquiv _).apply_symm_apply _
    exact (productIntegerCoordinates_map_piIsoPi_inv
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.pi γ)))).trans (by
        simp only [hγ]
        simp [γ, integerNormalization_signedExpLoop])
  have hone : Multiplicative.ofAdd (1 : ℤ) ≠ (1 : Multiplicative ℤ) := by decide
  refine ⟨hbij, hcoords m n, ?_, ?_, ?_⟩
  · intro h
    have hc := congrArg productIntegerCoordinates h
    simp only [hcoords, map_one] at hc
    exact hone (congrArg Prod.fst hc)
  · intro h
    have hc := congrArg productIntegerCoordinates h
    simp only [hcoords, map_one] at hc
    exact hone (congrArg Prod.snd hc)
  · intro h
    have hc := congrArg productIntegerCoordinates h
    simp only [hcoords] at hc
    exact hone (congrArg Prod.fst hc)

/-- In the empty case the source and target of the canonical comparison are
trivial groups, as is the fundamental group of the based one-point space. -/
private theorem empty_product_comparison :
    Subsingleton (FundamentalGroup.functor.obj (BasedTopCat.of PUnit.{1} PUnit.unit)) ∧
      IsIso (piComparison FundamentalGroup.functor
        (fun _ : Empty => BasedTopCat.of PUnit.{1} PUnit.unit)) ∧
      (∀ q : FundamentalGroup.functor.obj
          (∏ᶜ fun _ : Empty => BasedTopCat.of PUnit.{1} PUnit.unit), q = 1) ∧
      (∀ q : (∏ᶜ (fun _ : Empty =>
          FundamentalGroup.functor.obj (BasedTopCat.of PUnit.{1} PUnit.unit)) : GrpCat),
        q = 1) := by
  let X : Empty → BasedTopCat := fun _ => BasedTopCat.of PUnit.{1} PUnit.unit
  have htarget :
      ∀ q : (∏ᶜ (fun i => FundamentalGroup.functor.obj (X i)) : GrpCat), q = 1 := by
    intro q
    apply Concrete.limit_ext
      (Discrete.functor (fun i => FundamentalGroup.functor.obj (X i))) q 1
    intro i
    exact i.as.elim
  have hsource : ∀ q : FundamentalGroup.functor.obj (∏ᶜ X), q = 1 := by
    intro q
    apply ((asIso (piComparison FundamentalGroup.functor X)).groupIsoToMulEquiv).injective
    exact (htarget _).trans (map_one (piComparison FundamentalGroup.functor X).hom).symm
  exact ⟨(inferInstance : Subsingleton (FundamentalGroup PUnit.{1} PUnit.unit)),
    inferInstance, hsource, htarget⟩

end Circle
