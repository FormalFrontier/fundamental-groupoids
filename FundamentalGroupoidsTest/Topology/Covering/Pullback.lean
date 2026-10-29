/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.PullbackDoubleCoset
public import FundamentalGroupoidsTest.Topology.Covering.Monodromy
import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The periodic real pullback

The period-one quotient is pulled back along itself. Its points `(0,0)` and `(0,1)`
are separated by the continuous difference `y - x`. That difference has constant quotient
in the circle, so `AddCircle.isCoveringMap_coe` and `IsCoveringMap.const_of_comp` give
an obstruction to joining the two points.

The shared zero/one fiber data live in the monodromy examples. The positive loop
is the image of a straight zero-to-one real path.

An empty map to the same circle supplies the boundary: the stock covering definition has
no surjectivity requirement, and `IsCoveringMap.of_isEmpty` applies directly.
-/

@[expose] public section

noncomputable section

namespace PeriodOneCover

local notation "q" => ((↑) : ℝ → AddCircle (1 : ℝ))
local notation "G" => FundamentalGroup (AddCircle (1 : ℝ)) 0
local notation "H" =>
  MonoidHom.range (FundamentalGroup.mapOfEq
    (ContinuousMap.mk q (IsCoveringMap.continuous (AddCircle.isCoveringMap_coe (1 : ℝ))))
    (Subtype.property zeroPoint))

/-- The pullback point with real coordinates `(0,0)`. -/
def point00 : Function.Pullback q q :=
  ⟨(0, 0), by rfl⟩

/-- The pullback point with real coordinates `(0,1)`. -/
def point01 : Function.Pullback q q :=
  ⟨(0, 1), by
    exact (AddCircle.coe_zero (1 : ℝ)).trans (AddCircle.coe_period (1 : ℝ)).symm⟩

/-- The common-base projection, using the first coordinate. -/
def projection (z : Function.Pullback q q) : AddCircle (1 : ℝ) := q z.fst

/-- A real-valued separator defined on the stock product/subtype pullback. -/
def difference (z : Function.Pullback q q) : ℝ := z.snd - z.fst

/-- The double-coset dictionary uses the two covers and their origins. -/
def componentDoubleCoset : ZerothHomotopy (Function.Pullback q q) ≃
    DoubleCoset.Quotient (H : Set G) (H : Set G) :=
  (AddCircle.isCoveringMap_coe (1 : ℝ)).pullbackZerothHomotopyEquivDoubleCoset
    (AddCircle.isCoveringMap_coe (1 : ℝ)) 0 zeroPoint zeroPoint

/-- The first marked point has precisely its advertised coordinates. -/
private theorem point00_val : point00.val = (0, 0) := by
  rfl

/-- The second marked point has precisely its advertised coordinates. -/
private theorem point01_val : point01.val = (0, 1) := by
  rfl

/-- Both marked points lie over the specified zero basepoint. -/
private theorem marked_points_over_zero : projection point00 = 0 ∧ projection point01 = 0 := by
  exact ⟨AddCircle.coe_zero (1 : ℝ), AddCircle.coe_zero (1 : ℝ)⟩

/-- The model's projection is a covering by the two-cover common-base theorem. -/
private theorem projection_covering : IsCoveringMap projection := by
  exact (AddCircle.isCoveringMap_coe (1 : ℝ)).pullback_base
    (AddCircle.isCoveringMap_coe (1 : ℝ))

/-- The positive loop moves the zero lift to the unit lift for the real quotient covering. -/
private theorem positiveLoop_moves_zero :
    (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromy positiveLoop zeroPoint = onePoint := by
  apply (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromy_eq_of_map_eq (.mk positivePath)
  let γ := (Path.Homotopic.Quotient.mk positivePath).map
    ⟨q, (AddCircle.isCoveringMap_coe (1 : ℝ)).continuous⟩
  change γ = (γ.cast zeroPoint.property.symm onePoint.property.symm).cast
    zeroPoint.property onePoint.property
  exact ((γ.cast_cast zeroPoint.property.symm onePoint.property.symm
    zeroPoint.property onePoint.property).trans γ.cast_rfl_rfl).symm

/-- The separator is continuous in the inherited product/subtype topology. -/
private theorem continuous_difference : Continuous difference := by
  exact (continuous_snd.comp continuous_subtype_val).sub
    (continuous_fst.comp continuous_subtype_val)

/-- The separator has constant image under the quotient map. -/
private theorem difference_coe_zero (z : Function.Pullback q q) : q (difference z) = 0 := by
  change q (z.snd - z.fst) = 0
  have hz : q z.fst = q z.snd := z.property
  rw [AddCircle.coe_sub, hz, sub_self]

/-- The separator is an integer period. -/
private theorem difference_integer (z : Function.Pullback q q) :
    ∃ n : ℤ, n • (1 : ℝ) = difference z := by
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (difference_coe_zero z)

/-- Applying the real quotient's `const_of_comp` along a path preserves the separator. -/
private theorem joined_preserves_difference (x y : Function.Pullback q q) :
    Joined x y → difference x = difference y := by
  rintro ⟨γ⟩
  have h := (AddCircle.isCoveringMap_coe (1 : ℝ)).const_of_comp
    (continuous_difference.comp γ.continuous)
    (fun s t ↦ (difference_coe_zero (γ s)).trans (difference_coe_zero (γ t)).symm) 0 1
  simpa only [Function.comp_apply, γ.source, γ.target] using h

/-- The two fixed values of the separator are distinct. -/
private theorem difference_marked_points : difference point00 = 0 ∧ difference point01 = 1 := by
  exact ⟨sub_self (0 : ℝ), sub_zero (1 : ℝ)⟩

/-- Although both real factors and the circle are path-connected, these two pullback
points cannot be joined: their difference is invariant along every path. -/
private theorem not_joined : ¬ Joined point00 point01 := by
  intro h
  have heq := joined_preserves_difference point00 point01 h
  rw [difference_marked_points.1, difference_marked_points.2] at heq
  exact zero_ne_one heq

/-- The two marked points determine genuinely different path components. -/
private theorem components_ne : ZerothHomotopy.mk point00 ≠ ZerothHomotopy.mk point01 := by
  intro h
  exact not_joined (Quotient.exact h)

/-- The pullback is not path-connected. -/
private theorem not_pathConnected : ¬ PathConnectedSpace (Function.Pullback q q) := by
  intro h
  let := h
  exact not_joined (PathConnectedSpace.joined point00 point01)

/-- The component `(0,1)` corresponds to the positive loop's double coset, not its inverse. -/
private theorem componentDoubleCoset_point01 :
    componentDoubleCoset (ZerothHomotopy.mk point01) = DoubleCoset.mk H H positiveLoop := by
  have hone : (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromy (1 : G) zeroPoint =
      zeroPoint :=
    congr_fun ((AddCircle.isCoveringMap_coe (1 : ℝ)).monodromy_refl
      (x := (0 : AddCircle (1 : ℝ)))) zeroPoint
  have hpoint : ((Function.Pullback.fiberEquiv q q 0).symm
      (zeroPoint, onePoint)).val = point01 := by
    apply Subtype.ext
    rfl
  simpa only [componentDoubleCoset, hone, positiveLoop_moves_zero, hpoint, inv_one, one_mul]
    using (AddCircle.isCoveringMap_coe (1 : ℝ)).pullbackZerothHomotopyEquivDoubleCoset_apply
      (AddCircle.isCoveringMap_coe (1 : ℝ)) 0 zeroPoint zeroPoint (1 : G) positiveLoop

/-- The inverse dictionary returns the component of the point `(0,1)`. -/
private theorem componentDoubleCoset_symm_positiveLoop :
    componentDoubleCoset.symm (DoubleCoset.mk H H positiveLoop) =
      ZerothHomotopy.mk point01 := by
  unfold componentDoubleCoset
  rw [IsCoveringMap.pullbackZerothHomotopyEquivDoubleCoset_symm_apply, positiveLoop_moves_zero]
  apply congrArg ZerothHomotopy.mk
  apply Subtype.ext
  rfl

/-- Monodromy acts on the zero fiber of the period-one covering. -/
noncomputable local instance fiberMonodromyAction : MulAction G (q ⁻¹' {0}) :=
  (AddCircle.isCoveringMap_coe (1 : ℝ)).fundamentalGroupMulAction 0

/-- The diagonal orbit of the zero and unit lifts maps to the component of `(0,1)`. -/
private theorem productOrbitComponents_zero_one :
    (AddCircle.isCoveringMap_coe (1 : ℝ)).pullbackProdOrbitEquivZerothHomotopy
      (AddCircle.isCoveringMap_coe (1 : ℝ)) 0
      (Quotient.mk (MulAction.orbitRel G ((q ⁻¹' {0}) × (q ⁻¹' {0})))
        (zeroPoint, onePoint)) = ZerothHomotopy.mk point01 := by
  rw [IsCoveringMap.pullbackProdOrbitEquivZerothHomotopy_apply_mk]
  apply congrArg ZerothHomotopy.mk
  apply Subtype.ext
  rfl

/-- The map from the empty space to the circle. -/
def emptyProjection : Empty → AddCircle (1 : ℝ) := Empty.elim

/-- Monodromy acts on the empty fiber of the empty covering. -/
noncomputable local instance emptyFiberMonodromyAction :
    MulAction G (emptyProjection ⁻¹' {0}) :=
  (IsCoveringMap.of_isEmpty emptyProjection).fundamentalGroupMulAction 0

/-- The diagonal fiber orbits of the pullback with the empty cover correspond to its
path components. -/
def emptyOrbitComponents :
    MulAction.orbitRel.Quotient G ((emptyProjection ⁻¹' {0}) × (q ⁻¹' {0})) ≃
      ZerothHomotopy (emptyProjection.Pullback q) :=
  (IsCoveringMap.of_isEmpty emptyProjection).pullbackProdOrbitEquivZerothHomotopy
    (AddCircle.isCoveringMap_coe (1 : ℝ)) 0

/-- Its common-base fiber is empty. -/
private theorem empty_pullback_fiber :
    IsEmpty ((fun z : emptyProjection.Pullback q ↦ emptyProjection z.fst) ⁻¹' {0}) := by
  exact ⟨fun e ↦ Empty.elim e.val.fst⟩

/-- There are no path components to discard in the empty-cover comparison. -/
private theorem empty_components : IsEmpty (ZerothHomotopy (emptyProjection.Pullback q)) := by
  refine ⟨fun c ↦ ?_⟩
  obtain ⟨z, _⟩ := ZerothHomotopy.mk_surjective c
  exact Empty.elim z.fst

end PeriodOneCover
