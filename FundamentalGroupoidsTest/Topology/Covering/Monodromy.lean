/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Monodromy
import FundamentalGroupoids.Topology.Covering.Components
import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Instances.ZMultiples

/-!
# Examples for covering-space monodromy

The quotient `ℝ → AddCircle (1 : ℝ)` has distinct points in its zero fiber joined by a path
in `ℝ`. Its monodromy therefore has a moving loop, outside the image of the fundamental
group of `ℝ`. The covering map and the discreteness of the integer-period subgroup are
provided by Mathlib's prior formalizations in `Mathlib.Topology.Covering.AddCircle` and
`Mathlib.Topology.Instances.ZMultiples`. The projection of the straight path from zero to one
moves the zero fiber point to the unit-translate point. The fiber–coset equivalence sends its
coset to that endpoint, distinct from the image of the identity coset.

The discrete two-point trivial covering `Bool × Unit → Unit` has two distinct monodromy
orbits. Thus a connected base, even a point, does not by itself imply transitivity.
-/

@[expose] public section

namespace PeriodOneCover

/-- The zero point in the period-one quotient's zero fiber. -/
def zeroPoint : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0} :=
  ⟨0, AddCircle.coe_zero _⟩

/-- The unit-translate point in the same fiber. -/
def onePoint : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0} :=
  ⟨1, AddCircle.coe_period _⟩

/-- The straight real path from zero to one, before quotienting. -/
noncomputable def positivePath : Path (0 : ℝ) 1 := Path.segment 0 1

/-- The positive loop is the image of the zero-to-one real path, with endpoints
cast to the zero basepoint. -/
noncomputable def positiveLoop : FundamentalGroup (AddCircle (1 : ℝ)) 0 :=
  ((Path.Homotopic.Quotient.mk positivePath).map
    ⟨((↑) : ℝ → AddCircle (1 : ℝ)), (AddCircle.isCoveringMap_coe (1 : ℝ)).continuous⟩).cast
      (by exact (AddCircle.coe_zero (1 : ℝ)).symm)
      (by exact (AddCircle.coe_period (1 : ℝ)).symm)

/-- The positive loop lifts from zero to one in the real covering. -/
private theorem positiveLoop_monodromy :
    (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromy positiveLoop zeroPoint = onePoint := by
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let γ := (Path.Homotopic.Quotient.mk positivePath).map
    ⟨((↑) : ℝ → AddCircle (1 : ℝ)), cov.continuous⟩
  apply cov.monodromy_eq_of_map_eq (.mk positivePath)
  exact ((γ.cast_cast zeroPoint.property.symm onePoint.property.symm
    zeroPoint.property onePoint.property).trans γ.cast_rfl_rfl).symm

/-- The positive-loop coset and the identity coset have distinct images under the
fiber–coset equivalence: their real coordinates are one and zero, respectively. -/
private theorem monodromyQuotientEquiv_endpoints :
    (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromyQuotientEquiv 0 zeroPoint
        (QuotientGroup.mk positiveLoop) = onePoint ∧
      (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromyQuotientEquiv 0 zeroPoint
        (QuotientGroup.mk (1 : FundamentalGroup (AddCircle (1 : ℝ)) 0)) = zeroPoint ∧
      (QuotientGroup.mk positiveLoop : FundamentalGroup (AddCircle (1 : ℝ)) 0 ⧸
        (FundamentalGroup.mapOfEq
          ⟨((↑) : ℝ → AddCircle (1 : ℝ)), (AddCircle.isCoveringMap_coe (1 : ℝ)).continuous⟩
          zeroPoint.property).range) ≠
        QuotientGroup.mk (1 : FundamentalGroup (AddCircle (1 : ℝ)) 0) := by
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  have hpos : cov.monodromyQuotientEquiv 0 zeroPoint
      (QuotientGroup.mk positiveLoop) = onePoint := by
    rw [cov.monodromyQuotientEquiv_apply_mk, positiveLoop_monodromy]
  have hzero : cov.monodromyQuotientEquiv 0 zeroPoint
      (QuotientGroup.mk (1 : FundamentalGroup (AddCircle (1 : ℝ)) 0)) = zeroPoint := by
    rw [cov.monodromyQuotientEquiv_apply_mk]
    exact congr_fun cov.monodromy_refl zeroPoint
  refine ⟨hpos, hzero, ?_⟩
  intro h
  have hend := congrArg (cov.monodromyQuotientEquiv 0 zeroPoint) h
  rw [hpos, hzero] at hend
  exact one_ne_zero (congrArg Subtype.val hend)

end PeriodOneCover

/-- The period-one real quotient has a moving monodromy element, which does not come from a
loop in the total space based at its starting point. -/
private theorem realCircle_exists_moving_monodromy :
    ∃ (e e' : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0})
      (γ : FundamentalGroup (AddCircle (1 : ℝ)) 0),
      e ≠ e' ∧ (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromy γ e = e' ∧
        γ ∉ (FundamentalGroup.mapOfEq
          ⟨((↑) : ℝ → AddCircle (1 : ℝ)), (AddCircle.isCoveringMap_coe (1 : ℝ)).continuous⟩
          e.2).range := by
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  let e := PeriodOneCover.zeroPoint
  let e' := PeriodOneCover.onePoint
  have hne : e ≠ e' := by
    intro h
    exact zero_ne_one (congrArg Subtype.val h)
  have hγ : cov.monodromy PeriodOneCover.positiveLoop e = e' :=
    PeriodOneCover.positiveLoop_monodromy
  refine ⟨e, e', PeriodOneCover.positiveLoop, hne, hγ, ?_⟩
  intro hmem
  have hfix := (cov.monodromy_eq_self_iff_mem_range e PeriodOneCover.positiveLoop).mpr hmem
  exact hne (hfix.symm.trans hγ)

/-- The real circle covering has path-connected total and base spaces, pretransitive
canonical monodromy, and a moving element outside the total-space fundamental-group image. -/
private theorem realCircle_pathConnected_pretransitive_moving_monodromy :
    PathConnectedSpace ℝ ∧ PathConnectedSpace (AddCircle (1 : ℝ)) ∧
      @MulAction.IsPretransitive (FundamentalGroup (AddCircle (1 : ℝ)) 0)
        (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0})
        ((AddCircle.isCoveringMap_coe (1 : ℝ)).fundamentalGroupMulAction
          0).toSemigroupAction.toSMul ∧
      ∃ (e e' : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0})
        (γ : FundamentalGroup (AddCircle (1 : ℝ)) 0),
        e ≠ e' ∧ (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromy γ e = e' ∧
          γ ∉ (FundamentalGroup.mapOfEq
            ⟨((↑) : ℝ → AddCircle (1 : ℝ)), (AddCircle.isCoveringMap_coe (1 : ℝ)).continuous⟩
            e.2).range := by
  refine ⟨inferInstance, ?_, ?_, realCircle_exists_moving_monodromy⟩
  · exact QuotientAddGroup.mk_surjective.pathConnectedSpace
      (AddCircle.isCoveringMap_coe (1 : ℝ)).continuous
  · exact (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromy_isPretransitive 0

/-- Pretransitivity of the real circle covering recovers path connectedness of its total space. -/
example : PathConnectedSpace ℝ := by
  have : PathConnectedSpace (AddCircle (1 : ℝ)) :=
    realCircle_pathConnected_pretransitive_moving_monodromy.2.1
  exact (AddCircle.isCoveringMap_coe (1 : ℝ)).pathConnectedSpace_of_monodromy_isPretransitive
    0 realCircle_pathConnected_pretransitive_moving_monodromy.2.2.1

/-- The empty-aware path-connectedness criterion specializes to the real circle covering. -/
example : PathConnectedSpace ℝ ↔ Nonempty ℝ ∧
    @MulAction.IsPretransitive (FundamentalGroup (AddCircle (1 : ℝ)) 0)
      (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0})
      ((AddCircle.isCoveringMap_coe (1 : ℝ)).fundamentalGroupMulAction
        0).toSemigroupAction.toSMul := by
  have : PathConnectedSpace (AddCircle (1 : ℝ)) :=
    realCircle_pathConnected_pretransitive_moving_monodromy.2.1
  exact IsCoveringMap.pathConnectedSpace_iff_nonempty_and_monodromy_isPretransitive
    (AddCircle.isCoveringMap_coe (1 : ℝ)) 0

/-- Distinct lifts moved by circle monodromy have the same component image. -/
private theorem realCircle_exists_distinct_lifts_same_component_image :
    ∃ e e' : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0}, e ≠ e' ∧
      (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromyOrbitEquivZerothHomotopy 0
        (hB := realCircle_pathConnected_pretransitive_moving_monodromy.2.1) ⟦e⟧ =
      (AddCircle.isCoveringMap_coe (1 : ℝ)).monodromyOrbitEquivZerothHomotopy 0
        (hB := realCircle_pathConnected_pretransitive_moving_monodromy.2.1) ⟦e'⟧ := by
  let cov := AddCircle.isCoveringMap_coe (1 : ℝ)
  have : PathConnectedSpace (AddCircle (1 : ℝ)) :=
    realCircle_pathConnected_pretransitive_moving_monodromy.2.1
  obtain ⟨e, e', γ, hne, hγ, _⟩ := realCircle_exists_moving_monodromy
  refine ⟨e, e', hne, ?_⟩
  simp only [IsCoveringMap.monodromyOrbitEquivZerothHomotopy_apply]
  exact Quotient.sound ((cov.exists_monodromy_eq_iff_joined e e').mp ⟨γ, hγ⟩)

/-- A two-point discrete fiber over a point need not be a single monodromy orbit. -/
private theorem discreteCover_exists_distinct_monodromy_orbits :
    ∃ e e' : (Prod.snd : Bool × Unit → Unit) ⁻¹' {()},
      ¬ ∃ γ : FundamentalGroup Unit (),
        (IsCoveringMap.of_discreteTopology (Prod.snd : Bool × Unit → Unit)).monodromy γ e = e' := by
  let cov := IsCoveringMap.of_discreteTopology (Prod.snd : Bool × Unit → Unit)
  let e : (Prod.snd : Bool × Unit → Unit) ⁻¹' {()} := ⟨(false, ()), rfl⟩
  let e' : (Prod.snd : Bool × Unit → Unit) ⁻¹' {()} := ⟨(true, ()), rfl⟩
  refine ⟨e, e', ?_⟩
  intro h
  obtain ⟨Γ⟩ := (cov.exists_monodromy_eq_iff_joined e e').mp h
  have heq := cov.const_of_comp Γ.continuous (fun _ _ ↦ Subsingleton.elim _ _) 0 1
  have hbad : false = true := congrArg Prod.fst (Γ.source.symm.trans (heq.trans Γ.target))
  cases hbad

/-- The two-sheet covering has a path-connected base and an occupied raw fiber, but its
canonical monodromy is not pretransitive and its total space is not path-connected. -/
private theorem discreteCover_not_pretransitive_not_pathConnected :
    PathConnectedSpace Unit ∧ Nonempty ((Prod.snd : Bool × Unit → Unit) ⁻¹' {()}) ∧
      ¬ @MulAction.IsPretransitive (FundamentalGroup Unit ())
        ((Prod.snd : Bool × Unit → Unit) ⁻¹' {()})
        ((IsCoveringMap.of_discreteTopology
          (Prod.snd : Bool × Unit → Unit)).fundamentalGroupMulAction ()).toSemigroupAction.toSMul ∧
      ¬ PathConnectedSpace (Bool × Unit) := by
  obtain ⟨e, e', hne⟩ := discreteCover_exists_distinct_monodromy_orbits
  refine ⟨⟨⟨()⟩, ?_⟩, ⟨e⟩, ?_, ?_⟩
  · intro x y
    cases x
    cases y
    exact ⟨Path.refl ()⟩
  · intro h
    exact hne (h.exists_smul_eq e e')
  · intro h
    have := h
    exact hne ((IsCoveringMap.exists_monodromy_eq_iff_joined
      (IsCoveringMap.of_discreteTopology (Prod.snd : Bool × Unit → Unit)) e e').mpr
      (PathConnectedSpace.joined _ _))

/-- The two distinct monodromy orbits of the two-sheet cover have distinct component images. -/
private theorem discreteCover_exists_distinct_component_images :
    ∃ e e' : (Prod.snd : Bool × Unit → Unit) ⁻¹' {()},
      (IsCoveringMap.of_discreteTopology
        (Prod.snd : Bool × Unit → Unit)).monodromyOrbitEquivZerothHomotopy ()
          (hB := discreteCover_not_pretransitive_not_pathConnected.1) ⟦e⟧ ≠
      (IsCoveringMap.of_discreteTopology
        (Prod.snd : Bool × Unit → Unit)).monodromyOrbitEquivZerothHomotopy ()
          (hB := discreteCover_not_pretransitive_not_pathConnected.1) ⟦e'⟧ := by
  let cov := IsCoveringMap.of_discreteTopology (Prod.snd : Bool × Unit → Unit)
  have : PathConnectedSpace Unit := discreteCover_not_pretransitive_not_pathConnected.1
  obtain ⟨e, e', hne⟩ := discreteCover_exists_distinct_monodromy_orbits
  refine ⟨e, e', ?_⟩
  intro h
  have hq := (cov.monodromyOrbitEquivZerothHomotopy ()).injective h
  exact hne (Quotient.exact hq.symm)
