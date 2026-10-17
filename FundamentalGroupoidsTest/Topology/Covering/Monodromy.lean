/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Monodromy
import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.ZMultiples

/-!
# Examples for covering-space monodromy

The quotient `ℝ → AddCircle (1 : ℝ)` has distinct points in its zero fiber joined by a path
in `ℝ`. Its monodromy therefore has a moving loop, outside the image of the fundamental
group of `ℝ`. The covering map and the discreteness of the integer-period subgroup are
provided by Mathlib's prior formalizations in `Mathlib.Topology.Covering.AddCircle` and
`Mathlib.Topology.Instances.ZMultiples`.

The discrete two-point trivial covering `Bool × Unit → Unit` has two distinct monodromy
orbits. Thus a connected base, even a point, does not by itself imply transitivity.
-/

@[expose] public section

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
  let e : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0} := ⟨0, AddCircle.coe_zero _⟩
  let e' : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' {0} := ⟨1, AddCircle.coe_period _⟩
  have hne : e ≠ e' := by
    intro h
    exact zero_ne_one (congrArg Subtype.val h)
  obtain ⟨γ, hγ⟩ := (cov.exists_monodromy_eq_iff_joined e e').mpr
    (PathConnectedSpace.joined _ _)
  refine ⟨e, e', γ, hne, hγ, ?_⟩
  intro hmem
  have hfix := (cov.monodromy_eq_self_iff_mem_range e γ).mpr hmem
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
