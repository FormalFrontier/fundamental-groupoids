/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Equivalence
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.ZMultiples

/-!
# Examples for based equivalences of covering spaces

The period-one quotient `ℝ → AddCircle (1 : ℝ)` has points `0` and `1` over the same
basepoint. Both induced fundamental-group images are trivial, since `ℝ` is simply connected.
The based equivalence taking `0` to `1` is translation by `1`, not the identity.

For a component boundary, the identity cover of `Unit` and the two-point trivial cover
`Bool × Unit → Unit` have equal images in the fundamental group of `Unit`. But inclusion
into the false component is not surjective, and the two total spaces are not homeomorphic.
Thus target path connectedness is essential to both conclusions.
-/

@[expose] public section

private abbrev realCircleCover := AddCircle.isCoveringMap_coe (1 : ℝ)

private theorem realCircle_basepoint :
    ((0 : ℝ) : AddCircle (1 : ℝ)) = ((1 : ℝ) : AddCircle (1 : ℝ)) := by
  rw [AddCircle.coe_zero, AddCircle.coe_period]

private theorem realCircle_ranges :
    (FundamentalGroup.map ⟨((↑) : ℝ → AddCircle (1 : ℝ)), realCircleCover.continuous⟩ 0).range = ⊥ ∧
      (FundamentalGroup.mapOfEq
        ⟨((↑) : ℝ → AddCircle (1 : ℝ)), realCircleCover.continuous⟩
        realCircle_basepoint.symm).range = ⊥ := by
  constructor <;> apply MonoidHom.range_eq_bot_iff.mpr <;>
    apply MonoidHom.ext <;> intro γ <;> change _ = 1 <;>
    rw [Subsingleton.elim γ 1, map_one]

private theorem realCircle_rangeEq :
    (FundamentalGroup.map ⟨((↑) : ℝ → AddCircle (1 : ℝ)), realCircleCover.continuous⟩ 0).range =
      (FundamentalGroup.mapOfEq
        ⟨((↑) : ℝ → AddCircle (1 : ℝ)), realCircleCover.continuous⟩
        realCircle_basepoint.symm).range :=
  realCircle_ranges.1.trans realCircle_ranges.2.symm

/-- Translation by one is a continuous map over the period-one circle cover, so the
cover-morphism surjectivity statement applies. -/
private theorem realCircle_add_one_surjective : Function.Surjective (fun t : ℝ ↦ t + 1) := by
  apply realCircleCover.surjective_of_comp_eq realCircleCover
    ⟨fun t ↦ t + 1, continuous_id.add continuous_const⟩
  funext t
  exact AddCircle.coe_add_period (1 : ℝ) t

/-- The characterization of the based equivalence identifies it with translation by one. -/
private theorem realCircle_homeomorphOfRangeEq_eq_addRight_one :
    realCircleCover.homeomorphOfRangeEq realCircleCover 0 1 realCircle_basepoint
    realCircle_rangeEq = Homeomorph.addRight (1 : ℝ) := by
  have h := (realCircleCover.homeomorphOfRangeEq_eq_iff realCircleCover 0 1
    realCircle_basepoint realCircle_rangeEq (Homeomorph.addRight (1 : ℝ) : C(ℝ, ℝ))).mpr
    ⟨by funext t; exact AddCircle.coe_add_period (1 : ℝ) t, by simp⟩
  exact Homeomorph.ext (fun t ↦ DFunLike.congr_fun h t)

/-- Equal based images do not control other components of a total space. The same example
also prevents dropping target path connectedness from cover-morphism surjectivity. -/
private theorem discreteCover_equal_ranges_not_surjective_not_homeomorphic :
    let g : C(Unit, Bool × Unit) := ⟨fun _ ↦ (false, ()), continuous_const⟩
    IsCoveringMap (id : Unit → Unit) ∧
      IsCoveringMap (Prod.snd : Bool × Unit → Unit) ∧
      Prod.snd ∘ g = (id : Unit → Unit) ∧
      (FundamentalGroup.map ⟨(id : Unit → Unit), continuous_id⟩ ()).range =
        (FundamentalGroup.mapOfEq (x := (false, ()))
          ⟨(Prod.snd : Bool × Unit → Unit), continuous_snd⟩
          (show Prod.snd (false, ()) = (id : Unit → Unit) () from rfl)).range ∧
      ¬ Function.Surjective g ∧ ¬ Nonempty (Unit ≃ₜ Bool × Unit) := by
  dsimp only
  refine ⟨IsCoveringMap.of_discreteTopology _, IsCoveringMap.of_discreteTopology _,
    rfl, Subsingleton.elim _ _, ?_, ?_⟩
  · intro h
    obtain ⟨u, hu⟩ := h (true, ())
    have hbad : false = true := congrArg Prod.fst hu
    cases hbad
  · rintro ⟨H⟩
    have hbad : (false, ()) = (true, ()) := by
      calc
        (false, ()) = H (H.symm (false, ())) := (H.apply_symm_apply _).symm
        _ = H (H.symm (true, ())) := congrArg H (Subsingleton.elim _ _)
        _ = (true, ()) := H.apply_symm_apply _
    cases congrArg Prod.fst hbad
