/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Covering.Cardinality
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.Order.IntermediateValue

/-!
# Cardinalities of infinite and empty covering fibers

The trivial bundle with natural-number sheets over the real line is a covering map.
Its point fibers are homeomorphic to `ℕ`, so their cardinality is `ℵ₀`. The local-constancy
statement specializes to this covering, and its stock preconnectedness consequence compares
the fibers over zero and one.

The constant-false map `Bool → Bool` is a covering of discrete spaces. Its fibers over
`false` and `true` have cardinalities two and zero, respectively. Thus local constancy does
not imply global constancy on a disconnected base.

The coverings, topologies, and point-fiber comparisons use Mathlib's trivial-bundle and
discrete-covering constructions.
-/

open scoped Cardinal

private abbrev natSheetProjection : Bundle.TotalSpace ℕ (Bundle.Trivial ℝ ℕ) → ℝ :=
  Bundle.TotalSpace.proj

private theorem natSheetProjection_covering : IsCoveringMap natSheetProjection :=
  FiberBundle.isCoveringMap (F := ℕ) (E := Bundle.Trivial ℝ ℕ)

private abbrev natSheetFiberHomeomorph (b : ℝ) : natSheetProjection ⁻¹' {b} ≃ₜ ℕ :=
  (Bundle.Trivial.trivialization ℝ ℕ).preimageSingletonHomeomorph (Set.mem_univ b)

private theorem natSheetFiberHomeomorph_apply (b : ℝ) (e : natSheetProjection ⁻¹' {b}) :
    natSheetFiberHomeomorph b e = e.val.2 :=
  (Bundle.Trivial.trivialization ℝ ℕ).preimageSingletonHomeomorph_apply (Set.mem_univ b) e

private theorem natSheetFiberHomeomorph_symm_apply (b : ℝ) (n : ℕ) :
    ((natSheetFiberHomeomorph b).symm n).val =
      (⟨b, n⟩ : Bundle.TotalSpace ℕ (Bundle.Trivial ℝ ℕ)) := by
  have h := congrArg Subtype.val
    ((Bundle.Trivial.trivialization ℝ ℕ).preimageSingletonHomeomorph_symm_apply
      (Set.mem_univ b) n)
  exact h.trans (Bundle.Trivial.toOpenPartialHomeomorph_trivialization_symm_apply ℝ ℕ (b, n))

private theorem natSheetFiber_cardinalMk (b : ℝ) :
    Cardinal.mk (natSheetProjection ⁻¹' {b}) = ℵ₀ :=
  (Cardinal.mk_congr (natSheetFiberHomeomorph b).toEquiv).trans Cardinal.mk_nat

/-- Local constancy applies to the covering with countably infinite fibers. -/
private theorem natSheetFiber_cardinalMk_isLocallyConstant :
    IsLocallyConstant (fun b : ℝ ↦ Cardinal.mk (natSheetProjection ⁻¹' {b})) :=
  natSheetProjection_covering.isLocallyConstant_cardinalMk_fiber

/-- Preconnectedness of the real line makes the fiber cardinalities over zero and one equal. -/
example : Cardinal.mk (natSheetProjection ⁻¹' {(0 : ℝ)}) =
    Cardinal.mk (natSheetProjection ⁻¹' {(1 : ℝ)}) :=
  natSheetFiber_cardinalMk_isLocallyConstant.apply_eq_of_preconnectedSpace 0 1

private abbrev boolFalseProjection : Bool → Bool := fun _ ↦ false

private theorem boolFalseProjection_covering : IsCoveringMap boolFalseProjection :=
  IsCoveringMap.of_discreteTopology _

private abbrev boolFalseFiberEquiv : boolFalseProjection ⁻¹' {false} ≃ Bool :=
  Equiv.subtypeUnivEquiv fun _ ↦ rfl

private theorem boolFalseProjection_preimage_true :
    boolFalseProjection ⁻¹' {true} = (∅ : Set Bool) := by
  ext b
  simp

private abbrev boolTrueFiberEquiv : boolFalseProjection ⁻¹' {true} ≃ Empty :=
  (Set.equivOfEq boolFalseProjection_preimage_true).trans (Equiv.Set.empty Bool)

private theorem boolFalseFiber_cardinalMk :
    Cardinal.mk (boolFalseProjection ⁻¹' {false}) = 2 :=
  (Cardinal.mk_congr boolFalseFiberEquiv).trans Cardinal.mk_bool

private theorem boolTrueFiber_cardinalMk :
    Cardinal.mk (boolFalseProjection ⁻¹' {true}) = 0 :=
  (Cardinal.mk_congr boolTrueFiberEquiv).trans Cardinal.mk_empty

/-- The two fiber cardinalities differ, despite the map being a covering. -/
private theorem boolFiber_cardinalMk_ne :
    Cardinal.mk (boolFalseProjection ⁻¹' {false}) ≠
      Cardinal.mk (boolFalseProjection ⁻¹' {true}) := by
  rw [boolFalseFiber_cardinalMk, boolTrueFiber_cardinalMk]
  exact two_ne_zero
