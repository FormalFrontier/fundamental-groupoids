/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Covering.Proper
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.Order.Compact

/-!
# Properness of finite-sheeted product coverings

The two-sheeted projection `Fin 2 × ℝ → ℝ` is a covering map, obtained from Mathlib's
trivial bundle by its product homeomorphism. The finite-fiber characterization gives its
properness, and the compact-preimage theorem gives compactness over the interval `[0, 1]`.

Identity and empty-domain projections illustrate singleton and empty fibers. The discrete
projection `ℕ × PUnit → PUnit` is a covering map that is not proper.
-/

private theorem discreteProductProjection_covering
    {F : Type*} {B : Type*} [TopologicalSpace F] [DiscreteTopology F]
    [TopologicalSpace B] : IsCoveringMap (Prod.snd : F × B → B) := by
  have h : IsCoveringMap
      (Bundle.TotalSpace.proj : Bundle.TotalSpace F (Bundle.Trivial B F) → B) :=
    FiberBundle.isCoveringMap (F := F) (E := Bundle.Trivial B F)
  exact (h.comp_homeomorph (Bundle.Trivial.homeomorphProd B F).symm).comp_homeomorph
    (Homeomorph.prodComm F B)

private theorem twoSheetFiber_finite (y : ℝ) :
    Finite ((Prod.snd : Fin 2 × ℝ → ℝ) ⁻¹' {y}) := by
  refine Finite.of_injective (fun x : (Prod.snd : Fin 2 × ℝ → ℝ) ⁻¹' {y} ↦ x.val.1) ?_
  intro x x' h
  apply Subtype.ext
  exact Prod.ext h ((show x.val.2 = y from x.property).trans
    (show x'.val.2 = y from x'.property).symm)

private theorem twoSheetProjection_proper : IsProperMap (Prod.snd : Fin 2 × ℝ → ℝ) :=
  (discreteProductProjection_covering (F := Fin 2) (B := ℝ)).isProperMap_iff_finite_fibers.mpr
    twoSheetFiber_finite

/-- The inverse image of the closed unit interval in the two-sheeted real cover is compact. -/
example : IsCompact ((Prod.snd : Fin 2 × ℝ → ℝ) ⁻¹' Set.Icc (0 : ℝ) 1) :=
  twoSheetProjection_proper.isCompact_preimage isCompact_Icc

/-- The identity cover has finite singleton fibers. -/
example : IsProperMap (id : ℝ → ℝ) := by
  have hp : IsCoveringMap (id : ℝ → ℝ) :=
    (discreteProductProjection_covering (F := PUnit.{1}) (B := ℝ)).comp_homeomorph
      (Homeomorph.punitProd ℝ).symm
  exact hp.isProperMap_iff_finite_fibers.mpr fun y ↦ Set.finite_singleton y

/-- An empty-sheet covering of the real line is proper without being surjective. -/
example : IsProperMap (Prod.snd : Empty × ℝ → ℝ) ∧
    ¬ Function.Surjective (Prod.snd : Empty × ℝ → ℝ) := by
  have hp : IsCoveringMap (Prod.snd : Empty × ℝ → ℝ) := IsCoveringMap.of_isEmpty _
  refine ⟨hp.isProperMap_iff_finite_fibers.mpr (fun _ ↦ inferInstance), ?_⟩
  intro h
  obtain ⟨⟨e, _⟩, _⟩ := h 0
  cases e

/-- Infinitely many discrete sheets over a point prevent properness. -/
example : ¬ IsProperMap (Prod.snd : ℕ × PUnit → PUnit) := by
  intro h
  have hp := discreteProductProjection_covering (F := ℕ) (B := PUnit)
  have : Finite ((Prod.snd : ℕ × PUnit → PUnit) ⁻¹' {PUnit.unit}) :=
    (hp.isProperMap_iff_finite_fibers.mp h) PUnit.unit
  have : Finite ℕ := Finite.of_injective
    (fun n : ℕ ↦
      (⟨(n, PUnit.unit), rfl⟩ : (Prod.snd : ℕ × PUnit → PUnit) ⁻¹' {PUnit.unit}))
    (by
      intro m n hmn
      exact congrArg (fun x : (Prod.snd : ℕ × PUnit → PUnit) ⁻¹' {PUnit.unit} ↦ x.val.1) hmn)
  exact not_finite ℕ
