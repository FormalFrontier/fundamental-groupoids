/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Covering.FiniteIndex
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.FiberBundle.Constructions
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Properness of finite-sheeted product coverings

The two-sheeted projection `Fin 2 × ℝ → ℝ` is a covering map, obtained from Mathlib's
trivial bundle by its product homeomorphism. Its finite-fiber predicate is locally constant,
with clopen locus equal to the whole real line. Preconnectedness of the base makes finiteness
over the given point zero sufficient for properness, and the compact-preimage theorem gives
compactness over the interval `[0, 1]`.

The identity real cover uses the preconnected-total-space fiber criterion to prove properness
and the based fundamental-group criterion to deduce finite index. The constant-false cover
`PUnit → Bool` has connected total space, a singleton based fiber, an empty other fiber and a
clopen, nonsurjective image. Thus the total-space criterion needs no connectedness of the base
or surjectivity.

An empty-domain projection illustrates empty fibers. The discrete projection
`ℕ × PUnit → PUnit` is a covering map that is not proper.
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

/-- The generic API compares finiteness throughout any preconnected subset of the real line. -/
example {s : Set ℝ} (hs : IsPreconnected s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    Finite ((Prod.snd : Fin 2 × ℝ → ℝ) ⁻¹' {x}) =
      Finite ((Prod.snd : Fin 2 × ℝ → ℝ) ⁻¹' {y}) := by
  have hp := discreteProductProjection_covering (F := Fin 2) (B := ℝ)
  exact hp.isLocallyConstant_finite_fiber.apply_eq_of_isPreconnected hs hx hy

/-- The clopen finite-fiber locus contains every point of the real line. -/
example : IsClopen {y : ℝ | Finite ((Prod.snd : Fin 2 × ℝ → ℝ) ⁻¹' {y})} ∧
    {y : ℝ | Finite ((Prod.snd : Fin 2 × ℝ → ℝ) ⁻¹' {y})} = Set.univ := by
  have hp := discreteProductProjection_covering (F := Fin 2) (B := ℝ)
  refine ⟨hp.isClopen_setOf_finite_fiber, ?_⟩
  ext y
  simp [twoSheetFiber_finite]

private theorem twoSheetProjection_proper : IsProperMap (Prod.snd : Fin 2 × ℝ → ℝ) := by
  have hp := discreteProductProjection_covering (F := Fin 2) (B := ℝ)
  exact (hp.isProperMap_iff_finite_fiber 0).mpr (twoSheetFiber_finite 0)

/-- The inverse image of the closed unit interval in the two-sheeted real cover is compact. -/
example : IsCompact ((Prod.snd : Fin 2 × ℝ → ℝ) ⁻¹' Set.Icc (0 : ℝ) 1) :=
  twoSheetProjection_proper.isCompact_preimage isCompact_Icc

private theorem realIdentity_covering : IsCoveringMap (id : ℝ → ℝ) :=
  (discreteProductProjection_covering (F := PUnit.{1}) (B := ℝ)).comp_homeomorph
    (Homeomorph.punitProd ℝ).symm

/-- The identity real cover is proper by its singleton fiber and preconnected total space. -/
private theorem realIdentity_proper : IsProperMap (id : ℝ → ℝ) :=
  (realIdentity_covering.isProperMap_iff_finite_fiber_of_preconnectedSpace 0).mpr
    (Set.finite_singleton 0)

/-- Properness of the identity real cover gives finite index for its induced based image. -/
private theorem realIdentity_finiteIndex :
    (FundamentalGroup.map ⟨(id : ℝ → ℝ), realIdentity_covering.continuous⟩ 0).range.FiniteIndex :=
  (realIdentity_covering.isProperMap_iff_finiteIndex 0).mp realIdentity_proper

private abbrev pointToBool : PUnit → Bool := fun _ ↦ false

private theorem pointToBool_covering : IsCoveringMap pointToBool :=
  IsCoveringMap.of_discreteTopology _

/-- A connected total space can cover just one clopen component of a disconnected base. -/
private theorem pointToBool_boundary :
    ConnectedSpace PUnit ∧ IsProperMap pointToBool ∧
      pointToBool ⁻¹' {false} = {PUnit.unit} ∧ pointToBool ⁻¹' {true} = ∅ ∧
      IsClopen (Set.range pointToBool) ∧ ¬ Function.Surjective pointToBool := by
  refine ⟨inferInstance,
    (pointToBool_covering.isProperMap_iff_finite_fiber_of_preconnectedSpace PUnit.unit).mpr
      inferInstance, ?_, ?_, ?_, ?_⟩
  · ext x
    simp
  · ext x
    simp
  · exact ⟨isClosed_discrete _, isOpen_discrete _⟩
  · intro h
    obtain ⟨x, hx⟩ := h true
    have : (false : Bool) = true := hx
    cases this

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
