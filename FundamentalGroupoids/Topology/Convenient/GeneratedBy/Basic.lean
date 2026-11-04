/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Convenient.ContinuousMapGeneratedBy

/-!
# Continuous maps for generated-by refinement

The stock generated-by refinement acts on continuous maps and admits the canonical
lift of a continuous map from a generated source. The probe family, its index, and
all original carrier universes remain independent.
-/

@[expose] public section

noncomputable section

universe t u v w z

open Topology

namespace Topology.WithGeneratedByTopology

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

/-- The ordinary continuous counit of the stock generated-by refinement. -/
def counitContinuousMap (Y : Type v) [TopologicalSpace Y] :
    C(WithGeneratedByTopology X Y, Y) := by
  refine ⟨equiv, (continuous_from_iff _).2 ?_⟩
  intro i f
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using f.continuous

@[simp]
theorem counitContinuousMap_apply (Y : Type v) [TopologicalSpace Y]
    (y : WithGeneratedByTopology X Y) :
    counitContinuousMap X Y y = equiv y := rfl

variable {Y : Type v} [TopologicalSpace Y] {Z : Type w} [TopologicalSpace Z]

/-- The stock refinement of an ordinary continuous map. -/
def mapContinuousMap (f : C(Y, Z)) :
    C(WithGeneratedByTopology X Y, WithGeneratedByTopology X Z) :=
  (f.continuous.continuousGeneratedBy (X := X)).continuousMap

@[simp]
theorem mapContinuousMap_apply (f : C(Y, Z)) (y : WithGeneratedByTopology X Y) :
    mapContinuousMap X f y =
      (equiv (X := X) (Y := Z)).symm (f (equiv y)) := by
  exact congrFun (ContinuousGeneratedBy.continuousMap_coe
    (f.continuous.continuousGeneratedBy (X := X))) y

theorem equiv_mapContinuousMap (f : C(Y, Z)) (y : WithGeneratedByTopology X Y) :
    equiv (mapContinuousMap X f y) = f (equiv y) := by
  rw [mapContinuousMap_apply, Equiv.apply_symm_apply]

/-- Refinement preserves the identity continuous map. -/
@[simp]
theorem mapContinuousMap_id (Y : Type v) [TopologicalSpace Y] :
    mapContinuousMap X (ContinuousMap.id Y) =
      ContinuousMap.id (WithGeneratedByTopology X Y) := by
  apply ContinuousMap.ext
  intro y
  apply (equiv (X := X) (Y := Y)).injective
  simp only [equiv_mapContinuousMap, ContinuousMap.id_apply]

/-- Refinement preserves composition of continuous maps. -/
theorem mapContinuousMap_comp {T : Type z} [TopologicalSpace T]
    (f : C(Z, T)) (g : C(Y, Z)) :
    mapContinuousMap X (f.comp g) =
      (mapContinuousMap X f).comp (mapContinuousMap X g) := by
  apply ContinuousMap.ext
  intro y
  apply (equiv (X := X) (Y := T)).injective
  simp only [ContinuousMap.comp_apply, equiv_mapContinuousMap]

/-- The ordinary counit is natural in continuous maps. -/
theorem mapContinuousMap_counit (f : C(Y, Z)) :
    (counitContinuousMap X Z).comp (mapContinuousMap X f) =
      f.comp (counitContinuousMap X Y) := by
  apply ContinuousMap.ext
  intro y
  simp only [ContinuousMap.comp_apply, counitContinuousMap_apply, equiv_mapContinuousMap]

/-- Lift an ordinary continuous map from a generated source to a refined target. -/
def generatedSourceLift [IsGeneratedBy X Y] (f : C(Y, Z)) :
    C(Y, WithGeneratedByTopology X Z) :=
  (mapContinuousMap X f).comp
    (toContinuousMap ((IsGeneratedBy.homeomorph (X := X) (Y := Y)).symm))

@[simp]
theorem generatedSourceLift_apply [IsGeneratedBy X Y] (f : C(Y, Z)) (y : Y) :
    generatedSourceLift X f y = (equiv (X := X) (Y := Z)).symm (f y) := by
  simp [generatedSourceLift]

/-- Composing a generated-source lift with the counit recovers the original map. -/
@[simp]
theorem generatedSourceLift_counit [IsGeneratedBy X Y] (f : C(Y, Z)) :
    (counitContinuousMap X Z).comp (generatedSourceLift X f) = f := by
  apply ContinuousMap.ext
  intro y
  simp only [ContinuousMap.comp_apply, counitContinuousMap_apply,
    generatedSourceLift_apply, Equiv.apply_symm_apply]

/-- A lift to the refined target is determined by its composite with the counit. -/
theorem generatedSourceLift_unique [IsGeneratedBy X Y] (f : C(Y, Z))
    (g : C(Y, WithGeneratedByTopology X Z))
    (hg : (counitContinuousMap X Z).comp g = f) :
    g = generatedSourceLift X f := by
  apply ContinuousMap.ext
  intro y
  apply (equiv (X := X) (Y := Z)).injective
  have hy := DFunLike.congr_fun hg y
  simpa only [ContinuousMap.comp_apply, counitContinuousMap_apply,
    generatedSourceLift_apply, Equiv.apply_symm_apply] using hy

end Topology.WithGeneratedByTopology
