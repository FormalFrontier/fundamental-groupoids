/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Convenient.ContinuousMapGeneratedBy

/-!
# Continuous maps and homeomorphisms for generated-by refinement

Generated-by refinement preserves continuity on the original carriers. It acts on
bundled continuous maps and homeomorphisms without changing their underlying
functions, and preserves identities and composition.

The refinement type synonym also admits the canonical lift of a continuous map
from a generated source. Its counit is natural, and determines such lifts uniquely.
The probe family, its index, and all original carrier universes remain independent.

## References

The generated-topology construction and its type-synonym API build on Mathlib's
[generated-by topology](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/GeneratedBy.lean), by Joël Riou, Dagur Asgeirsson and Ben Eltschig. The
generated-map continuity API used here is part of [generated maps](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/ContinuousMapGeneratedBy.lean), by Joël Riou.
The same-carrier interfaces and their characteristic laws compose these APIs.
-/

@[expose] public section

noncomputable section

universe t u v w z

open Topology

namespace Topology.WithGeneratedByTopology

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

/-- The ordinary continuous counit of the generated-by refinement. -/
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

/-- The generated-by refinement of an ordinary continuous map. -/
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

namespace Continuous

variable {ι : Type t} (Φ : ι → Type u) [tΦ : ∀ i, TopologicalSpace (Φ i)]
  {A : Type v} [tA : TopologicalSpace A] {B : Type w} [tB : TopologicalSpace B]

/-- A continuous map is continuous between the generated refinements of its
original source and target topologies, on the same carriers. -/
theorem generatedByTopology {f : A → B} (hf : @Continuous A B tA tB f) :
    @Continuous A B (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
      (@TopologicalSpace.generatedBy ι Φ tΦ B tB) f := by
  exact (hf.continuousGeneratedBy (X := Φ)).continuousMap.continuous

end Continuous

namespace Homeomorph

variable {ι : Type t} (Φ : ι → Type u) [tΦ : ∀ i, TopologicalSpace (Φ i)]
  {A : Type v} [tA : TopologicalSpace A] {B : Type w} [tB : TopologicalSpace B]

/-- Refine the topology dictionaries of a homeomorphism without changing its
underlying equivalence. -/
def generatedByTopology (e : @Homeomorph A B tA tB) :
    @Homeomorph A B (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
      (@TopologicalSpace.generatedBy ι Φ tΦ B tB) :=
  @Homeomorph.mk A B (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
    (@TopologicalSpace.generatedBy ι Φ tΦ B tB) (@Homeomorph.toEquiv A B tA tB e)
    (@Continuous.generatedByTopology ι Φ tΦ A tA B tB
      (@Homeomorph.toEquiv A B tA tB e)
      (@Homeomorph.continuous_toFun A B tA tB e))
    (@Continuous.generatedByTopology ι Φ tΦ B tB A tA
      (@Homeomorph.toEquiv A B tA tB e).symm
      (@Homeomorph.continuous_invFun A B tA tB e))

/-- Refining a homeomorphism preserves its whole underlying function. -/
theorem coe_generatedByTopology (e : @Homeomorph A B tA tB) :
    ⇑(generatedByTopology Φ e) = ⇑e := rfl

/-- Refining a homeomorphism preserves its values. -/
@[simp]
theorem generatedByTopology_apply (e : @Homeomorph A B tA tB) (a : A) :
    generatedByTopology Φ e a = e a := rfl

/-- Refining a homeomorphism preserves the values of its inverse. -/
@[simp]
theorem generatedByTopology_symm_apply (e : @Homeomorph A B tA tB) (b : B) :
    (@Homeomorph.symm A B (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
      (@TopologicalSpace.generatedBy ι Φ tΦ B tB) (generatedByTopology Φ e)) b =
      (@Homeomorph.symm A B tA tB e) b := rfl

/-- Generated refinement preserves the identity homeomorphism. -/
@[simp]
theorem generatedByTopology_refl (A : Type v) [tA : TopologicalSpace A] :
    generatedByTopology Φ (Homeomorph.refl A) =
      @Homeomorph.refl A (@TopologicalSpace.generatedBy ι Φ tΦ A tA) := rfl

/-- Generated refinement preserves composition of homeomorphisms. -/
theorem generatedByTopology_trans {D : Type z} [tD : TopologicalSpace D]
    (e : @Homeomorph A B tA tB) (d : @Homeomorph B D tB tD) :
    generatedByTopology Φ (e.trans d) =
      @Homeomorph.trans A B D (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
        (@TopologicalSpace.generatedBy ι Φ tΦ B tB)
        (@TopologicalSpace.generatedBy ι Φ tΦ D tD)
        (generatedByTopology Φ e) (generatedByTopology Φ d) := rfl

end Homeomorph

namespace ContinuousMap

section Refinement

variable {ι : Type t} (Φ : ι → Type u) [tΦ : ∀ i, TopologicalSpace (Φ i)]
  {A : Type v} [tA : TopologicalSpace A] {B : Type w} [tB : TopologicalSpace B]

/-- Refine the topology dictionaries of a continuous map, preserving its function. -/
def generatedByTopology (f : @ContinuousMap A B tA tB) :
    @ContinuousMap A B (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
      (@TopologicalSpace.generatedBy ι Φ tΦ B tB) :=
  @ContinuousMap.mk A B (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
    (@TopologicalSpace.generatedBy ι Φ tΦ B tB) (@ContinuousMap.toFun A B tA tB f)
    (@Continuous.generatedByTopology ι Φ tΦ A tA B tB
      (@ContinuousMap.toFun A B tA tB f) (@ContinuousMap.continuous A B tA tB f))

/-- Generated refinement does not change the whole underlying function. -/
theorem coe_generatedByTopology (f : @ContinuousMap A B tA tB) :
    @ContinuousMap.toFun A B (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
      (@TopologicalSpace.generatedBy ι Φ tΦ B tB)
      (@ContinuousMap.generatedByTopology ι Φ tΦ A tA B tB f) =
        @ContinuousMap.toFun A B tA tB f := rfl

/-- Generated refinement preserves the value of a continuous map at each point. -/
@[simp]
theorem generatedByTopology_apply (f : @ContinuousMap A B tA tB) (a : A) :
    @ContinuousMap.toFun A B (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
      (@TopologicalSpace.generatedBy ι Φ tΦ B tB)
      (@ContinuousMap.generatedByTopology ι Φ tΦ A tA B tB f) a =
        @ContinuousMap.toFun A B tA tB f a := rfl

/-- Generated refinement preserves the identity continuous map. -/
@[simp]
theorem generatedByTopology_id :
    @ContinuousMap.generatedByTopology ι Φ tΦ A tA A tA (@ContinuousMap.id A tA) =
      @ContinuousMap.id A (@TopologicalSpace.generatedBy ι Φ tΦ A tA) := rfl

/-- Generated refinement preserves composition of continuous maps. -/
theorem generatedByTopology_comp {D : Type z} [tD : TopologicalSpace D]
    (g : @ContinuousMap B D tB tD) (f : @ContinuousMap A B tA tB) :
    @ContinuousMap.generatedByTopology ι Φ tΦ A tA D tD
      (@ContinuousMap.comp A B D tA tB tD g f) =
      @ContinuousMap.comp A B D (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
        (@TopologicalSpace.generatedBy ι Φ tΦ B tB)
        (@TopologicalSpace.generatedBy ι Φ tΦ D tD)
        (@ContinuousMap.generatedByTopology ι Φ tΦ B tB D tD g)
        (@ContinuousMap.generatedByTopology ι Φ tΦ A tA B tB f) := by
  apply @ContinuousMap.ext A D (@TopologicalSpace.generatedBy ι Φ tΦ A tA)
    (@TopologicalSpace.generatedBy ι Φ tΦ D tD)
  intro a
  rfl

end Refinement

end ContinuousMap
