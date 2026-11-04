/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.CompactOpen.GeneratedByHomeomorph

/-!
# Bundled naturality of generated mapping-space comparisons

Ordinary source precomposition and target postcomposition act continuously on
both ordinary compact-open maps and generated maps. These actions require neither
generatedness of the source nor local compactness of the probes. Refining their
topology dictionaries gives continuous maps between the generated mapping spaces,
without changing the underlying actions.

The comparison with generated ordinary compact-open topology intertwines these
bundled actions, in both directions. The squares allow simultaneous change of
source and target and retain the original topologies of all four spaces. Only the
comparison squares require locally compact probes and generated ordinary products
of probes with each original generated source.

## References

The ordinary precomposition object delegates to Mathlib's
`ContinuousMap.compRightContinuousMap`; ordinary postcomposition uses its
compact-open continuity API. Generated actions build on [generated maps](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/ContinuousMapGeneratedBy.lean),
by Joël Riou, and [generated-by topology](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/GeneratedBy.lean), by Joël Riou, Dagur Asgeirsson
and Ben Eltschig. The bundled comparison squares and coherence laws compose
these formalizations.
-/

@[expose] public section

noncomputable section

universe t u v w v' w' z

open Topology

namespace ContinuousMap

section Composition

variable {A : Type v} [tA : TopologicalSpace A]
  {B : Type v'} [tB : TopologicalSpace B]
  {Y : Type w} [tY : TopologicalSpace Y]
  {Z : Type w'} [tZ : TopologicalSpace Z]

/-- Ordinary source precomposition, bundled between ordinary compact-open spaces. -/
def precompContinuousMap (p : @ContinuousMap B A tB tA) :
    @ContinuousMap (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
      (@ContinuousMap.compactOpen A Y tA tY)
      (@ContinuousMap.compactOpen B Y tB tY) := by
  apply ContinuousMap.compRightContinuousMap
  exact p

/-- Ordinary target postcomposition, bundled between ordinary compact-open spaces. -/
def postcompContinuousMap (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
      (@ContinuousMap.compactOpen A Y tA tY)
      (@ContinuousMap.compactOpen A Z tA tZ) :=
  @ContinuousMap.mk (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
    (@ContinuousMap.compactOpen A Y tA tY) (@ContinuousMap.compactOpen A Z tA tZ)
    (fun f => g.comp f) (ContinuousMap.continuous_postcomp g)

/-- The bundled precomposition action has the usual whole underlying function. -/
theorem coe_precompContinuousMap (p : @ContinuousMap B A tB tA) :
    @ContinuousMap.toFun (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
      (@ContinuousMap.compactOpen A Y tA tY)
      (@ContinuousMap.compactOpen B Y tB tY)
      (precompContinuousMap (Y := Y) p) =
      (fun f : @ContinuousMap A Y tA tY => f.comp p) := rfl

@[simp]
theorem precompContinuousMap_apply (p : @ContinuousMap B A tB tA)
    (f : @ContinuousMap A Y tA tY) :
    precompContinuousMap (Y := Y) p f = f.comp p := rfl

theorem precompContinuousMap_apply_apply (p : @ContinuousMap B A tB tA)
    (f : @ContinuousMap A Y tA tY) (b : B) :
    precompContinuousMap (Y := Y) p f b = f (p b) := rfl

/-- The bundled postcomposition action has the usual whole underlying function. -/
theorem coe_postcompContinuousMap (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap.toFun (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
      (@ContinuousMap.compactOpen A Y tA tY)
      (@ContinuousMap.compactOpen A Z tA tZ)
      (postcompContinuousMap (A := A) g) =
      (fun f : @ContinuousMap A Y tA tY => g.comp f) := rfl

@[simp]
theorem postcompContinuousMap_apply (g : @ContinuousMap Y Z tY tZ)
    (f : @ContinuousMap A Y tA tY) :
    postcompContinuousMap (A := A) g f = g.comp f := rfl

theorem postcompContinuousMap_apply_apply (g : @ContinuousMap Y Z tY tZ)
    (f : @ContinuousMap A Y tA tY) (a : A) :
    postcompContinuousMap (A := A) g f a = g (f a) := rfl

/-- Precomposition by the identity acts as the identity. -/
@[simp]
theorem precompContinuousMap_id :
    precompContinuousMap (Y := Y) (ContinuousMap.id A) =
      ContinuousMap.id (@ContinuousMap A Y tA tY) := by
  apply @ContinuousMap.ext (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
    (@ContinuousMap.compactOpen A Y tA tY)
    (@ContinuousMap.compactOpen A Y tA tY)
  intro f
  apply @ContinuousMap.ext A Y tA tY
  intro a
  rfl

/-- Precomposition reverses composition of source maps. -/
theorem precompContinuousMap_comp {D : Type z} [tD : TopologicalSpace D]
    (p : @ContinuousMap B A tB tA) (q : @ContinuousMap D B tD tB) :
    precompContinuousMap (Y := Y) (p.comp q) =
      (precompContinuousMap q).comp (precompContinuousMap p) := by
  apply @ContinuousMap.ext (@ContinuousMap A Y tA tY) (@ContinuousMap D Y tD tY)
    (@ContinuousMap.compactOpen A Y tA tY)
    (@ContinuousMap.compactOpen D Y tD tY)
  intro f
  apply @ContinuousMap.ext D Y tD tY
  intro d
  rfl

/-- Postcomposition by the identity acts as the identity. -/
@[simp]
theorem postcompContinuousMap_id :
    postcompContinuousMap (A := A) (ContinuousMap.id Y) =
      ContinuousMap.id (@ContinuousMap A Y tA tY) := by
  apply @ContinuousMap.ext (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
    (@ContinuousMap.compactOpen A Y tA tY)
    (@ContinuousMap.compactOpen A Y tA tY)
  intro f
  apply @ContinuousMap.ext A Y tA tY
  intro a
  rfl

/-- Postcomposition preserves composition of target maps. -/
theorem postcompContinuousMap_comp {T : Type z} [tT : TopologicalSpace T]
    (g : @ContinuousMap Y Z tY tZ) (h : @ContinuousMap Z T tZ tT) :
    postcompContinuousMap (A := A) (h.comp g) =
      (postcompContinuousMap h).comp (postcompContinuousMap g) := by
  apply @ContinuousMap.ext (@ContinuousMap A Y tA tY) (@ContinuousMap A T tA tT)
    (@ContinuousMap.compactOpen A Y tA tY)
    (@ContinuousMap.compactOpen A T tA tT)
  intro f
  apply @ContinuousMap.ext A T tA tT
  intro a
  rfl

variable {ι : Type t} (Φ : ι → Type u) [tΦ : ∀ i, TopologicalSpace (Φ i)]

/-- Source precomposition between generated ordinary compact-open spaces. -/
def precompGeneratedBy (p : @ContinuousMap B A tB tA) :
    @ContinuousMap (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Y tB tY)
        (@ContinuousMap.compactOpen B Y tB tY)) :=
  @ContinuousMap.generatedByTopology ι Φ tΦ (@ContinuousMap A Y tA tY)
    (@ContinuousMap.compactOpen A Y tA tY)
    (@ContinuousMap B Y tB tY) (@ContinuousMap.compactOpen B Y tB tY)
    (precompContinuousMap p)

/-- Target postcomposition between generated ordinary compact-open spaces. -/
def postcompGeneratedBy (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Z tA tZ)
        (@ContinuousMap.compactOpen A Z tA tZ)) :=
  @ContinuousMap.generatedByTopology ι Φ tΦ (@ContinuousMap A Y tA tY)
    (@ContinuousMap.compactOpen A Y tA tY)
    (@ContinuousMap A Z tA tZ) (@ContinuousMap.compactOpen A Z tA tZ)
    (postcompContinuousMap g)

/-- Refinement retains the whole ordinary precomposition action. -/
theorem coe_precompGeneratedBy (p : @ContinuousMap B A tB tA) :
    @ContinuousMap.toFun (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Y tB tY)
        (@ContinuousMap.compactOpen B Y tB tY))
      (precompGeneratedBy Φ (Y := Y) p) =
      (fun f : @ContinuousMap A Y tA tY => f.comp p) := rfl

@[simp]
theorem precompGeneratedBy_apply (p : @ContinuousMap B A tB tA)
    (f : @ContinuousMap A Y tA tY) :
    @ContinuousMap.toFun (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Y tB tY)
        (@ContinuousMap.compactOpen B Y tB tY))
      (precompGeneratedBy Φ (Y := Y) p) f = f.comp p := rfl

theorem precompGeneratedBy_apply_apply (p : @ContinuousMap B A tB tA)
    (f : @ContinuousMap A Y tA tY) (b : B) :
    @ContinuousMap.toFun (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Y tB tY)
        (@ContinuousMap.compactOpen B Y tB tY))
      (precompGeneratedBy Φ (Y := Y) p) f b = f (p b) := rfl

/-- Refinement retains the whole ordinary postcomposition action. -/
theorem coe_postcompGeneratedBy (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap.toFun (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Z tA tZ)
        (@ContinuousMap.compactOpen A Z tA tZ))
      (postcompGeneratedBy Φ (A := A) g) =
      (fun f : @ContinuousMap A Y tA tY => g.comp f) := rfl

@[simp]
theorem postcompGeneratedBy_apply (g : @ContinuousMap Y Z tY tZ)
    (f : @ContinuousMap A Y tA tY) :
    @ContinuousMap.toFun (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Z tA tZ)
        (@ContinuousMap.compactOpen A Z tA tZ))
      (postcompGeneratedBy Φ (A := A) g) f = g.comp f := rfl

theorem postcompGeneratedBy_apply_apply (g : @ContinuousMap Y Z tY tZ)
    (f : @ContinuousMap A Y tA tY) (a : A) :
    @ContinuousMap.toFun (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Z tA tZ)
        (@ContinuousMap.compactOpen A Z tA tZ))
      (postcompGeneratedBy Φ (A := A) g) f a = g (f a) := rfl

/-- Generated ordinary precomposition preserves the identity source map. -/
@[simp]
theorem precompGeneratedBy_id :
    precompGeneratedBy Φ (Y := Y) (ContinuousMap.id A) =
      @ContinuousMap.id (@ContinuousMap A Y tA tY)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY)) := by
  exact (congrArg
    (@ContinuousMap.generatedByTopology ι Φ tΦ
      (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY)
      (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY))
    (precompContinuousMap_id (A := A) (Y := Y))).trans
      (@ContinuousMap.generatedByTopology_id ι Φ tΦ
        (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY))

/-- Generated ordinary precomposition reverses composition of source maps. -/
theorem precompGeneratedBy_comp {D : Type z} [tD : TopologicalSpace D]
    (p : @ContinuousMap B A tB tA) (q : @ContinuousMap D B tD tB) :
    precompGeneratedBy Φ (Y := Y) (p.comp q) =
      @ContinuousMap.comp (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
        (@ContinuousMap D Y tD tY)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY))
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Y tB tY)
          (@ContinuousMap.compactOpen B Y tB tY))
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap D Y tD tY)
          (@ContinuousMap.compactOpen D Y tD tY))
        (precompGeneratedBy Φ q) (precompGeneratedBy Φ p) := by
  exact (congrArg
    (@ContinuousMap.generatedByTopology ι Φ tΦ
      (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY)
      (@ContinuousMap D Y tD tY) (@ContinuousMap.compactOpen D Y tD tY))
    (precompContinuousMap_comp (Y := Y) p q)).trans
      (@ContinuousMap.generatedByTopology_comp ι Φ tΦ
        (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY)
        (@ContinuousMap B Y tB tY) (@ContinuousMap.compactOpen B Y tB tY)
        (@ContinuousMap D Y tD tY) (@ContinuousMap.compactOpen D Y tD tY)
        (precompContinuousMap q) (precompContinuousMap p))

/-- Generated ordinary postcomposition preserves the identity target map. -/
@[simp]
theorem postcompGeneratedBy_id :
    postcompGeneratedBy Φ (A := A) (ContinuousMap.id Y) =
      @ContinuousMap.id (@ContinuousMap A Y tA tY)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY)) := by
  exact (congrArg
    (@ContinuousMap.generatedByTopology ι Φ tΦ
      (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY)
      (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY))
    (postcompContinuousMap_id (A := A) (Y := Y))).trans
      (@ContinuousMap.generatedByTopology_id ι Φ tΦ
        (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY))

/-- Generated ordinary postcomposition preserves composition of target maps. -/
theorem postcompGeneratedBy_comp {T : Type z} [tT : TopologicalSpace T]
    (g : @ContinuousMap Y Z tY tZ) (h : @ContinuousMap Z T tZ tT) :
    postcompGeneratedBy Φ (A := A) (h.comp g) =
      @ContinuousMap.comp (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
        (@ContinuousMap A T tA tT)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY))
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Z tA tZ)
          (@ContinuousMap.compactOpen A Z tA tZ))
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A T tA tT)
          (@ContinuousMap.compactOpen A T tA tT))
        (postcompGeneratedBy Φ h) (postcompGeneratedBy Φ g) := by
  exact (congrArg
    (@ContinuousMap.generatedByTopology ι Φ tΦ
      (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY)
      (@ContinuousMap A T tA tT) (@ContinuousMap.compactOpen A T tA tT))
    (postcompContinuousMap_comp (A := A) g h)).trans
      (@ContinuousMap.generatedByTopology_comp ι Φ tΦ
        (@ContinuousMap A Y tA tY) (@ContinuousMap.compactOpen A Y tA tY)
        (@ContinuousMap A Z tA tZ) (@ContinuousMap.compactOpen A Z tA tZ)
        (@ContinuousMap A T tA tT) (@ContinuousMap.compactOpen A T tA tT)
        (postcompContinuousMap h) (postcompContinuousMap g))

end Composition

end ContinuousMap

namespace Topology.ContinuousMapGeneratedBy

variable {ι : Type t} (Φ : ι → Type u) [tΦ : ∀ i, TopologicalSpace (Φ i)]
  {A : Type v} [tA : TopologicalSpace A]
  {B : Type v'} [tB : TopologicalSpace B]
  {Y : Type w} [tY : TopologicalSpace Y]
  {Z : Type w'} [tZ : TopologicalSpace Z]

/-- Precomposition by an ordinary continuous map, bundled on generated-map spaces.
This is source precomposition, as opposed to the probe-coordinate map `precomp`. -/
def precompContinuousMap (p : @ContinuousMap B A tB tA) :
    @ContinuousMap (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
      inferInstance inferInstance := by
  refine @ContinuousMap.mk (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
    inferInstance inferInstance (fun f => f.comp (ofContinuousMap Φ p)) ?_
  apply (continuous_iff (X := Φ) (φ := fun f : ContinuousMapGeneratedBy Φ A Y =>
    f.comp (ofContinuousMap Φ p))).2
  intro i q
  have hcoord :
      precomp (X := Φ) q ∘ (fun f : ContinuousMapGeneratedBy Φ A Y =>
        f.comp (ofContinuousMap Φ p)) = precomp (X := Φ) (p.comp q) := by
    funext f
    apply @ContinuousMap.ext (Φ i) Y (tΦ i) tY
    intro x
    exact (congrFun (precomp_apply (X := Φ) q (f.comp (ofContinuousMap Φ p))) x).trans
      (congrFun (precomp_apply (X := Φ) (p.comp q) f) x).symm
  rw [hcoord]
  simpa only [Function.comp_id] using
    ((continuous_iff (X := Φ) (φ := (_root_.id : ContinuousMapGeneratedBy Φ A Y →
      ContinuousMapGeneratedBy Φ A Y))).1 continuous_id i (p.comp q))

/-- Postcomposition by an ordinary continuous map, bundled on generated-map spaces. -/
def postcompContinuousMap (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
      inferInstance inferInstance := by
  refine @ContinuousMap.mk (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
    inferInstance inferInstance (fun f => (ofContinuousMap Φ g).comp f) ?_
  apply (continuous_iff (X := Φ) (φ := fun f : ContinuousMapGeneratedBy Φ A Y =>
    (ofContinuousMap Φ g).comp f)).2
  intro i q
  have hcoord :
      precomp (X := Φ) q ∘ (fun f : ContinuousMapGeneratedBy Φ A Y =>
        (ofContinuousMap Φ g).comp f) =
      (fun k : @ContinuousMap (Φ i) Y (tΦ i) tY => g.comp k) ∘ precomp (X := Φ) q := by
    funext f
    apply @ContinuousMap.ext (Φ i) Z (tΦ i) tZ
    intro x
    exact (congrFun (precomp_apply (X := Φ) q ((ofContinuousMap Φ g).comp f)) x).trans
      (congrArg g (congrFun (precomp_apply (X := Φ) q f) x).symm)
  rw [hcoord]
  have hq : Continuous (precomp (X := Φ) q : ContinuousMapGeneratedBy Φ A Y →
      @ContinuousMap (Φ i) Y (tΦ i) tY) := by
    simpa only [Function.comp_id] using
      ((continuous_iff (X := Φ) (φ := (_root_.id : ContinuousMapGeneratedBy Φ A Y →
        ContinuousMapGeneratedBy Φ A Y))).1 continuous_id i q)
  exact (ContinuousMap.continuous_postcomp g).comp hq

/-- Whole source precomposition uses the canonical conversion of the source map. -/
theorem coe_precompContinuousMap (p : @ContinuousMap B A tB tA) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
      inferInstance
      inferInstance
      (precompContinuousMap Φ (Y := Y) p) =
      (fun f : ContinuousMapGeneratedBy Φ A Y => f.comp (ofContinuousMap Φ p)) := rfl

@[simp]
theorem precompContinuousMap_apply (p : @ContinuousMap B A tB tA)
    (f : ContinuousMapGeneratedBy Φ A Y) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
      inferInstance
      inferInstance
      (precompContinuousMap Φ (Y := Y) p) f = f.comp (ofContinuousMap Φ p) := rfl

theorem precompContinuousMap_apply_apply (p : @ContinuousMap B A tB tA)
    (f : ContinuousMapGeneratedBy Φ A Y) (b : B) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
      inferInstance
      inferInstance
      (precompContinuousMap Φ (Y := Y) p) f b = f (p b) := rfl

/-- Whole target postcomposition uses the canonical conversion of the target map. -/
theorem coe_postcompContinuousMap (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
      inferInstance
      inferInstance
      (postcompContinuousMap Φ (A := A) g) =
      (fun f : ContinuousMapGeneratedBy Φ A Y => (ofContinuousMap Φ g).comp f) := rfl

@[simp]
theorem postcompContinuousMap_apply (g : @ContinuousMap Y Z tY tZ)
    (f : ContinuousMapGeneratedBy Φ A Y) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
      inferInstance
      inferInstance
      (postcompContinuousMap Φ (A := A) g) f = (ofContinuousMap Φ g).comp f := rfl

theorem postcompContinuousMap_apply_apply (g : @ContinuousMap Y Z tY tZ)
    (f : ContinuousMapGeneratedBy Φ A Y) (a : A) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
      inferInstance
      inferInstance
      (postcompContinuousMap Φ (A := A) g) f a = g (f a) := rfl

/-- Precomposition by the identity acts as the identity on generated maps. -/
@[simp]
theorem precompContinuousMap_id :
    precompContinuousMap Φ (Y := Y) (ContinuousMap.id A) =
      ContinuousMap.id (ContinuousMapGeneratedBy Φ A Y) := by
  apply @ContinuousMap.ext (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Y)
    inferInstance
    inferInstance
  intro f
  apply DFunLike.ext
  intro a
  rfl

/-- Source precomposition reverses composition of ordinary source maps. -/
theorem precompContinuousMap_comp {D : Type z} [tD : TopologicalSpace D]
    (p : @ContinuousMap B A tB tA) (q : @ContinuousMap D B tD tB) :
    precompContinuousMap Φ (Y := Y) (p.comp q) =
      (precompContinuousMap Φ q).comp (precompContinuousMap Φ p) := by
  apply @ContinuousMap.ext (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ D Y)
    inferInstance
    inferInstance
  intro f
  apply DFunLike.ext
  intro d
  rfl

/-- Postcomposition by the identity acts as the identity on generated maps. -/
@[simp]
theorem postcompContinuousMap_id :
    postcompContinuousMap Φ (A := A) (ContinuousMap.id Y) =
      ContinuousMap.id (ContinuousMapGeneratedBy Φ A Y) := by
  apply @ContinuousMap.ext (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Y)
    inferInstance
    inferInstance
  intro f
  apply DFunLike.ext
  intro a
  rfl

/-- Target postcomposition preserves composition of ordinary target maps. -/
theorem postcompContinuousMap_comp {T : Type z} [tT : TopologicalSpace T]
    (g : @ContinuousMap Y Z tY tZ) (h : @ContinuousMap Z T tZ tT) :
    postcompContinuousMap Φ (A := A) (h.comp g) =
      (postcompContinuousMap Φ h).comp (postcompContinuousMap Φ g) := by
  apply @ContinuousMap.ext (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A T)
    inferInstance
    inferInstance
  intro f
  apply DFunLike.ext
  intro a
  rfl

/-- Source precomposition between generated refinements of generated-map spaces. -/
def precompGeneratedBy (p : @ContinuousMap B A tB tA) :
    @ContinuousMap (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Y) inferInstance) :=
  @ContinuousMap.generatedByTopology ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance
    (ContinuousMapGeneratedBy Φ B Y) inferInstance (precompContinuousMap Φ p)

/-- Target postcomposition between generated refinements of generated-map spaces. -/
def postcompGeneratedBy (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Z) inferInstance) :=
  @ContinuousMap.generatedByTopology ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance
    (ContinuousMapGeneratedBy Φ A Z) inferInstance (postcompContinuousMap Φ g)

/-- Refinement retains the whole source precomposition action on generated maps. -/
theorem coe_precompGeneratedBy (p : @ContinuousMap B A tB tA) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Y) inferInstance)
      (precompGeneratedBy Φ (Y := Y) p) =
      (fun f : ContinuousMapGeneratedBy Φ A Y => f.comp (ofContinuousMap Φ p)) := rfl

@[simp]
theorem precompGeneratedBy_apply (p : @ContinuousMap B A tB tA)
    (f : ContinuousMapGeneratedBy Φ A Y) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Y) inferInstance)
      (precompGeneratedBy Φ (Y := Y) p) f = f.comp (ofContinuousMap Φ p) := rfl

theorem precompGeneratedBy_apply_apply (p : @ContinuousMap B A tB tA)
    (f : ContinuousMapGeneratedBy Φ A Y) (b : B) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Y) inferInstance)
      (precompGeneratedBy Φ (Y := Y) p) f b = f (p b) := rfl

/-- Refinement retains the whole target postcomposition action on generated maps. -/
theorem coe_postcompGeneratedBy (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Z) inferInstance)
      (postcompGeneratedBy Φ (A := A) g) =
      (fun f : ContinuousMapGeneratedBy Φ A Y => (ofContinuousMap Φ g).comp f) := rfl

@[simp]
theorem postcompGeneratedBy_apply (g : @ContinuousMap Y Z tY tZ)
    (f : ContinuousMapGeneratedBy Φ A Y) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Z) inferInstance)
      (postcompGeneratedBy Φ (A := A) g) f = (ofContinuousMap Φ g).comp f := rfl

theorem postcompGeneratedBy_apply_apply (g : @ContinuousMap Y Z tY tZ)
    (f : ContinuousMapGeneratedBy Φ A Y) (a : A) :
    @ContinuousMap.toFun (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Z) inferInstance)
      (postcompGeneratedBy Φ (A := A) g) f a = g (f a) := rfl

/-- Generated source precomposition preserves the identity source map. -/
@[simp]
theorem precompGeneratedBy_id :
    precompGeneratedBy Φ (Y := Y) (ContinuousMap.id A) =
      @ContinuousMap.id (ContinuousMapGeneratedBy Φ A Y)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y)
          inferInstance) := by
  exact (congrArg
    (@ContinuousMap.generatedByTopology ι Φ tΦ
      (ContinuousMapGeneratedBy Φ A Y) inferInstance
      (ContinuousMapGeneratedBy Φ A Y) inferInstance)
    (precompContinuousMap_id Φ (A := A) (Y := Y))).trans
      (@ContinuousMap.generatedByTopology_id ι Φ tΦ
        (ContinuousMapGeneratedBy Φ A Y) inferInstance)

/-- Generated source precomposition reverses composition of ordinary source maps. -/
theorem precompGeneratedBy_comp {D : Type z} [tD : TopologicalSpace D]
    (p : @ContinuousMap B A tB tA) (q : @ContinuousMap D B tD tB) :
    precompGeneratedBy Φ (Y := Y) (p.comp q) =
      @ContinuousMap.comp (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
        (ContinuousMapGeneratedBy Φ D Y)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Y) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ D Y) inferInstance)
        (precompGeneratedBy Φ q) (precompGeneratedBy Φ p) := by
  exact (congrArg
    (@ContinuousMap.generatedByTopology ι Φ tΦ
      (ContinuousMapGeneratedBy Φ A Y) inferInstance
      (ContinuousMapGeneratedBy Φ D Y) inferInstance)
    (precompContinuousMap_comp Φ (Y := Y) p q)).trans
      (@ContinuousMap.generatedByTopology_comp ι Φ tΦ
        (ContinuousMapGeneratedBy Φ A Y) inferInstance
        (ContinuousMapGeneratedBy Φ B Y) inferInstance
        (ContinuousMapGeneratedBy Φ D Y) inferInstance
        (precompContinuousMap Φ q) (precompContinuousMap Φ p))

/-- Generated target postcomposition preserves the identity target map. -/
@[simp]
theorem postcompGeneratedBy_id :
    postcompGeneratedBy Φ (A := A) (ContinuousMap.id Y) =
      @ContinuousMap.id (ContinuousMapGeneratedBy Φ A Y)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y)
          inferInstance) := by
  exact (congrArg
    (@ContinuousMap.generatedByTopology ι Φ tΦ
      (ContinuousMapGeneratedBy Φ A Y) inferInstance
      (ContinuousMapGeneratedBy Φ A Y) inferInstance)
    (postcompContinuousMap_id Φ (A := A) (Y := Y))).trans
      (@ContinuousMap.generatedByTopology_id ι Φ tΦ
        (ContinuousMapGeneratedBy Φ A Y) inferInstance)

/-- Generated target postcomposition preserves composition of ordinary target maps. -/
theorem postcompGeneratedBy_comp {T : Type z} [tT : TopologicalSpace T]
    (g : @ContinuousMap Y Z tY tZ) (h : @ContinuousMap Z T tZ tT) :
    postcompGeneratedBy Φ (A := A) (h.comp g) =
      @ContinuousMap.comp (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ A Z)
        (ContinuousMapGeneratedBy Φ A T)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Z) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A T) inferInstance)
        (postcompGeneratedBy Φ h) (postcompGeneratedBy Φ g) := by
  exact (congrArg
    (@ContinuousMap.generatedByTopology ι Φ tΦ
      (ContinuousMapGeneratedBy Φ A Y) inferInstance
      (ContinuousMapGeneratedBy Φ A T) inferInstance)
    (postcompContinuousMap_comp Φ (A := A) g h)).trans
      (@ContinuousMap.generatedByTopology_comp ι Φ tΦ
        (ContinuousMapGeneratedBy Φ A Y) inferInstance
        (ContinuousMapGeneratedBy Φ A Z) inferInstance
        (ContinuousMapGeneratedBy Φ A T) inferInstance
        (postcompContinuousMap Φ h) (postcompContinuousMap Φ g))

end Topology.ContinuousMapGeneratedBy

namespace Homeomorph

variable {ι : Type t} (Φ : ι → Type u) [tΦ : ∀ i, TopologicalSpace (Φ i)]
  (A : Type v) [tA : TopologicalSpace A] (Y : Type w) [tY : TopologicalSpace Y]
  [∀ i, LocallyCompactSpace (Φ i)] [∀ i, IsGeneratedBy Φ (Φ i × A)]
  [IsGeneratedBy Φ A]

/-- The generated compact-open comparison intertwines bundled source
precomposition and target postcomposition. All four sides of the square are
continuous maps between the generated hom-space topologies. -/
theorem generatedByCompactOpen_naturality_continuousMap
    {B : Type v'} [tB : TopologicalSpace B]
    [∀ i, IsGeneratedBy Φ (Φ i × B)] [IsGeneratedBy Φ B]
    {Z : Type w'} [tZ : TopologicalSpace Z]
    (p : @ContinuousMap B A tB tA) (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap.comp
      (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Z)
      (@ContinuousMap B Z tB tZ)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
        (@ContinuousMap.compactOpen B Z tB tZ))
      (@ContinuousMap.mk (ContinuousMapGeneratedBy Φ B Z) (@ContinuousMap B Z tB tZ)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
          (@ContinuousMap.compactOpen B Z tB tZ))
        (@Homeomorph.toEquiv (ContinuousMapGeneratedBy Φ B Z) (@ContinuousMap B Z tB tZ)
          (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
          (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
            (@ContinuousMap.compactOpen B Z tB tZ))
          (generatedByCompactOpen Φ B Z))
        (@Homeomorph.continuous_toFun (ContinuousMapGeneratedBy Φ B Z) (@ContinuousMap B Z tB tZ)
          (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
          (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
            (@ContinuousMap.compactOpen B Z tB tZ))
          (generatedByCompactOpen Φ B Z)))
      (@ContinuousMap.comp
        (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
        (ContinuousMapGeneratedBy Φ B Z)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Y) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
        (ContinuousMapGeneratedBy.postcompGeneratedBy Φ (A := B) g)
        (ContinuousMapGeneratedBy.precompGeneratedBy Φ (Y := Y) p)) =
    @ContinuousMap.comp
      (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
      (@ContinuousMap B Z tB tZ)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
        (@ContinuousMap.compactOpen B Z tB tZ))
      (@ContinuousMap.comp
        (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
        (@ContinuousMap B Z tB tZ)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY))
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Y tB tY)
          (@ContinuousMap.compactOpen B Y tB tY))
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
          (@ContinuousMap.compactOpen B Z tB tZ))
        (ContinuousMap.postcompGeneratedBy Φ (A := B) g)
        (ContinuousMap.precompGeneratedBy Φ (Y := Y) p))
      (@ContinuousMap.mk (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY))
        (@Homeomorph.toEquiv (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
          (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
          (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
            (@ContinuousMap.compactOpen A Y tA tY))
          (generatedByCompactOpen Φ A Y))
        (@Homeomorph.continuous_toFun (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
          (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
          (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
            (@ContinuousMap.compactOpen A Y tA tY))
          (generatedByCompactOpen Φ A Y))) := by
  apply @ContinuousMap.ext (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap B Z tB tZ)
    (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
    (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
      (@ContinuousMap.compactOpen B Z tB tZ))
  intro f
  exact congrFun (generatedByCompactOpen_naturality Φ A Y p g) f

/-- The inverse comparison intertwines the same bundled actions, giving the
commuting square in the reverse direction. -/
theorem generatedByCompactOpen_symm_naturality_continuousMap
    {B : Type v'} [tB : TopologicalSpace B]
    [∀ i, IsGeneratedBy Φ (Φ i × B)] [IsGeneratedBy Φ B]
    {Z : Type w'} [tZ : TopologicalSpace Z]
    (p : @ContinuousMap B A tB tA) (g : @ContinuousMap Y Z tY tZ) :
    @ContinuousMap.comp
      (@ContinuousMap A Y tA tY) (@ContinuousMap B Z tB tZ)
      (ContinuousMapGeneratedBy Φ B Z)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
        (@ContinuousMap.compactOpen B Z tB tZ))
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
      (@ContinuousMap.mk (@ContinuousMap B Z tB tZ) (ContinuousMapGeneratedBy Φ B Z)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
          (@ContinuousMap.compactOpen B Z tB tZ))
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
        (@Homeomorph.toEquiv (ContinuousMapGeneratedBy Φ B Z) (@ContinuousMap B Z tB tZ)
          (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
          (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
            (@ContinuousMap.compactOpen B Z tB tZ))
          (generatedByCompactOpen Φ B Z)).symm
        (@Homeomorph.continuous_invFun (ContinuousMapGeneratedBy Φ B Z) (@ContinuousMap B Z tB tZ)
          (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
          (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
            (@ContinuousMap.compactOpen B Z tB tZ))
          (generatedByCompactOpen Φ B Z)))
      (@ContinuousMap.comp
        (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
        (@ContinuousMap B Z tB tZ)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY))
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Y tB tY)
          (@ContinuousMap.compactOpen B Y tB tY))
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
          (@ContinuousMap.compactOpen B Z tB tZ))
        (ContinuousMap.postcompGeneratedBy Φ (A := B) g)
        (ContinuousMap.precompGeneratedBy Φ (Y := Y) p)) =
    @ContinuousMap.comp
      (@ContinuousMap A Y tA tY) (ContinuousMapGeneratedBy Φ A Y)
      (ContinuousMapGeneratedBy Φ B Z)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY))
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
      (@ContinuousMap.comp
        (ContinuousMapGeneratedBy Φ A Y) (ContinuousMapGeneratedBy Φ B Y)
        (ContinuousMapGeneratedBy Φ B Z)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Y) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
        (ContinuousMapGeneratedBy.postcompGeneratedBy Φ (A := B) g)
        (ContinuousMapGeneratedBy.precompGeneratedBy Φ (Y := Y) p))
      (@ContinuousMap.mk (@ContinuousMap A Y tA tY) (ContinuousMapGeneratedBy Φ A Y)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY))
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
        (@Homeomorph.toEquiv (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
          (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
          (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
            (@ContinuousMap.compactOpen A Y tA tY))
          (generatedByCompactOpen Φ A Y)).symm
        (@Homeomorph.continuous_invFun (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
          (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
          (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
            (@ContinuousMap.compactOpen A Y tA tY))
          (generatedByCompactOpen Φ A Y))) := by
  apply @ContinuousMap.ext (@ContinuousMap A Y tA tY) (ContinuousMapGeneratedBy Φ B Z)
    (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
      (@ContinuousMap.compactOpen A Y tA tY))
    (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
  intro f
  exact congrFun (generatedByCompactOpen_symm_naturality Φ A Y p g) f

end Homeomorph
