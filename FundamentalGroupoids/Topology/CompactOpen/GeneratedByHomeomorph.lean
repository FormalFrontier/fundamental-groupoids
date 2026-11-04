/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.CompactOpen.GeneratedBy
public import FundamentalGroupoids.Topology.CompactOpen.GeneratedByMaps

/-!
# Generated mapping spaces and compact-open topology

The topology on generated maps induces the probe compact-open topology on the
ordinary continuous-map carrier, without any generatedness hypothesis. For an
original generated source, the carrier equivalence is therefore a homeomorphism
between generated maps and probe compact-open maps.

Generated refinement preserves continuous maps and homeomorphisms. Applying
this to the carrier homeomorphism and then using the generated compact-open
comparison gives a value-preserving homeomorphism from the refinement of the
generated mapping space to the refinement of ordinary compact-open maps.

Only local compactness of the probes, generatedness of their ordinary products
with the original source, and generatedness of that source are assumed. The original
source and target topologies, the continuous-map carrier, and both outer refinements
are retained.
-/

@[expose] public section

noncomputable section

universe t u v w v' w'

open Topology

namespace ContinuousMap

variable {ι : Type t} (Φ : ι → Type u) [tΦ : ∀ i, TopologicalSpace (Φ i)]
  (A : Type v) [tA : TopologicalSpace A] (Y : Type w) [tY : TopologicalSpace Y]

/-- The probe compact-open topology is precisely the topology induced by the
conversion to generated maps. This equality needs no generatedness assumption. -/
theorem probeCompactOpenTopology_eq_inducedContinuousMap :
    probeCompactOpenTopology Φ A Y =
      ContinuousMapGeneratedBy.continuousMapInducedTopology Φ (A := A) (Y := Y) := by
  apply le_antisymm
  · apply continuous_id_iff_le.1
    let : TopologicalSpace (@ContinuousMap A Y tA tY) := probeCompactOpenTopology Φ A Y
    have hcoords : ∀ (i : ι) (p : @ContinuousMap (Φ i) A (tΦ i) tA),
        @Continuous (@ContinuousMap A Y tA tY)
          (@ContinuousMap (Φ i) Y (tΦ i) tY) (probeCompactOpenTopology Φ A Y)
          (@ContinuousMap.compactOpen (Φ i) Y (tΦ i) tY)
          (fun f => f.comp p) := by
      exact (continuous_probeCompactOpen_iff Φ A Y
        (tZ := probeCompactOpenTopology Φ A Y) (h := id)).1
          (@continuous_id (@ContinuousMap A Y tA tY) (probeCompactOpenTopology Φ A Y))
    exact (ContinuousMapGeneratedBy.continuous_inducedTopology_iff_precomp Φ id).2 hcoords
  · apply continuous_id_iff_le.1
    let : TopologicalSpace (@ContinuousMap A Y tA tY) :=
      ContinuousMapGeneratedBy.continuousMapInducedTopology Φ (A := A) (Y := Y)
    apply (continuous_probeCompactOpen_iff Φ A Y
      (tZ := ContinuousMapGeneratedBy.continuousMapInducedTopology Φ (A := A) (Y := Y))
      (h := id)).2
    exact (ContinuousMapGeneratedBy.continuous_inducedTopology_iff_precomp Φ id).1
      (@continuous_id (@ContinuousMap A Y tA tY)
        (ContinuousMapGeneratedBy.continuousMapInducedTopology Φ (A := A) (Y := Y)))

end ContinuousMap

namespace Homeomorph

variable {ι : Type t} (Φ : ι → Type u) [tΦ : ∀ i, TopologicalSpace (Φ i)]
  (A : Type v) [tA : TopologicalSpace A] (Y : Type w) [tY : TopologicalSpace Y]

/-- Generated maps on an original generated source are homeomorphic to the ordinary
continuous-map carrier with its probe compact-open topology. -/
def generatedMapProbeCompactOpen [IsGeneratedBy Φ A] :
    @Homeomorph (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
      inferInstance (ContinuousMap.probeCompactOpenTopology Φ A Y) :=
  @Homeomorph.mk (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
    inferInstance (ContinuousMap.probeCompactOpenTopology Φ A Y)
    (@Homeomorph.toEquiv (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
      inferInstance (ContinuousMapGeneratedBy.continuousMapInducedTopology Φ (A := A) (Y := Y))
      (ContinuousMapGeneratedBy.homeomorphInducedContinuousMap Φ (A := A) (Y := Y)))
    (by
      rw [ContinuousMap.probeCompactOpenTopology_eq_inducedContinuousMap Φ A Y]
      exact @Homeomorph.continuous_toFun
        (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY) inferInstance
        (ContinuousMapGeneratedBy.continuousMapInducedTopology Φ (A := A) (Y := Y))
        (ContinuousMapGeneratedBy.homeomorphInducedContinuousMap Φ (A := A) (Y := Y)))
    (by
      rw [ContinuousMap.probeCompactOpenTopology_eq_inducedContinuousMap Φ A Y]
      exact @Homeomorph.continuous_invFun
        (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY) inferInstance
        (ContinuousMapGeneratedBy.continuousMapInducedTopology Φ (A := A) (Y := Y))
        (ContinuousMapGeneratedBy.homeomorphInducedContinuousMap Φ (A := A) (Y := Y)))

/-- The whole forward function is conversion to an ordinary continuous map. -/
theorem coe_generatedMapProbeCompactOpen [IsGeneratedBy Φ A] :
    ⇑(generatedMapProbeCompactOpen Φ A Y) = ContinuousMapGeneratedBy.toContinuousMap Φ := rfl

/-- The forward homeomorphism is conversion to an ordinary continuous map. -/
@[simp]
theorem generatedMapProbeCompactOpen_apply [IsGeneratedBy Φ A]
    (f : ContinuousMapGeneratedBy Φ A Y) :
    generatedMapProbeCompactOpen Φ A Y f = ContinuousMapGeneratedBy.toContinuousMap Φ f := rfl

/-- The whole inverse function is conversion to a generated map. -/
theorem coe_generatedMapProbeCompactOpen_symm [IsGeneratedBy Φ A] :
    ⇑(@Homeomorph.symm (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
      inferInstance (ContinuousMap.probeCompactOpenTopology Φ A Y)
      (generatedMapProbeCompactOpen Φ A Y)) = ContinuousMapGeneratedBy.ofContinuousMap Φ := rfl

/-- The inverse homeomorphism is conversion to a generated map. -/
@[simp]
theorem generatedMapProbeCompactOpen_symm_apply [IsGeneratedBy Φ A]
    (f : @ContinuousMap A Y tA tY) :
    (@Homeomorph.symm (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
      inferInstance (ContinuousMap.probeCompactOpenTopology Φ A Y)
      (generatedMapProbeCompactOpen Φ A Y)) f = ContinuousMapGeneratedBy.ofContinuousMap Φ f := rfl

section Generated

variable [∀ i, LocallyCompactSpace (Φ i)]
  [∀ i, IsGeneratedBy Φ (Φ i × A)] [IsGeneratedBy Φ A]

/-- Refined generated maps on an original generated source are homeomorphic to
refined ordinary compact-open maps. Both refinements use the same probe family.

Only the ordinary products of probes with the original source need be generated;
no local compactness of the original source or generatedness of the target is
required. -/
def generatedByCompactOpen :
    @Homeomorph (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY)) := by
  exact @Homeomorph.trans (ContinuousMapGeneratedBy Φ A Y)
    (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
    (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
    (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
      (ContinuousMap.probeCompactOpenTopology Φ A Y))
    (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
      (@ContinuousMap.compactOpen A Y tA tY))
    (@Homeomorph.generatedByTopology ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance
      (@ContinuousMap A Y tA tY) (ContinuousMap.probeCompactOpenTopology Φ A Y)
      (generatedMapProbeCompactOpen Φ A Y))
    (generatedByProbeCompactOpen Φ A Y)

/-- The whole refined forward function is the ordinary continuous-map conversion. -/
theorem coe_generatedByCompactOpen :
    ⇑(generatedByCompactOpen Φ A Y) = ContinuousMapGeneratedBy.toContinuousMap Φ := rfl

/-- The refined homeomorphism has the prescribed forward conversion. -/
@[simp]
theorem generatedByCompactOpen_apply (f : ContinuousMapGeneratedBy Φ A Y) :
    generatedByCompactOpen Φ A Y f = ContinuousMapGeneratedBy.toContinuousMap Φ f := rfl

/-- The refined forward homeomorphism preserves every original value. -/
theorem generatedByCompactOpen_apply_apply (f : ContinuousMapGeneratedBy Φ A Y) (a : A) :
    generatedByCompactOpen Φ A Y f a = f a := rfl

/-- The whole refined inverse function is conversion to a generated map. -/
theorem coe_generatedByCompactOpen_symm :
    ⇑(@Homeomorph.symm (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY)) (generatedByCompactOpen Φ A Y)) =
      ContinuousMapGeneratedBy.ofContinuousMap Φ := rfl

/-- The refined inverse homeomorphism has the prescribed conversion. -/
@[simp]
theorem generatedByCompactOpen_symm_apply (f : @ContinuousMap A Y tA tY) :
    (@Homeomorph.symm (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY)) (generatedByCompactOpen Φ A Y)) f =
      ContinuousMapGeneratedBy.ofContinuousMap Φ f := rfl

/-- The refined inverse homeomorphism preserves every original value. -/
theorem generatedByCompactOpen_symm_apply_apply (f : @ContinuousMap A Y tA tY) (a : A) :
    (@Homeomorph.symm (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
      (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ A Y) inferInstance)
      (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY)) (generatedByCompactOpen Φ A Y)) f a = f a := rfl

/-- The refined comparison commutes as a whole function with ordinary source
precomposition and target postcomposition, using the canonical generated maps. -/
theorem generatedByCompactOpen_naturality
    {B : Type v'} [tB : TopologicalSpace B]
    [∀ i, IsGeneratedBy Φ (Φ i × B)] [IsGeneratedBy Φ B]
    {Z : Type w'} [tZ : TopologicalSpace Z] (p : C(B, A)) (g : C(Y, Z)) :
    (fun f : ContinuousMapGeneratedBy Φ A Y =>
      generatedByCompactOpen Φ B Z
        ((ContinuousMapGeneratedBy.ofContinuousMap Φ g).comp
          (f.comp (ContinuousMapGeneratedBy.ofContinuousMap Φ p)))) =
      (fun f : ContinuousMapGeneratedBy Φ A Y =>
        g.comp ((generatedByCompactOpen Φ A Y f).comp p)) := by
  funext f
  apply ContinuousMap.ext
  intro b
  rfl

/-- The inverse refined comparison also commutes as a whole function with ordinary
source precomposition and target postcomposition. -/
theorem generatedByCompactOpen_symm_naturality
    {B : Type v'} [tB : TopologicalSpace B]
    [∀ i, IsGeneratedBy Φ (Φ i × B)] [IsGeneratedBy Φ B]
    {Z : Type w'} [tZ : TopologicalSpace Z] (p : C(B, A)) (g : C(Y, Z)) :
    (fun f : @ContinuousMap A Y tA tY =>
      (@Homeomorph.symm (ContinuousMapGeneratedBy Φ B Z) (@ContinuousMap B Z tB tZ)
        (@TopologicalSpace.generatedBy ι Φ tΦ (ContinuousMapGeneratedBy Φ B Z) inferInstance)
        (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap B Z tB tZ)
          (@ContinuousMap.compactOpen B Z tB tZ)) (generatedByCompactOpen Φ B Z))
        (g.comp (f.comp p))) =
      (fun f : @ContinuousMap A Y tA tY =>
        (ContinuousMapGeneratedBy.ofContinuousMap Φ g).comp
          (((@Homeomorph.symm (ContinuousMapGeneratedBy Φ A Y) (@ContinuousMap A Y tA tY)
            (@TopologicalSpace.generatedBy ι Φ tΦ
              (ContinuousMapGeneratedBy Φ A Y) inferInstance)
            (@TopologicalSpace.generatedBy ι Φ tΦ (@ContinuousMap A Y tA tY)
              (@ContinuousMap.compactOpen A Y tA tY))
            (generatedByCompactOpen Φ A Y)) f).comp
            (ContinuousMapGeneratedBy.ofContinuousMap Φ p))) := by
  funext f
  apply DFunLike.ext
  intro b
  rfl

end Generated

end Homeomorph
