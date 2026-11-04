/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Convenient.GeneratedBy.Basic
public import Mathlib.Topology.CompactOpen

/-!
# Compact-open topology tested by a family of probes

The carrier is the space of continuous maps for the original topologies on the
source and target. The probe compact-open topology is initial for precomposition
by every continuous map from a probe, with ordinary compact-open topology on each
coordinate space.

For locally compact probes whose ordinary products with the source are generated
by the same family, this topology and the ordinary compact-open topology have the
same continuous probes. Their generated refinements are therefore equal, and the
identity on continuous maps gives a homeomorphism between them. Neither local
compactness nor generatedness of the original source is required.

The probe index, probe spaces, source and target have independent universes. Both
generated refinements are retained in the comparison.

## References

The probe refinement uses Mathlib's [generated-by topology](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/GeneratedBy.lean),
by Joël Riou, Dagur Asgeirsson and Ben Eltschig, together with Mathlib's ordinary
compact-open topology and precomposition API. The comparison is stated on the
original continuous-map carrier rather than a new generated-map model.
-/

@[expose] public section

noncomputable section

universe t u v w v' w' z

open Topology

namespace ContinuousMap

variable {ι : Type t} (X : ι → Type u) [tX : ∀ i, TopologicalSpace (X i)]
  (A : Type v) [tA : TopologicalSpace A] (Y : Type w) [tY : TopologicalSpace Y]

/-- The initial topology on ordinary continuous maps for all probe precompositions.
The named original topologies determine the carrier and all probe maps. -/
abbrev probeCompactOpenTopology : TopologicalSpace (@ContinuousMap A Y tA tY) :=
  ⨅ (i : ι) (p : @ContinuousMap (X i) A (tX i) tA),
    TopologicalSpace.induced
      (fun f : @ContinuousMap A Y tA tY => f.comp p)
      (@ContinuousMap.compactOpen (X i) Y (tX i) tY)

/-- Continuity into the probe compact-open topology is equivalent to continuity of
all precomposition coordinates, for an arbitrary source space. -/
theorem continuous_probeCompactOpen_iff
    {Z : Type z} [tZ : TopologicalSpace Z]
    {h : Z → @ContinuousMap A Y tA tY} :
    @Continuous Z (@ContinuousMap A Y tA tY) tZ
        (probeCompactOpenTopology X A Y) h ↔
      ∀ (i : ι) (p : @ContinuousMap (X i) A (tX i) tA),
        @Continuous Z (@ContinuousMap (X i) Y (tX i) tY) tZ
          (@ContinuousMap.compactOpen (X i) Y (tX i) tY)
          (fun z => (h z).comp p) := by
  simp only [continuous_iInf_rng, continuous_induced_rng, Function.comp_def]

/-- Every probe precomposition coordinate is continuous for the probe compact-open
topology, with ordinary compact-open topology on its target. -/
theorem continuous_probeCompactOpen_precomp
    {i : ι} (p : @ContinuousMap (X i) A (tX i) tA) :
    @Continuous (@ContinuousMap A Y tA tY)
      (@ContinuousMap (X i) Y (tX i) tY)
      (probeCompactOpenTopology X A Y)
      (@ContinuousMap.compactOpen (X i) Y (tX i) tY)
      (fun f => f.comp p) := by
  exact ((continuous_probeCompactOpen_iff X A Y
    (tZ := probeCompactOpenTopology X A Y) (h := id)).1
      (@continuous_id (@ContinuousMap A Y tA tY)
        (probeCompactOpenTopology X A Y))) i p

/-- Ordinary compact-open topology is finer than the probe compact-open topology.
This direction needs no local compactness or generatedness assumption. -/
theorem continuous_compactOpen_to_probeCompactOpen :
    @Continuous (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
      (@ContinuousMap.compactOpen A Y tA tY)
      (probeCompactOpenTopology X A Y) id := by
  apply (continuous_probeCompactOpen_iff X A Y).2
  intro i p
  exact continuous_precomp p

/-- Precomposition by an ordinary continuous map is continuous between the probe
compact-open topologies. -/
theorem continuous_precomp_probeCompactOpen
    {B : Type v'} [tB : TopologicalSpace B] (p : C(B, A)) :
    @Continuous (@ContinuousMap A Y tA tY) (@ContinuousMap B Y tB tY)
      (probeCompactOpenTopology X A Y) (probeCompactOpenTopology X B Y)
      (fun f => f.comp p) := by
  apply (continuous_probeCompactOpen_iff X B Y
    (tZ := probeCompactOpenTopology X A Y)).2
  intro i q
  exact continuous_probeCompactOpen_precomp X A Y (p.comp q)

/-- Postcomposition by an ordinary continuous map is continuous between the probe
compact-open topologies. -/
theorem continuous_postcomp_probeCompactOpen
    {Z : Type w'} [tZ : TopologicalSpace Z] (g : C(Y, Z)) :
    @Continuous (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
      (probeCompactOpenTopology X A Y) (probeCompactOpenTopology X A Z)
      (fun f => g.comp f) := by
  apply (continuous_probeCompactOpen_iff X A Z
    (tZ := probeCompactOpenTopology X A Y)).2
  intro i p
  let c : @ContinuousMap (@ContinuousMap A Y tA tY)
      (@ContinuousMap (X i) Y (tX i) tY)
      (probeCompactOpenTopology X A Y)
      (@ContinuousMap.compactOpen (X i) Y (tX i) tY) :=
    @ContinuousMap.mk (@ContinuousMap A Y tA tY)
      (@ContinuousMap (X i) Y (tX i) tY) (probeCompactOpenTopology X A Y)
      (@ContinuousMap.compactOpen (X i) Y (tX i) tY)
      (fun f => f.comp p) (continuous_probeCompactOpen_precomp X A Y p)
  let d : C(C(X i, Y), C(X i, Z)) :=
    ⟨fun f => g.comp f, continuous_postcomp g⟩
  exact @ContinuousMap.continuous (@ContinuousMap A Y tA tY)
    (@ContinuousMap (X i) Z (tX i) tZ)
    (probeCompactOpenTopology X A Y)
    (@ContinuousMap.compactOpen (X i) Z (tX i) tZ)
    (@ContinuousMap.comp (@ContinuousMap A Y tA tY)
      (@ContinuousMap (X i) Y (tX i) tY) (@ContinuousMap (X i) Z (tX i) tZ)
      (probeCompactOpenTopology X A Y)
      (@ContinuousMap.compactOpen (X i) Y (tX i) tY)
      (@ContinuousMap.compactOpen (X i) Z (tX i) tZ) d c)

section Comparison

variable [∀ i, LocallyCompactSpace (X i)] [∀ i, IsGeneratedBy X (X i × A)]

/-- For each probe, continuity of a family into the probe compact-open topology is
equivalent to continuity into ordinary compact-open topology.

For the nontrivial direction, joint evaluation is tested against maps from probes
into the ordinary product of the parameter probe and the source. Evaluation then
occurs on a probe, so only local compactness of the probes is used. -/
theorem continuous_probeCompactOpen_iff_compactOpen
    {i : ι} {h : X i → @ContinuousMap A Y tA tY} :
    @Continuous (X i) (@ContinuousMap A Y tA tY) (tX i)
        (probeCompactOpenTopology X A Y) h ↔
      @Continuous (X i) (@ContinuousMap A Y tA tY) (tX i)
        (@ContinuousMap.compactOpen A Y tA tY) h := by
  constructor
  · intro hh
    apply continuous_of_continuous_uncurry h
    apply (IsGeneratedBy.continuous_iff (X := X)
      (fun z : X i × A => h z.1 z.2)).2
    intro j q
    let p : C(X j, A) := (ContinuousMap.snd : C(X i × A, A)).comp q
    let r : C(X j, X i) := (ContinuousMap.fst : C(X i × A, X i)).comp q
    let k : C(X i, C(X j, Y)) :=
      ⟨fun x => (h x).comp p, (continuous_probeCompactOpen_iff X A Y).1 hh j p⟩
    exact (continuous_uncurry_of_continuous k).comp
      (r.continuous.prodMk continuous_id)
  · intro hh
    let hmap : @ContinuousMap (X i) (@ContinuousMap A Y tA tY) (tX i)
        (@ContinuousMap.compactOpen A Y tA tY) := ⟨h, hh⟩
    let e : @ContinuousMap (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY) (probeCompactOpenTopology X A Y) :=
      @ContinuousMap.mk (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY) (probeCompactOpenTopology X A Y)
        id (continuous_compactOpen_to_probeCompactOpen X A Y)
    exact @ContinuousMap.continuous (X i) (@ContinuousMap A Y tA tY) (tX i)
      (probeCompactOpenTopology X A Y)
      (@ContinuousMap.comp (X i) (@ContinuousMap A Y tA tY)
        (@ContinuousMap A Y tA tY) (tX i)
        (@ContinuousMap.compactOpen A Y tA tY) (probeCompactOpenTopology X A Y) e hmap)

/-- Generated refinement identifies the probe compact-open topology with ordinary
compact-open topology when probes are locally compact and their ordinary products
with the source are generated by the same family. -/
theorem generatedBy_probeCompactOpen_eq_compactOpen :
    @TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (probeCompactOpenTopology X A Y) =
      @TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY) := by
  let M := @ContinuousMap A Y tA tY
  let τAux : TopologicalSpace M := probeCompactOpenTopology X A Y
  let τCO : TopologicalSpace M := @ContinuousMap.compactOpen A Y tA tY
  let τΓAux : TopologicalSpace M := @TopologicalSpace.generatedBy ι X tX M τAux
  have hidem : @TopologicalSpace.generatedBy ι X tX M τΓAux = τΓAux := by
    exact @TopologicalSpace.generatedBy_generatedBy ι X tX M τAux
  let hgen : @IsGeneratedBy ι X tX M τΓAux :=
    (@IsGeneratedBy.iff_le_generatedBy ι X tX M τΓAux).2 (le_of_eq hidem.symm)
  have htoAux : @Continuous M M τΓAux τAux id :=
    (@continuous_id_iff_le M τΓAux τAux).2
      (@TopologicalSpace.generatedBy_le ι X tX M τAux)
  have htoCO : @Continuous M M τΓAux τCO id := by
    apply (@IsGeneratedBy.continuous_iff ι X tX M τΓAux M τCO hgen id).2
    intro i p
    have hpAux : @Continuous (X i) M (tX i) τAux (⇑p) :=
      @Continuous.comp (X i) M M (tX i) τΓAux τAux (⇑p) id htoAux
        (@ContinuousMap.continuous (X i) M (tX i) τΓAux p)
    have hpCO : @Continuous (X i) M (tX i) τCO (⇑p) :=
      (continuous_probeCompactOpen_iff_compactOpen X A Y
        (tX := tX) (tA := tA) (tY := tY) (i := i) (h := (⇑p))).1 hpAux
    exact hpCO
  have hleCO : τΓAux ≤ τCO :=
    (@continuous_id_iff_le M τΓAux τCO).1 htoCO
  have hleft : τΓAux ≤ @TopologicalSpace.generatedBy ι X tX M τCO := by
    calc
      τΓAux = @TopologicalSpace.generatedBy ι X tX M τΓAux := hidem.symm
      _ ≤ @TopologicalSpace.generatedBy ι X tX M τCO :=
        @TopologicalSpace.generatedBy_mono ι X tX M τΓAux τCO hleCO
  have hordinary : τCO ≤ τAux :=
    (@continuous_id_iff_le M τCO τAux).1
      (continuous_compactOpen_to_probeCompactOpen X A Y
        (tX := tX) (tA := tA) (tY := tY))
  have hright : @TopologicalSpace.generatedBy ι X tX M τCO ≤ τΓAux :=
    @TopologicalSpace.generatedBy_mono ι X tX M τCO τAux hordinary
  exact le_antisymm hleft hright

end Comparison

end ContinuousMap

namespace Homeomorph

variable {ι : Type t} (X : ι → Type u) [tX : ∀ i, TopologicalSpace (X i)]
  (A : Type v) [tA : TopologicalSpace A] (Y : Type w) [tY : TopologicalSpace Y]
  [∀ i, LocallyCompactSpace (X i)] [∀ i, IsGeneratedBy X (X i × A)]

/-- The value-identity homeomorphism from the generated probe compact-open topology
to the generated ordinary compact-open topology.

The carrier consists of continuous maps for the original source and target
topologies. Only the probes are assumed locally compact; generatedness is required
of their ordinary products with the source, not of the source or target alone. -/
def generatedByProbeCompactOpen :
    @Homeomorph (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
      (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (ContinuousMap.probeCompactOpenTopology X A Y))
      (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY)) :=
  @Homeomorph.mk (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
    (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
      (ContinuousMap.probeCompactOpenTopology X A Y))
    (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
      (@ContinuousMap.compactOpen A Y tA tY))
    (Equiv.refl (@ContinuousMap A Y tA tY))
    (by
      change @Continuous (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
        (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
          (ContinuousMap.probeCompactOpenTopology X A Y))
        (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY)) id
      rw [ContinuousMap.generatedBy_probeCompactOpen_eq_compactOpen X A Y]
      exact @continuous_id (@ContinuousMap A Y tA tY)
        (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY)))
    (by
      change @Continuous (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
        (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY))
        (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
          (ContinuousMap.probeCompactOpenTopology X A Y)) id
      rw [ContinuousMap.generatedBy_probeCompactOpen_eq_compactOpen X A Y]
      exact @continuous_id (@ContinuousMap A Y tA tY)
        (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY)))

/-- The whole function underlying the generated compact-open comparison is the
identity on ordinary continuous maps. -/
theorem coe_generatedByProbeCompactOpen :
    ⇑(generatedByProbeCompactOpen X A Y) =
      (id : @ContinuousMap A Y tA tY → @ContinuousMap A Y tA tY) := rfl

/-- The generated compact-open comparison preserves each continuous map. -/
@[simp]
theorem generatedByProbeCompactOpen_apply (f : @ContinuousMap A Y tA tY) :
    generatedByProbeCompactOpen X A Y f = f := rfl

/-- The generated compact-open comparison preserves every value. -/
theorem generatedByProbeCompactOpen_apply_apply
    (f : @ContinuousMap A Y tA tY) (a : A) :
    generatedByProbeCompactOpen X A Y f a = f a := rfl

/-- The whole inverse function is also the identity on ordinary continuous maps. -/
theorem coe_generatedByProbeCompactOpen_symm :
    ⇑(@Homeomorph.symm (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
      (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (ContinuousMap.probeCompactOpenTopology X A Y))
      (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY)) (generatedByProbeCompactOpen X A Y)) =
      (id : @ContinuousMap A Y tA tY → @ContinuousMap A Y tA tY) := rfl

/-- The inverse generated compact-open comparison preserves each continuous map. -/
@[simp]
theorem generatedByProbeCompactOpen_symm_apply (f : @ContinuousMap A Y tA tY) :
    (@Homeomorph.symm (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
      (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (ContinuousMap.probeCompactOpenTopology X A Y))
      (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY)) (generatedByProbeCompactOpen X A Y)) f = f := rfl

/-- The inverse generated compact-open comparison preserves every value. -/
theorem generatedByProbeCompactOpen_symm_apply_apply
    (f : @ContinuousMap A Y tA tY) (a : A) :
    (@Homeomorph.symm (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
      (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (ContinuousMap.probeCompactOpenTopology X A Y))
      (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
        (@ContinuousMap.compactOpen A Y tA tY)) (generatedByProbeCompactOpen X A Y)) f a =
      f a := rfl

/-- The generated compact-open comparison commutes, as a whole function on
continuous maps, with simultaneous precomposition and postcomposition. -/
theorem generatedByProbeCompactOpen_naturality
    {B : Type v'} [tB : TopologicalSpace B] [∀ i, IsGeneratedBy X (X i × B)]
    {Z : Type w'} [tZ : TopologicalSpace Z] (p : C(B, A)) (g : C(Y, Z)) :
    (fun f : @ContinuousMap A Y tA tY =>
      generatedByProbeCompactOpen X B Z (g.comp (f.comp p))) =
      (fun f : @ContinuousMap A Y tA tY =>
        g.comp ((generatedByProbeCompactOpen X A Y f).comp p)) := rfl

/-- The inverse generated compact-open comparison also commutes, as a whole
function, with simultaneous precomposition and postcomposition. -/
theorem generatedByProbeCompactOpen_symm_naturality
    {B : Type v'} [tB : TopologicalSpace B] [∀ i, IsGeneratedBy X (X i × B)]
    {Z : Type w'} [tZ : TopologicalSpace Z] (p : C(B, A)) (g : C(Y, Z)) :
    (fun f : @ContinuousMap A Y tA tY =>
      (@Homeomorph.symm (@ContinuousMap B Z tB tZ) (@ContinuousMap B Z tB tZ)
        (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap B Z tB tZ)
          (ContinuousMap.probeCompactOpenTopology X B Z))
        (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap B Z tB tZ)
          (@ContinuousMap.compactOpen B Z tB tZ)) (generatedByProbeCompactOpen X B Z))
        (g.comp (f.comp p))) =
      (fun f : @ContinuousMap A Y tA tY =>
        g.comp (((@Homeomorph.symm (@ContinuousMap A Y tA tY) (@ContinuousMap A Y tA tY)
          (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
            (ContinuousMap.probeCompactOpenTopology X A Y))
          (@TopologicalSpace.generatedBy ι X tX (@ContinuousMap A Y tA tY)
            (@ContinuousMap.compactOpen A Y tA tY))
          (generatedByProbeCompactOpen X A Y)) f).comp p)) := rfl

end Homeomorph
