/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.CompactOpen

/-!
# Partial evaluation in the compact-open topology

Partial evaluation `P × C(P × X, Z) → C(X, Z)` is continuous when the parameter
space `P` is locally compact. No local compactness or separation assumption is
needed on `X` or `Z`. The proof combines the compact-tube lemma with a compact
neighborhood in `P` and a compact-open neighborhood of the map.

Parameterized precomposition and continuity of the curry operator follow from
this same partial-evaluation map, using fixed precomposition and swapping the
factors, respectively. The curry operator agrees with the usual continuous
curry operator when `P × X` is also locally compact.
-/

@[expose] public section

open Set Filter Topology

universe uP uX uY uZ

namespace ContinuousMap

variable {P : Type uP} {X : Type uX} {Y : Type uY} {Z : Type uZ}
  [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Joint partial evaluation is continuous if the parameter space is locally compact.
The source and target of the resulting maps need not be locally compact or separated. -/
theorem continuous_curry_apply [LocallyCompactSpace P] :
    Continuous (fun q : P × C(P × X, Z) => q.2.curry q.1) := by
  refine continuous_iff_continuousAt.2 fun q => ?_
  apply tendsto_nhds_compactOpen.2
  intro K hK U hU hq
  -- The tube is obtained using compactness of K, not local compactness of X.
  have htube : q.2 ⁻¹' U ∈ (𝓝 q.1) ×ˢ 𝓝ˢ K := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro x hx
    simpa only [nhds_prod_eq] using
      (show q.2 ⁻¹' U ∈ 𝓝 (q.1, x) from
        q.2.continuous.continuousAt (hU.mem_nhds (hq hx)))
  rcases mem_prod_iff.1 htube with ⟨V, hV, W, hW, hVW⟩
  rcases local_compact_nhds hV with ⟨L, hL, hLV, hLc⟩
  -- L × K is compact even when neither X nor Z has any separation property.
  have hmaps : MapsTo q.2 (L ×ˢ K) U := by
    rintro ⟨p, x⟩ ⟨hp, hx⟩
    exact hVW ⟨hLV hp, subset_of_mem_nhdsSet hW hx⟩
  have hG : {g : C(P × X, Z) | MapsTo g (L ×ˢ K) U} ∈ 𝓝 q.2 :=
    eventually_mapsTo (hLc.prod hK) hU hmaps
  change {r : P × C(P × X, Z) | MapsTo (r.2.curry r.1) K U} ∈ 𝓝 (q.1, q.2)
  rw [nhds_prod_eq]
  refine mem_of_superset (prod_mem_prod hL hG) ?_
  rintro ⟨p, g⟩ ⟨hp, hg⟩ x hx
  exact hg ⟨hp, hx⟩

/-- Precomposition along a continuous family is jointly continuous when its parameter
space is locally compact, without local compactness assumptions on the mapping spaces. -/
theorem continuous_comp_curry [LocallyCompactSpace P] (F : C(P × X, Y)) :
    Continuous (fun q : P × C(Y, Z) => q.2.comp (F.curry q.1)) :=
  continuous_curry_apply.comp
    (continuous_fst.prodMk ((compRightContinuousMap Z F).continuous.comp continuous_snd))

/-- The curry operator is continuous when its first factor `P` is locally compact.
Unlike `continuous_curry`, this does not require local compactness of `P × X`. -/
theorem continuous_curry_of_locallyCompact_left [LocallyCompactSpace P] :
    Continuous (curry : C(P × X, Z) → C(P, C(X, Z))) :=
  continuous_of_continuous_uncurry _ (continuous_curry_apply.comp continuous_swap)

/-- On the overlap of the locally compact parameter and locally compact product
hypotheses, the two bundled continuous curry operators agree. -/
theorem curry_operator_eq [LocallyCompactSpace P] [LocallyCompactSpace (P × X)] :
    (⟨curry, continuous_curry_of_locallyCompact_left⟩ :
      C(C(P × X, Z), C(P, C(X, Z)))) = ⟨curry, continuous_curry⟩ := by
  rfl

end ContinuousMap
