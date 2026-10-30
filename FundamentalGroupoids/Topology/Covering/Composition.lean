/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Cancellation of covering maps

If `q ∘ g` and `q` are covering maps, `g` is continuous, and the target of `g` is locally
connected, then `g` is a covering map. The common-base formulation
`IsCoveringMap.of_comp_eq` follows by transporting along the equality of composites.
The three spaces have independent universes. Neither covering map nor `g` needs to be
surjective, and empty fibers are allowed.

The proof restricts a raw evenly covered chart for the composite to a connected neighborhood
inside a local chart for `q`. Uniqueness of continuous lifts selects exactly the composite
sheets meeting this neighborhood. The selected sheet set may be empty, so the construction
uses `IsEvenlyCovered` directly rather than a trivialization requiring a nonempty model fiber.

## References

The chart and lift-uniqueness APIs are from
[Mathlib's covering maps](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Covering/Basic.lean),
by Thomas Browning. In particular, `IsCoveringMap.eq_of_comp_eq` supplies uniqueness of
continuous lifts, documented there as Hatcher's Proposition 1.34. Connected open
neighborhoods come from
[Mathlib's locally connected spaces](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Connected/LocallyConnected.lean),
by Anatole Dedecker. The restriction of a local chart uses Mathlib's
`OpenPartialHomeomorph.homeomorphOfImageSubsetSource`.
-/

@[expose] public section

open Set Topology

universe uE uF uB uI

namespace IsCoveringMap

variable {E : Type uE} {F : Type uF} {B : Type uB}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- Assemble an evenly covered chart from a composite chart and a connected local inverse
of the second covering map. The sheet set is selected by agreement at one point. -/
private theorem isEvenlyCovered_of_comp_chart {q : F → B} {g : E → F}
    (hq : IsCoveringMap q) (hg : Continuous g)
    {I : Type uI} [TopologicalSpace I] [DiscreteTopology I]
    {W : Set B} (H : (q ∘ g) ⁻¹' W ≃ₜ W × I)
    (hH : ∀ e, (H e).1.1 = (q ∘ g) e)
    {V : Set F} {U : Set B} [PreconnectedSpace U]
    (hV : IsOpen V) (hUW : U ⊆ W)
    (Q : V ≃ₜ U) (hQ : ∀ v, (Q v).1 = q v)
    {f : F} (hf : f ∈ V) : IsEvenlyCovered g f (g ⁻¹' {f}) := by
  let a : U → W := fun u ↦ ⟨u, hUW u.2⟩
  have ha : Continuous a := continuous_subtype_val.subtype_mk _
  let s : I → U → E := fun i u ↦ (H.symm (a u, i)).1
  have hs (i : I) : Continuous (s i) :=
    continuous_subtype_val.comp (H.symm.continuous.comp (ha.prodMk continuous_const))
  have hproj (i : I) (u : U) : q (g (s i u)) = u := by
    calc
      q (g (s i u)) = (H (H.symm (a u, i))).1.1 := (hH _).symm
      _ = u := by rw [H.apply_symm_apply]
  let t : U → F := fun u ↦ (Q.symm u).1
  have ht : Continuous t := continuous_subtype_val.comp Q.symm.continuous
  have htproj (u : U) : q (t u) = u := by
    calc
      q (t u) = (Q (Q.symm u)).1 := (hQ _).symm
      _ = u := congrArg Subtype.val (Q.apply_symm_apply u)
  have htQ (v : V) : t (Q v) = v :=
    congrArg Subtype.val (Q.symm_apply_apply v)
  let u₀ : U := Q ⟨f, hf⟩
  have ht₀ : t u₀ = f := htQ ⟨f, hf⟩
  let J := {i : I // g (s i u₀) = f}
  have lift_eq (i : I) (u : U) (hu : g (s i u) = t u) :
      (fun v ↦ g (s i v)) = t :=
    hq.eq_of_comp_eq (hg.comp (hs i)) ht
      (funext fun v ↦ (hproj i v).trans (htproj v).symm) u hu
  have hselected (j : J) (u : U) : g (s j.1 u) = t u :=
    congrFun (lift_eq j.1 u₀ (j.2.trans ht₀.symm)) u
  let b : g ⁻¹' V → V := fun e ↦ ⟨g e, e.2⟩
  let eW : g ⁻¹' V → (q ∘ g) ⁻¹' W :=
    fun e ↦ ⟨e, hUW (by
      change q (b e) ∈ U
      rw [← hQ (b e)]
      exact (Q (b e)).2)⟩
  have hfirst (e : g ⁻¹' V) : (H (eW e)).1 = a (Q (b e)) :=
    Subtype.ext ((hH _).trans (hQ (b e)).symm)
  have hs_label (e : g ⁻¹' V) : s (H (eW e)).2 (Q (b e)) = e := by
    change (H.symm (a (Q (b e)), (H (eW e)).2)).1 = e.1
    rw [← hfirst e]
    exact congrArg Subtype.val (H.symm_apply_apply (eW e))
  -- A sheet meeting the neighborhood is compared at that meeting point, not just at u₀.
  have label_selected (e : g ⁻¹' V) : g (s (H (eW e)).2 u₀) = f := by
    have heq := lift_eq (H (eW e)).2 (Q (b e)) (by
      rw [hs_label e]
      exact (htQ (b e)).symm)
    exact (congrFun heq u₀).trans ht₀
  let k : g ⁻¹' V → V × J :=
    fun e ↦ (b e, ⟨(H (eW e)).2, label_selected e⟩)
  let l : V × J → g ⁻¹' V := fun vj ↦ ⟨s vj.2.1 (Q vj.1), by
    change g (s vj.2.1 (Q vj.1)) ∈ V
    rw [hselected vj.2 (Q vj.1), htQ vj.1]
    exact vj.1.2⟩
  have hleft (e : g ⁻¹' V) : l (k e) = e :=
    Subtype.ext (hs_label e)
  have hright (vj : V × J) : k (l vj) = vj := by
    rcases vj with ⟨v, j⟩
    apply Prod.ext
    · apply Subtype.ext
      exact (hselected j (Q v)).trans (htQ v)
    · apply Subtype.ext
      change (H (eW (l (v, j)))).2 = j.1
      have he : eW (l (v, j)) = H.symm (a (Q v), j.1) := by
        apply Subtype.ext
        rfl
      rw [he, H.apply_symm_apply]
  have hb : Continuous b := (hg.comp continuous_subtype_val).subtype_mk _
  have heW : Continuous eW := continuous_subtype_val.subtype_mk _
  have hk_label : Continuous (fun e ↦ (⟨(H (eW e)).2, label_selected e⟩ : J)) :=
    (H.continuous.comp heW).snd.subtype_mk _
  have hk : Continuous k := hb.prodMk hk_label
  have hl_pre : Continuous (fun vj : V × J ↦ (a (Q vj.1), vj.2.1)) :=
    (ha.comp (Q.continuous.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hl : Continuous l :=
    (continuous_subtype_val.comp (H.symm.continuous.comp hl_pre)).subtype_mk _
  let K : g ⁻¹' V ≃ₜ V × J :=
    { toFun := k
      invFun := l
      left_inv := hleft
      right_inv := hright
      continuous_toFun := hk
      continuous_invFun := hl }
  have hraw : IsEvenlyCovered g f J :=
    ⟨inferInstance, V, hf, hV, hV.preimage hg, K, fun _ ↦ rfl⟩
  exact hraw.to_isEvenlyCovered_preimage

/-- Cancel a covering map from a composite of covering maps when the intermediate space is
locally connected and the first map is continuous. Empty fibers are allowed. The proof uses
Mathlib's evenly covered charts and uniqueness of continuous lifts (see the module references). -/
theorem of_comp [LocallyConnectedSpace F] {q : F → B} {g : E → F}
    (hcomp : IsCoveringMap (q ∘ g)) (hq : IsCoveringMap q)
    (hg : Continuous g) : IsCoveringMap g := by
  intro f
  obtain ⟨hI, W, hfW, hW, _, H, hH⟩ := hcomp (q f)
  let : DiscreteTopology ((q ∘ g) ⁻¹' {q f}) := hI
  obtain ⟨c, hfc, hc⟩ := hq.isLocalHomeomorph f
  obtain ⟨V, hVsub, hVopen, hfV, hVconn⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp
      (inferInstance : LocallyConnectedSpace F) f (c.source ∩ q ⁻¹' W)
      ((c.open_source.inter (hW.preimage hq.continuous)).mem_nhds ⟨hfc, hfW⟩)
  let U : Set B := q '' V
  have hUW : U ⊆ W := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hVsub hv).2
  have hUconn : IsConnected U := hVconn.image q hq.continuous.continuousOn
  let : PreconnectedSpace U := Subtype.preconnectedSpace hUconn.isPreconnected
  let Q : V ≃ₜ U := c.homeomorphOfImageSubsetSource
    (fun _ hv ↦ (hVsub hv).1) (congrArg (fun k : F → B ↦ k '' V) hc.symm)
  have hQ (v : V) : (Q v).1 = q v := by
    change c v = q v
    exact (congrFun hc v).symm
  exact isEvenlyCovered_of_comp_chart hq hg H hH hVopen hUW Q hQ hfV

/-- A continuous map over a common base between covering spaces is a covering map if its
target total space is locally connected. This is equality transport followed by
`IsCoveringMap.of_comp`; it does not require surjectivity or nonempty fibers. -/
theorem of_comp_eq [LocallyConnectedSpace F] {p : E → B} {q : F → B}
    (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (g : C(E, F)) (hcomp : q ∘ g = p) : IsCoveringMap g := by
  have hcomp' : IsCoveringMap (q ∘ g) := by
    rw [hcomp]
    exact hp
  exact of_comp hcomp' hq g.continuous

end IsCoveringMap
