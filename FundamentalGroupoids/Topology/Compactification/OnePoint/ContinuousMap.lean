/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Compactification.OnePoint.Collapse
public import GroupTheory.Topology.ContinuousMap.CompactCovering

/-!
# Based continuous maps out of an open-subspace compactification

For an open subspace `s` of a compact Hausdorff space `K`, pullback along
`OnePoint.collapse s` identifies maps from `OnePoint s` taking infinity to `x`
with continuous maps from `K` equal to `x` outside `s`. Both mapping spaces have
the subspace topology inherited from the ordinary compact-open topology.

The inverse extends the restriction to `s` by the prescribed value `x` at
infinity. The target space requires only a topology. The open subspace may be
empty or all of `K`.

## References

* Mathlib's `Mathlib.Topology.Compactification.OnePoint.Basic`, by Yourong Zang
  and Yury Kudryashov, supplies `OnePoint` and its recursor.
* Mathlib supplies the compact-open topology and continuity of precomposition.
* Mathlib supplies continuous descent through quotient maps.
* Group Theory's `GroupTheory.Topology.ContinuousMap.CompactCovering` supplies
  `ContinuousMap.isEmbedding_precomp_of_compactCovering` for the inverse family.
-/

@[expose] public section

universe u v

open scoped OnePoint

namespace OnePoint

section

variable {K : Type u} [TopologicalSpace K] [T2Space K]
  (s : TopologicalSpace.Opens K) {X : Type v} [TopologicalSpace X] (x : X)

private theorem rec_collapseWithPoint
    (f : {f : C(K, X) // ∀ k, k ∉ s → f k = x}) (z : K ⊕ PUnit.{u + 1}) :
    OnePoint.rec x (fun k : s => f.val k.val) (collapseWithPoint s z) =
      Sum.elim f.val (fun _ : PUnit.{u + 1} => x) z := by
  rcases z with k | p
  · change OnePoint.rec x (fun k : s => f.val k.val) (collapse s k) = f.val k
    by_cases hk : k ∈ s
    · rw [collapse_of_mem s hk]
      rfl
    · rw [collapse_of_notMem s hk]
      exact (f.property k hk).symm
  · rfl

private theorem compactCovering_collapseWithPoint [CompactSpace K] :
    ∀ C : Set (OnePoint s), IsCompact C →
      ∃ L : Set (K ⊕ PUnit.{u + 1}), IsCompact L ∧ collapseWithPoint s '' L = C := by
  let : LocallyCompactSpace s := s.isOpen.locallyCompactSpace
  intro C hC
  refine ⟨collapseWithPoint s ⁻¹' C,
    (hC.isClosed.preimage (map_continuous (collapseWithPoint s))).isCompact, ?_⟩
  exact Set.image_preimage_eq C (surjective_collapseWithPoint s)

end

/-- Pullback along the collapse of the complement of an open subspace of a compact
Hausdorff space. The inverse restricts the ambient map to the open subspace and
assigns the prescribed value at infinity. -/
noncomputable def collapsePullbackHomeomorph
    {K : Type u} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    (s : TopologicalSpace.Opens K) {X : Type v} [TopologicalSpace X] (x : X) :
    {F : C(OnePoint s, X) // F ∞ = x} ≃ₜ
      {f : C(K, X) // ∀ k, k ∉ s → f k = x} where
  toFun F := ⟨F.val.comp (collapse s), by
    intro k hk
    change F.val (collapse s k) = x
    rw [collapse_of_notMem s hk]
    exact F.property⟩
  invFun f := ⟨
    { toFun := OnePoint.rec x (fun k : s => f.val k.val)
      continuous_toFun := by
        apply (isQuotientMap_collapseWithPoint s).continuous_iff.mpr
        simpa only [Function.comp_def, rec_collapseWithPoint s x f] using
          f.val.continuous.sumElim
            (continuous_const : Continuous (fun _ : PUnit.{u + 1} => x)) }, rfl⟩
  left_inv := by
    intro F
    apply Subtype.ext
    apply ContinuousMap.ext
    intro z
    induction z using OnePoint.rec with
    | infty => exact F.property.symm
    | coe k =>
      change F.val (collapse s k.val) = F.val (k : OnePoint s)
      rw [collapse_coe s k]
  right_inv := by
    intro f
    apply Subtype.ext
    apply ContinuousMap.ext
    intro k
    exact rec_collapseWithPoint s x f (Sum.inl k)
  continuous_toFun :=
    ((ContinuousMap.continuous_precomp (collapse s)).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    -- The extra point covers infinity even when the open subspace is the whole space.
    have hEmb := ContinuousMap.isEmbedding_precomp_of_compactCovering
      (T := X) (collapseWithPoint s) (compactCovering_collapseWithPoint s)
    apply hEmb.isInducing.continuous_iff.mpr
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : {f : C(K, X) // ∀ k, k ∉ s → f k = x} ×
        (K ⊕ PUnit.{u + 1}) =>
      (OnePoint.rec x (fun k : s => p.1.val k.val) (collapseWithPoint s p.2) : X))
    simp_rw [rec_collapseWithPoint s x]
    rw [← Homeomorph.prodSumDistrib.symm.comp_continuous_iff']
    refine continuous_sum_dom.mpr ⟨?_, ?_⟩
    · exact (continuous_subtype_val.comp continuous_fst).eval continuous_snd
    · exact continuous_const

variable {K : Type u} [TopologicalSpace K] [T2Space K] [CompactSpace K]
  (s : TopologicalSpace.Opens K) {X : Type v} [TopologicalSpace X] (x : X)

/-- The underlying forward map is precomposition by the collapse map. -/
@[simp]
theorem coe_collapsePullbackHomeomorph_apply
    (F : {F : C(OnePoint s, X) // F ∞ = x}) :
    (collapsePullbackHomeomorph s x F).val = F.val.comp (collapse s) :=
  rfl

/-- Evaluate a pulled-back map at any point of the ambient space. -/
@[simp]
theorem collapsePullbackHomeomorph_apply_apply
    (F : {F : C(OnePoint s, X) // F ∞ = x}) (k : K) :
    (collapsePullbackHomeomorph s x F).val k = F.val (collapse s k) :=
  rfl

/-- The inverse is the one-point recursor with the prescribed value at infinity
and the restriction of the ambient map at points of the open subspace. -/
theorem coe_collapsePullbackHomeomorph_symm_apply
    (f : {f : C(K, X) // ∀ k, k ∉ s → f k = x}) :
    ⇑((collapsePullbackHomeomorph s x).symm f).val =
      OnePoint.rec x (fun k : s => f.val k.val) :=
  rfl

/-- The extension has the prescribed value at infinity. -/
@[simp]
theorem collapsePullbackHomeomorph_symm_apply_infty
    (f : {f : C(K, X) // ∀ k, k ∉ s → f k = x}) :
    ((collapsePullbackHomeomorph s x).symm f).val ∞ = x :=
  rfl

/-- At a point of the open subspace, the extension evaluates the original map. -/
@[simp]
theorem collapsePullbackHomeomorph_symm_apply_coe
    (f : {f : C(K, X) // ∀ k, k ∉ s → f k = x}) (k : s) :
    ((collapsePullbackHomeomorph s x).symm f).val (k : OnePoint s) = f.val k.val :=
  rfl

end OnePoint
