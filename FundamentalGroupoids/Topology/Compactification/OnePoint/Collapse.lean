/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Constructions.SumProd

/-!
# Collapsing the complement of an open subspace

`OnePoint.collapse s` maps an ambient Hausdorff space to the one-point compactification
of an open subspace `s`, retaining the points of `s` and sending its complement to infinity.
`OnePoint.collapseWithPoint s` also sends a disjoint point to infinity, so it is surjective
even when `s` is the whole ambient space. For a compact ambient space this extension is a
quotient map. Neither construction requires `s` to be nonempty or proper.

The quotient-map theorem gives access to the descent API
`Topology.IsQuotientMap.lift` and `Topology.IsQuotientMap.liftEquiv`.

## References

* Mathlib's `Mathlib.Topology.Compactification.OnePoint.Basic`, by Yourong Zang and
  Yury Kudryashov, supplies the one-point compactification and its topology.
* Mathlib's `Mathlib.Topology.Constructions.SumProd` supplies `Continuous.sumElim`.
* Mathlib's `Mathlib.Topology.ContinuousMap.Basic` supplies quotient-map descent.
-/

@[expose] public section

universe u

open scoped OnePoint

namespace OnePoint

variable {K : Type u} [TopologicalSpace K]

/-- Map an ambient Hausdorff space to the one-point compactification of an open subspace,
sending every point outside the subspace to infinity. -/
noncomputable def collapse [T2Space K] (s : TopologicalSpace.Opens K) :
    C(K, OnePoint s) := by
  classical
  exact
    { toFun := fun k => if hk : k ∈ s then ↑(⟨k, hk⟩ : s) else ∞
      continuous_toFun := by
        refine continuous_def.mpr fun V hV => ?_
        rcases OnePoint.isOpen_def.mp hV with ⟨hcompact, hopen⟩
        by_cases hinfty : (∞ : OnePoint s) ∈ V
        · -- The Hausdorff hypothesis makes the compact ambient image closed.
          have hclosed : IsClosed ((Subtype.val : s → K) ''
              (((↑) : s → OnePoint s) ⁻¹' V)ᶜ) :=
            ((hcompact hinfty).image continuous_subtype_val).isClosed
          convert hclosed.isOpen_compl using 1
          ext k
          by_cases hk : k ∈ s <;> simp [hk, hinfty, Subtype.coe_image]
        · convert s.isOpen.isOpenMap_subtype_val _ hopen using 1
          ext k
          by_cases hk : k ∈ s <;> simp [hk, hinfty, Subtype.coe_image] }

variable [T2Space K]

/-- On a point of the open subspace, the collapse map is the canonical inclusion. -/
@[simp]
theorem collapse_of_mem (s : TopologicalSpace.Opens K) {k : K} (hk : k ∈ s) :
    collapse s k = ↑(⟨k, hk⟩ : s) := by
  classical
  simp only [collapse, ContinuousMap.coe_mk, dite_eq_left hk]

/-- Every point outside the open subspace is sent to infinity. -/
@[simp]
theorem collapse_of_notMem (s : TopologicalSpace.Opens K) {k : K} (hk : k ∉ s) :
    collapse s k = ∞ := by
  classical
  simp only [collapse, ContinuousMap.coe_mk, dite_eq_right hk]

theorem collapse_coe (s : TopologicalSpace.Opens K) (k : s) :
    collapse s (k : K) = (k : OnePoint s) :=
  collapse_of_mem s k.property

/-- The points sent to infinity are exactly the complement of the open subspace. -/
@[simp]
theorem collapse_eq_infty_iff (s : TopologicalSpace.Opens K) (k : K) :
    collapse s k = ∞ ↔ k ∉ s := by
  classical
  by_cases hk : k ∈ s <;> simp [hk]

/-- Extend the collapse map by a disjoint point sent to infinity. -/
noncomputable def collapseWithPoint (s : TopologicalSpace.Opens K) :
    C(K ⊕ PUnit.{u + 1}, OnePoint s) where
  toFun := Sum.elim (collapse s) (ContinuousMap.const PUnit.{u + 1} ∞)
  continuous_toFun := (map_continuous (collapse s)).sumElim
    (map_continuous (ContinuousMap.const PUnit.{u + 1} (∞ : OnePoint s)))

@[simp]
theorem collapseWithPoint_inl (s : TopologicalSpace.Opens K) (k : K) :
    collapseWithPoint s (Sum.inl k) = collapse s k :=
  rfl

@[simp]
theorem collapseWithPoint_inr (s : TopologicalSpace.Opens K) (p : PUnit.{u + 1}) :
    collapseWithPoint s (Sum.inr p) = ∞ :=
  rfl

/-- The disjoint point ensures surjectivity, without compactness of the ambient space. -/
theorem surjective_collapseWithPoint (s : TopologicalSpace.Opens K) :
    Function.Surjective (collapseWithPoint s) := by
  intro y
  refine OnePoint.rec ?_ (fun k => ?_) y
  · exact ⟨Sum.inr PUnit.unit, rfl⟩
  · exact ⟨Sum.inl (k : K), collapse_coe s k⟩

/-- For a compact Hausdorff ambient space, collapsing the complement of an open subspace
and a disjoint point to infinity is a quotient map onto its one-point compactification. -/
theorem isQuotientMap_collapseWithPoint [CompactSpace K] (s : TopologicalSpace.Opens K) :
    Topology.IsQuotientMap (collapseWithPoint s) := by
  let : LocallyCompactSpace s := s.isOpen.locallyCompactSpace
  exact Topology.IsQuotientMap.of_surjective_continuous
    (surjective_collapseWithPoint s) (map_continuous (collapseWithPoint s))

end OnePoint
