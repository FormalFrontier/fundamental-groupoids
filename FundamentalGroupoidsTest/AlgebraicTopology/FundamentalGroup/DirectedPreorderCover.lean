/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.DirectedOpenCover
import all FundamentalGroupoidsTest.AlgebraicTopology.FundamentalGroup.DirectedOpenCover
import all FundamentalGroupoidsTest.FundamentalGroup
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Directed
import Mathlib.Order.SupClosed

/-!
# Finite neighborhood families with ordinary inclusion arrows

Nonempty finite collections of neighborhoods in the circle-and-discrete-points cover
form a directed preorder under family inclusion. Their finite unions give a monotone
open cover. Two nested, intersection-closed collections have the same proper union,
although the larger collection has no arrow to the smaller one in this preorder.
The nonidentity circle classes and retractions are reused from the existing fixture.
Canonical colimit descent for the finite-family preorder, applied to the compatible
circle projections, recovers the original nonidentity circle class from its ambient image.

## Implementation notes

The fixture is imported with `import all` to reuse its private model and proofs.
The whole original chart range is not intersection-closed; no directedness assertion
is made about the subtype of intersection-closed finite families over that range.

## References

* `FundamentalGroupoidsTest.AlgebraicTopology.FundamentalGroup.DirectedOpenCover`
  supplies the space, cover, proper charts, nonidentity circle classes and retractions.
* Mathlib supplies the inherited finset/subtype order and nonempty finite joins.
-/

noncomputable section

open TopologicalSpace

namespace CircleFiniteSubsetCover

private abbrev Family :=
  {F : Finset (OpenNhds (X := TopCat.of X) point) //
    F.Nonempty ∧
      (↑F : Set (OpenNhds (X := TopCat.of X) point)) ⊆ Set.range W}

private def unionNhds (F : Family) : OpenNhds (X := TopCat.of X) point :=
  F.val.sup' F.property.1 id

private theorem unionNhds_le_iff (F : Family)
    (N : OpenNhds (X := TopCat.of X) point) :
    unionNhds F ≤ N ↔ ∀ M ∈ F.val, M ≤ N :=
  Finset.sup'_le_iff F.property.1 id

private theorem unionNhds_mono : Monotone unionNhds := by
  intro F G hFG
  exact Finset.sup'_mono id hFG F.property.1

private instance familyDirected : IsDirectedOrder Family where
  directed F G := by
    classical
    have hrange :
        (↑(F.val ∪ G.val) : Set (OpenNhds (X := TopCat.of X) point)) ⊆ Set.range W := by
      intro N hN
      rcases Finset.mem_union.mp hN with hN | hN
      · exact F.property.2 hN
      · exact G.property.2 hN
    exact ⟨⟨F.val ∪ G.val,
      F.property.1.mono Finset.subset_union_left, hrange⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩

private def singletonFamily (i : Index) : Family :=
  ⟨{W i}, Finset.singleton_nonempty _, by
    intro N hN
    rcases Finset.mem_singleton.mp hN with rfl
    exact Set.mem_range_self i⟩

private theorem mem_singletonFamily (i : Index)
    (N : OpenNhds (X := TopCat.of X) point) :
    N ∈ (singletonFamily i).val ↔ N = W i :=
  Finset.mem_singleton

private theorem unionNhds_singleton (i : Index) :
    unionNhds (singletonFamily i) = W i :=
  Finset.sup'_singleton id

private theorem unionNhds_cover : IsOpenCover (fun F => (unionNhds F).1) := by
  apply IsOpenCover.mk
  apply top_unique
  intro q _
  obtain ⟨i, hi⟩ := cover.exists_mem q
  apply Opens.mem_iSup.mpr
  refine ⟨singletonFamily i, ?_⟩
  rw [unionNhds_singleton]
  exact hi

private def pairIndex : Index :=
  (⟨{0, 1}, by simp⟩, false)

private abbrev U₀ : OpenNhds (X := TopCat.of X) point :=
  W (singletonIndex 0 false)

private abbrev V₀ : OpenNhds (X := TopCat.of X) point := W pairIndex

private theorem inr_mem_U₀ (n : ℕ) : Sum.inr n ∈ U₀.val ↔ n = 0 :=
  Finset.mem_singleton

private theorem inr_mem_V₀ (n : ℕ) : Sum.inr n ∈ V₀.val ↔ n = 0 ∨ n = 1 := by
  change n ∈ ({0, 1} : Finset ℕ) ↔ n = 0 ∨ n = 1
  simp only [Finset.mem_insert, Finset.mem_singleton]

private theorem U₀_lt_V₀ : U₀ < V₀ := by
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · intro q hq
    cases q with
    | inl _ => exact True.intro
    | inr n => exact (inr_mem_V₀ n).mpr (Or.inl ((inr_mem_U₀ n).mp hq))
  · intro hVU
    have hone : Sum.inr 1 ∈ V₀.val := (inr_mem_V₀ 1).mpr (Or.inr rfl)
    exact Nat.one_ne_zero ((inr_mem_U₀ 1).mp (hVU hone))

private def J₀ : Family := singletonFamily pairIndex

private def K₀ : Family := by
  classical
  refine ⟨{U₀, V₀}, Finset.insert_nonempty _ _, ?_⟩
  intro N hN
  rcases Finset.mem_insert.mp hN with hN | hN
  · subst N
    exact Set.mem_range_self (singletonIndex 0 false)
  · rcases Finset.mem_singleton.mp hN with rfl
    exact Set.mem_range_self pairIndex

private theorem mem_J₀ (N : OpenNhds (X := TopCat.of X) point) :
    N ∈ J₀.val ↔ N = V₀ :=
  mem_singletonFamily pairIndex N

private theorem mem_K₀ (N : OpenNhds (X := TopCat.of X) point) :
    N ∈ K₀.val ↔ N = U₀ ∨ N = V₀ := by
  classical
  simp only [K₀, Finset.mem_insert, Finset.mem_singleton]

/-- The larger finite family has no reverse inclusion arrow, even though both
intersection-closed families have exactly the same proper union. -/
private theorem nested_families_boundary :
    U₀ < V₀ ∧ U₀ ≠ ⊤ ∧ V₀ ≠ ⊤ ∧ J₀ < K₀ ∧ ¬ K₀ ≤ J₀ ∧
      InfClosed (↑J₀.val : Set (OpenNhds (X := TopCat.of X) point)) ∧
      InfClosed (↑K₀.val : Set (OpenNhds (X := TopCat.of X) point)) ∧
      unionNhds J₀ = V₀ ∧ unionNhds K₀ = V₀ ∧ unionNhds K₀ ≤ unionNhds J₀ := by
  have hUV : U₀ ≤ V₀ := U₀_lt_V₀.le
  have hJK : J₀ ≤ K₀ := by
    intro N hN
    exact (mem_K₀ N).mpr (Or.inr ((mem_J₀ N).mp hN))
  have hnot : ¬ K₀ ≤ J₀ := by
    intro hKJ
    exact U₀_lt_V₀.ne ((mem_J₀ U₀).mp (hKJ ((mem_K₀ U₀).mpr (Or.inl rfl))))
  have hJinf : InfClosed (↑J₀.val : Set (OpenNhds (X := TopCat.of X) point)) := by
    intro N hN M hM
    apply (mem_J₀ _).mpr
    rw [(mem_J₀ N).mp hN, (mem_J₀ M).mp hM, inf_idem]
  have hKinf : InfClosed (↑K₀.val : Set (OpenNhds (X := TopCat.of X) point)) := by
    intro N hN M hM
    rcases (mem_K₀ N).mp hN with rfl | rfl
    · rcases (mem_K₀ M).mp hM with rfl | rfl
      · exact (mem_K₀ _).mpr (Or.inl (inf_idem U₀))
      · exact (mem_K₀ _).mpr (Or.inl (inf_eq_left.mpr hUV))
    · rcases (mem_K₀ M).mp hM with rfl | rfl
      · exact (mem_K₀ _).mpr (Or.inl (inf_eq_right.mpr hUV))
      · exact (mem_K₀ _).mpr (Or.inr (inf_idem V₀))
  have hJ : unionNhds J₀ = V₀ := unionNhds_singleton pairIndex
  have hK : unionNhds K₀ = V₀ := by
    apply le_antisymm
    · apply (unionNhds_le_iff K₀ V₀).mpr
      intro N hN
      rcases (mem_K₀ N).mp hN with rfl | rfl
      · exact hUV
      · exact le_rfl
    · exact Finset.le_sup' id ((mem_K₀ V₀).mpr (Or.inr rfl))
  refine ⟨U₀_lt_V₀, ?_, ?_, lt_iff_le_not_ge.mpr ⟨hJK, hnot⟩,
    hnot, hJinf, hKinf, hJ, hK, hK.le.trans hJ.ge⟩
  · intro h
    exact proper (singletonIndex 0 false) (congrArg Subtype.val h)
  · intro h
    exact proper pairIndex (congrArg Subtype.val h)

/-- Finite neighborhood families give a directed monotone open cover. Their common
union chart `V₀` carries a nonidentity circle class detected by a circle retraction,
and its ambient image remains nonidentity. -/
private theorem finiteFamily_cover_nontrivial :
    IsDirectedOrder Family ∧ Monotone unionNhds ∧
      IsOpenCover (fun F => (unionNhds F).1) ∧
      circleClassX ≠ 1 ∧ circleClass pairIndex ≠ 1 ∧
      FundamentalGroup.map (j pairIndex) (localPoint pairIndex) (circleClass pairIndex) =
        circleClassX ∧
      (FundamentalGroup.map (r pairIndex) (localPoint pairIndex)).comp
          (FundamentalGroup.map (s pairIndex) (0 : A)) =
        MonoidHom.id (FundamentalGroup A 0) ∧
      ¬ InfClosed (Set.range W) :=
  ⟨inferInstance, unionNhds_mono, unionNhds_cover, circleClasses_ne_one.1,
    circleClasses_ne_one.2 pairIndex, circleClass_global pairIndex,
    group_retraction pairIndex, not_infClosed⟩

open CategoryTheory CategoryTheory.Limits

private def familyCircleCocone :
    Cocone (unionNhds_mono.functor ⋙ FundamentalGroup.openNhdsFunctor point) :=
  ((FundamentalGroup.openNhdsCocone point).whisker unionNhds_mono.functor).extend
    (GrpCat.ofHom (FundamentalGroup.map rX point))

/-- Descent along the finite-family inclusion cocone recovers the original circle
class under the circle projection, so its image is nonidentity. -/
example :
    let ψ := (FundamentalGroup.isColimitOfIsOpenCoverOfMonotone point unionNhds
      unionNhds_cover unionNhds_mono).desc familyCircleCocone
    ψ.hom circleClassX = CircleTransport.loopClass ∧ ψ.hom circleClassX ≠ 1 := by
  let hc := FundamentalGroup.isColimitOfIsOpenCoverOfMonotone point unionNhds
    unionNhds_cover unionNhds_mono
  have hdesc : hc.desc familyCircleCocone =
      GrpCat.ofHom (FundamentalGroup.map rX point) :=
    (hc.uniq familyCircleCocone _ (fun _ => rfl)).symm
  have hclass : (hc.desc familyCircleCocone).hom circleClassX =
      CircleTransport.loopClass := by
    rw [hdesc]
    exact projection_circleClassX
  exact ⟨hclass, fun h => CircleTransport.loopClass_ne_one (hclass.symm.trans h)⟩

end CircleFiniteSubsetCover
