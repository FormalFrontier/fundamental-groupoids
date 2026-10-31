/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.FundamentalGroup
import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.DirectedOpenCover
import all FundamentalGroupoidsTest.FundamentalGroup
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SupClosed
import Mathlib.Topology.Category.TopCat.OpenNhds
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Sets.OpenCover

/-!
# A directed cover with disconnected charts and nontrivial fundamental groups

The space `AddCircle 1 ⊕ ℕ`, based at zero on the circle, is covered by the circle
with a nonempty finite set of right-hand points attached. The indices retain a
Boolean coordinate, giving distinct indices for equal opens. Finite unions give
inclusion-directedness, but the range is not closed under binary intersections:
the charts for the singletons `{0}` and `{1}` intersect in just the circle.

Every chart is disconnected and proper, and no finite subfamily covers the space.
The circle section and the sum retraction show that the existing nonidentity
circle class remains nonidentity in every chart and in the ambient space. These
classes are compatible with all chart inclusions and the ambient subtype maps.
These facts are proved without an open-cover fundamental-group theorem. As a separate
application, the directed-cover colimit descent to the circle sends the ambient
circle class back to the original nonidentity circle class.

## References

* `FundamentalGroupoidsTest.FundamentalGroup` supplies the nonidentity circle class,
  constructed using Mathlib's quotient covering of the circle.
* Mathlib supplies sum topology, clopen separation, finite unions, open
  neighborhoods, and the induced fundamental-group homomorphisms.
-/

noncomputable section

open TopologicalSpace

namespace CircleFiniteSubsetCover

private abbrev A := AddCircle (1 : ℝ)
private abbrev X := A ⊕ ℕ
private abbrev point : X := Sum.inl 0
private abbrev Index := {F : Finset ℕ // F.Nonempty} × Bool

private def U (i : Index) : Opens X :=
  ⟨{q | Sum.elim (fun _ : A => True) (fun n => n ∈ i.1.1) q},
    isOpen_sum_iff.mpr ⟨isOpen_univ, isOpen_discrete _⟩⟩

private theorem commonPoint (i : Index) : point ∈ U i := True.intro

private def W (i : Index) : OpenNhds (X := TopCat.of X) point :=
  ⟨U i, commonPoint i⟩

private def localPoint (i : Index) : U i := ⟨point, commonPoint i⟩

private def singletonIndex (n : ℕ) (b : Bool) : Index :=
  (⟨{n}, Finset.singleton_nonempty n⟩, b)

private theorem cover : IsOpenCover (fun i => (W i).1) := by
  apply IsOpenCover.mk
  apply top_unique
  intro q _
  apply Opens.mem_iSup.mpr
  cases q with
  | inl _ => exact ⟨singletonIndex 0 false, True.intro⟩
  | inr n => exact ⟨singletonIndex n false, Finset.mem_singleton_self n⟩

private theorem directed : Directed (· ≤ ·) W := by
  intro i j
  obtain ⟨n, hn⟩ := i.1.2
  let k : Index :=
    (⟨i.1.1 ∪ j.1.1, ⟨n, Finset.mem_union.mpr (Or.inl hn)⟩⟩, false)
  refine ⟨k, ?_, ?_⟩
  · change U i ≤ U k
    intro q hq
    cases q with
    | inl _ => exact True.intro
    | inr _ => exact Finset.mem_union.mpr (Or.inl hq)
  · change U j ≤ U k
    intro q hq
    cases q with
    | inl _ => exact True.intro
    | inr _ => exact Finset.mem_union.mpr (Or.inr hq)

private theorem repeated_indices : ∃ i j : Index, i ≠ j ∧ W i = W j := by
  refine ⟨singletonIndex 0 false, singletonIndex 0 true, ?_, rfl⟩
  intro h
  have hb : false = true := congrArg Prod.snd h
  cases hb

private theorem not_preconnected_of_sides {S : Set X} (hl : point ∈ S)
    (hr : ∃ n : ℕ, Sum.inr n ∈ S) : ¬ IsPreconnected S := by
  intro hS
  have hleft : S ⊆ Set.range (Sum.inl : A → X) :=
    hS.subset_isClopen isClopen_range_inl ⟨point, hl, 0, rfl⟩
  obtain ⟨n, hn⟩ := hr
  obtain ⟨z, hz⟩ := hleft hn
  cases hz

private theorem disconnected (i : Index) : ¬ IsPreconnected (U i : Set X) := by
  obtain ⟨n, hn⟩ := i.1.2
  exact not_preconnected_of_sides (commonPoint i) ⟨n, hn⟩

private theorem ambient_disconnected : ¬ IsPreconnected (Set.univ : Set X) :=
  not_preconnected_of_sides (Set.mem_univ point) ⟨0, Set.mem_univ _⟩

private theorem proper (i : Index) : U i ≠ ⊤ := by
  obtain ⟨n, hn⟩ := i.1.1.exists_notMem
  intro h
  apply hn
  have hmem : Sum.inr n ∈ U i := by
    rw [h]
    trivial
  exact hmem

private theorem no_finite_subcover (s : Finset Index) :
    ∃ x : X, ∀ i ∈ s, x ∉ U i := by
  classical
  obtain ⟨n, hn⟩ := (s.biUnion (fun i => i.1.1)).exists_notMem
  refine ⟨Sum.inr n, ?_⟩
  intro i hi hmem
  exact hn (Finset.mem_biUnion.mpr ⟨i, hi, hmem⟩)

private theorem not_infClosed : ¬ InfClosed (Set.range W) := by
  intro h
  obtain ⟨k, hk⟩ := h (Set.mem_range_self (singletonIndex 0 false))
    (Set.mem_range_self (singletonIndex 1 false))
  obtain ⟨n, hn⟩ := k.1.2
  have hmem : Sum.inr n ∈
      (W (singletonIndex 0 false) ⊓ W (singletonIndex 1 false)).1 := by
    rw [← hk]
    exact hn
  have hzero : n = 0 := Finset.mem_singleton.mp hmem.1
  have hone : n = 1 := Finset.mem_singleton.mp hmem.2
  exact Nat.zero_ne_one (hzero.symm.trans hone)

private def j (i : Index) : C(U i, X) := ContinuousMap.subtypeVal (U i : Set X)

private def inclusion {i j : Index} (h : U i ≤ U j) : C(U i, U j) :=
  ContinuousMap.inclusion h

private def sX : C(A, X) := ⟨Sum.inl, continuous_inl⟩

private def rX : C(X, A) :=
  ⟨Sum.elim id (fun _ : ℕ => 0), continuous_id.sumElim continuous_const⟩

private def s (i : Index) : C(A, U i) where
  toFun z := ⟨Sum.inl z, True.intro⟩
  continuous_toFun :=
    (continuous_inl : Continuous (Sum.inl : A → X)).subtype_mk (fun _ => True.intro)

private def r (i : Index) : C(U i, A) := rX.comp (j i)

private theorem group_retraction_X :
    (FundamentalGroup.map rX point).comp (FundamentalGroup.map sX (0 : A)) =
      MonoidHom.id (FundamentalGroup A 0) :=
  (FundamentalGroup.map_comp rX sX (0 : A)).symm.trans (FundamentalGroup.map_id (0 : A))

private theorem group_retraction (i : Index) :
    (FundamentalGroup.map (r i) (localPoint i)).comp
        (FundamentalGroup.map (s i) (0 : A)) =
      MonoidHom.id (FundamentalGroup A 0) :=
  (FundamentalGroup.map_comp (r i) (s i) (0 : A)).symm.trans
    (FundamentalGroup.map_id (0 : A))

private def circleClassX : FundamentalGroup X point :=
  FundamentalGroup.map sX (0 : A) CircleTransport.loopClass

private def circleClass (i : Index) : FundamentalGroup (U i) (localPoint i) :=
  FundamentalGroup.map (s i) (0 : A) CircleTransport.loopClass

private theorem projection_circleClassX :
    FundamentalGroup.map rX point circleClassX = CircleTransport.loopClass :=
  DFunLike.congr_fun group_retraction_X CircleTransport.loopClass

private theorem projection_circleClass (i : Index) :
    FundamentalGroup.map (r i) (localPoint i) (circleClass i) = CircleTransport.loopClass :=
  DFunLike.congr_fun (group_retraction i) CircleTransport.loopClass

private theorem circleClass_inclusion {i j : Index} (h : U i ≤ U j) :
    FundamentalGroup.map (inclusion h) (localPoint i) (circleClass i) = circleClass j :=
  DFunLike.congr_fun (FundamentalGroup.map_comp (inclusion h) (s i) (0 : A)).symm
    CircleTransport.loopClass

private theorem circleClass_global (i : Index) :
    FundamentalGroup.map (j i) (localPoint i) (circleClass i) = circleClassX :=
  DFunLike.congr_fun (FundamentalGroup.map_comp (j i) (s i) (0 : A)).symm
    CircleTransport.loopClass

private theorem circleClasses_ne_one : circleClassX ≠ 1 ∧ ∀ i, circleClass i ≠ 1 := by
  constructor
  · intro h
    have hr := projection_circleClassX
    rw [h, map_one] at hr
    exact CircleTransport.loopClass_ne_one hr.symm
  · intro i h
    have hr := projection_circleClass i
    rw [h, map_one] at hr
    exact CircleTransport.loopClass_ne_one hr.symm

/-- An inclusion-directed open cover with repeated indices, no preconnected charts,
no finite subcover, and a range that is not intersection-closed. Its nonidentity
circle classes survive all chart inclusions and the ambient subtype maps. -/
example :
    IsOpenCover (fun i => (W i).1) ∧ Directed (· ≤ ·) W ∧
      (∃ i j : Index, i ≠ j ∧ W i = W j) ∧
      (∀ i, ¬ IsPreconnected (U i : Set X)) ∧
      ¬ IsPreconnected (Set.univ : Set X) ∧
      (∀ i, U i ≠ ⊤) ∧
      (∀ t : Finset Index, ∃ x : X, ∀ i ∈ t, x ∉ U i) ∧
      ¬ InfClosed (Set.range W) ∧ circleClassX ≠ 1 ∧
      (∀ i, circleClass i ≠ 1 ∧
        FundamentalGroup.map (j i) (localPoint i) (circleClass i) = circleClassX) ∧
      (∀ (i j : Index) (h : U i ≤ U j),
        FundamentalGroup.map (inclusion h) (localPoint i) (circleClass i) = circleClass j) :=
  ⟨cover, directed, repeated_indices, disconnected, ambient_disconnected, proper,
    no_finite_subcover, not_infClosed, circleClasses_ne_one.1,
    fun i => ⟨circleClasses_ne_one.2 i, circleClass_global i⟩,
    fun _ _ h => circleClass_inclusion h⟩

open CategoryTheory CategoryTheory.Limits

private def circleCocone :
    Cocone (inducedFunctor W ⋙ FundamentalGroup.openNhdsFunctor point) where
  pt := GrpCat.of (FundamentalGroup A 0)
  ι :=
    { app := fun i => GrpCat.ofHom (FundamentalGroup.map (r i) (localPoint i))
      naturality := by
        intro i k f
        apply GrpCat.hom_ext
        exact (FundamentalGroup.map_comp (r k) (inclusion f.hom.le) (localPoint i)).symm }

/-- Colimit descent along the circle retractions detects the surviving circle class. -/
example :
    ((FundamentalGroup.isColimitOfIsOpenCoverOfDirected point W cover directed).desc
      circleCocone).hom circleClassX = CircleTransport.loopClass := by
  let i := singletonIndex 0 false
  have h := ConcreteCategory.congr_hom
    ((FundamentalGroup.isColimitOfIsOpenCoverOfDirected point W cover directed).fac
      circleCocone i) (circleClass i)
  change ((FundamentalGroup.isColimitOfIsOpenCoverOfDirected point W cover directed).desc
      circleCocone).hom (FundamentalGroup.map (j i) (localPoint i) (circleClass i)) =
    FundamentalGroup.map (r i) (localPoint i) (circleClass i) at h
  simpa only [circleClass_global, projection_circleClass] using h

end CircleFiniteSubsetCover
