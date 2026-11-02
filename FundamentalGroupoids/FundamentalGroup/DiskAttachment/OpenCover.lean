/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover
public import FundamentalGroupoids.FundamentalGroup.HomotopyEquiv
public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.OpenCover

/-!
# Homomorphisms from the fundamental group of a disk attachment

Compatible homomorphisms on the punctured component and all its thickened disk
charts extend uniquely to the fundamental group of the attachment. The
restrictions are induced by the inclusions into the attachment itself, not
merely by the inclusions into its chosen path component.

The proof uses the common-overlap open-cover theorem on the attachment
component. The range homeomorphisms identify its core and chart legs, including
the whole core-to-chart maps. No finiteness or nonemptiness of the family is
required, and the target group has an independent universe.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §7,
  for the open-cover form of the van Kampen theorem.
-/

@[expose] public section

noncomputable section

universe u v w

namespace FundamentalGroup

open CategoryTheory TopCat TopCat.DiskAttachment

variable {X : Type u} [TopologicalSpace X] {J : Type v}

/-- Compatible homomorphisms on the punctured component and every thickened disk
chart extend uniquely to the fundamental group of the disk attachment. Both
restriction laws use the inclusions into the entire attachment. This is the
common-overlap van Kampen theorem applied to its component cover. -/
theorem existsUnique_hom_of_diskAttachmentChartFamily
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x)
    (H : Type w) [Group H]
    (a0 : FundamentalGroup (diskAttachmentPuncturedComponent f x)
      (diskAttachmentPuncturedComponentBasepoint f x) →* H)
    (a : ∀ j, FundamentalGroup (PuncturedChart f x j)
      (chartCore f x j (diskAttachmentPuncturedComponentBasepoint f x)) →* H)
    (ha : ∀ j, (a j).comp
      (map (chartCore f x j) (diskAttachmentPuncturedComponentBasepoint f x)) = a0) :
    ∃! φ : FundamentalGroup (diskAttachment f) (diskAttachmentInclusion f x) →* H,
      φ.comp (mapOfEq (coreMap f x) (show
        coreMap f x (diskAttachmentPuncturedComponentBasepoint f x) =
          diskAttachmentInclusion f x from by
        simp only [coreMap_apply, diskAttachmentPuncturedComponentBasepoint_coe,
          diskAttachmentPuncturedInclusion_coe])) = a0 ∧
      ∀ j, φ.comp (mapOfEq
        (x := chartCore f x j (diskAttachmentPuncturedComponentBasepoint f x))
        (ContinuousMap.subtypeVal (chartSet f x j)) (show
        (ContinuousMap.subtypeVal (chartSet f x j))
            (chartCore f x j (diskAttachmentPuncturedComponentBasepoint f x)) =
          diskAttachmentInclusion f x from by
        simp only [ContinuousMap.subtypeVal_apply]
        exact (chartCore_coe f x j _).trans (by
          simp only [coreMap_apply, diskAttachmentPuncturedComponentBasepoint_coe,
            diskAttachmentPuncturedInclusion_coe]))) = a j := by
  let c0 := diskAttachmentPuncturedComponentBasepoint f x
  let y := diskAttachmentInclusion f x
  let Y := ↥(pathComponent y)
  let p : Y := componentBasepoint f x
  let C := componentOpenNhds f x h none
  let U := fun j => componentOpenNhds f x h (some j)
  let hCU : ∀ j, C ≤ U j := componentOpenNhds_none_le f x h
  -- Transport only the range subtype, keeping its canonical subspace topology.
  let L : diskAttachmentPuncturedComponent f x ≃ₜ C.1 :=
    (componentCoreHomeomorph f x h).trans
      (Homeomorph.setCongr (congrArg
        (fun W : TopologicalSpace.Opens Y => (W : Set Y))
        (componentOpenNhds_val f x h none).symm))
  let Lj : ∀ j, PuncturedChart f x j ≃ₜ (U j).1 := fun j =>
    (componentChartHomeomorph f x h j).trans
      (Homeomorph.setCongr (congrArg
        (fun W : TopologicalSpace.Opens Y => (W : Set Y))
        (componentOpenNhds_val f x h (some j)).symm))
  let l0 : C(diskAttachmentPuncturedComponent f x, C.1) :=
    (L : C(diskAttachmentPuncturedComponent f x, C.1))
  let lJ : ∀ j, C(PuncturedChart f x j, (U j).1) := fun j =>
    (Lj j : C(PuncturedChart f x j, (U j).1))
  have hLcoe (c : diskAttachmentPuncturedComponent f x) :
      (L c : Y) = componentCoreMap f x c := by
    change (componentCoreHomeomorph f x h c : Y) = _
    exact componentCoreHomeomorph_coe f x h c
  have hLjcoe (j : J) (c : PuncturedChart f x j) :
      (Lj j c : Y) = chartComponentMap f x j (h j) c := by
    change (componentChartHomeomorph f x h j c : Y) = _
    exact componentChartHomeomorph_coe f x h j c
  have hc0 : c0 = diskAttachmentPuncturedComponentInclusion f x
      ⟨x, mem_pathComponent_self x⟩ := by
    apply Subtype.ext
    simp only [c0, diskAttachmentPuncturedComponentBasepoint_coe,
      diskAttachmentPuncturedComponentInclusion_coe]
  have hL : L c0 = (⟨p, C.2⟩ : C.1) := by
    apply Subtype.ext
    change (L c0 : Y) = p
    rw [hLcoe, hc0]
    exact componentCoreMap_basepoint f x
  have hLj : ∀ j, Lj j (chartCore f x j c0) = (⟨p, (U j).2⟩ : (U j).1) := by
    intro j
    apply Subtype.ext
    change (Lj j (chartCore f x j c0) : Y) = p
    rw [hLjcoe, chartComponentMap_chartCore, hc0]
    exact componentCoreMap_basepoint f x
  have hl0 : l0 c0 = (⟨p, C.2⟩ : C.1) :=
    (ContinuousMap.coe_apply L c0).trans hL
  have hlJ : ∀ j, lJ j (chartCore f x j c0) = (⟨p, (U j).2⟩ : (U j).1) :=
    fun j => (ContinuousMap.coe_apply (Lj j) (chartCore f x j c0)).trans (hLj j)
  have hLMap : L.toHomotopyEquiv.toFun = l0 := by
    apply ContinuousMap.ext
    intro c
    exact (congrFun (Homeomorph.coe_toHomotopyEquiv L) c).trans
      (ContinuousMap.coe_apply L c).symm
  have hLjMap : ∀ j, (Lj j).toHomotopyEquiv.toFun = lJ j := by
    intro j
    apply ContinuousMap.ext
    intro c
    exact (congrFun (Homeomorph.coe_toHomotopyEquiv (Lj j)) c).trans
      (ContinuousMap.coe_apply (Lj j) c).symm
  have hLHomotopyPoint : L.toHomotopyEquiv.toFun c0 = (⟨p, C.2⟩ : C.1) :=
    (congrFun (Homeomorph.coe_toHomotopyEquiv L) c0).trans hL
  have hLjHomotopyPoint : ∀ j, (Lj j).toHomotopyEquiv.toFun
      (chartCore f x j c0) = (⟨p, (U j).2⟩ : (U j).1) := fun j =>
    (congrFun (Homeomorph.coe_toHomotopyEquiv (Lj j))
      (chartCore f x j c0)).trans (hLj j)
  -- Use each equivalence's own forward functor and its fully faithful dictionary.
  let e0 : FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 ≃*
      FundamentalGroup C.1 ⟨p, C.2⟩ :=
    (CategoryTheory.Functor.FullyFaithful.mulEquivEnd
      (C := FundamentalGroupoid (diskAttachmentPuncturedComponent f x))
      (D := FundamentalGroupoid C.1)
      (f := (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
        L.toHomotopyEquiv).functor)
      (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
        L.toHomotopyEquiv).fullyFaithfulFunctor
      (FundamentalGroupoid.mk c0)).trans
        (CategoryTheory.Iso.conj (C := FundamentalGroupoid C.1)
          (eqToIso (congrArg FundamentalGroupoid.mk hLHomotopyPoint)))
  let eJ : ∀ j, FundamentalGroup (PuncturedChart f x j) (chartCore f x j c0) ≃*
      FundamentalGroup (U j).1 ⟨p, (U j).2⟩ := fun j =>
    (CategoryTheory.Functor.FullyFaithful.mulEquivEnd
      (C := FundamentalGroupoid (PuncturedChart f x j))
      (D := FundamentalGroupoid (U j).1)
      (f := (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
        (Lj j).toHomotopyEquiv).functor)
      (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
        (Lj j).toHomotopyEquiv).fullyFaithfulFunctor
      (FundamentalGroupoid.mk (chartCore f x j c0))).trans
        (CategoryTheory.Iso.conj (C := FundamentalGroupoid (U j).1)
          (eqToIso (congrArg FundamentalGroupoid.mk (hLjHomotopyPoint j))))
  have he0 : e0.toMonoidHom = mapOfEq l0 hl0 := by
    dsimp only [e0]
    exact (homotopyEquiv_mulEquivEnd_trans_conj_toMonoidHom
      L.toHomotopyEquiv c0 ⟨p, C.2⟩ hLHomotopyPoint).trans
        (mapOfEq_congr hLMap hLHomotopyPoint hl0)
  have heJ : ∀ j, (eJ j).toMonoidHom = mapOfEq (lJ j) (hlJ j) := by
    intro j
    dsimp only [eJ]
    exact (homotopyEquiv_mulEquivEnd_trans_conj_toMonoidHom
      (Lj j).toHomotopyEquiv (chartCore f x j c0) ⟨p, (U j).2⟩
      (hLjHomotopyPoint j)).trans
        (mapOfEq_congr (hLjMap j) (hLjHomotopyPoint j) (hlJ j))
  let δ0 := ((openNhdsCocone p).ι.app C).hom
  let δJ := fun j => ((openNhdsCocone p).ι.app (U j)).hom
  let m := fun j => ((openNhdsFunctor p).map (homOfLE (hCU j))).hom
  have hdiag : ∀ j, (m j).comp e0.toMonoidHom =
      (eJ j).toMonoidHom.comp (map (chartCore f x j) c0) := by
    intro j
    let i := ContinuousMap.inclusion (hCU j)
    have hi : i (⟨p, C.2⟩ : C.1) = (⟨p, (U j).2⟩ : (U j).1) := by rfl
    have hsquare : (lJ j).comp (chartCore f x j) = i.comp l0 := by
      apply ContinuousMap.ext
      intro c
      apply Subtype.ext
      simpa only [ContinuousMap.comp_apply, lJ, l0, ContinuousMap.coe_coe,
        i, ContinuousMap.inclusion, ContinuousMap.coe_mk, Set.coe_inclusion] using
        ((hLjcoe j (chartCore f x j c)).trans
          (chartComponentMap_chartCore f x j (h j) c)).trans (hLcoe c).symm
    have hleft : (i.comp l0) c0 = (⟨p, (U j).2⟩ : (U j).1) :=
      (congrArg i hl0).trans hi
    have hright : ((lJ j).comp (chartCore f x j)) c0 =
        (⟨p, (U j).2⟩ : (U j).1) := hlJ j
    have hm : m j = mapOfEq i hi :=
      (openNhdsFunctor_map_hom p (homOfLE (hCU j))).trans
        (mapOfEq_rfl i (⟨p, C.2⟩ : C.1)).symm
    have hrightComp : mapOfEq ((lJ j).comp (chartCore f x j)) hright =
        (mapOfEq (lJ j) (hlJ j)).comp (map (chartCore f x j) c0) :=
      (mapOfEq_comp (lJ j) (chartCore f x j)
        (rfl : chartCore f x j c0 = chartCore f x j c0) (hlJ j)).trans
          (congrArg ((mapOfEq (lJ j) (hlJ j)).comp)
            (mapOfEq_rfl (chartCore f x j) c0))
    have hcomp : (mapOfEq i hi).comp (mapOfEq l0 hl0) =
        (mapOfEq (lJ j) (hlJ j)).comp (map (chartCore f x j) c0) :=
      (mapOfEq_comp i l0 hl0 hi).symm.trans
        ((mapOfEq_congr hsquare.symm hleft hright).trans hrightComp)
    exact (congrArg₂ MonoidHom.comp hm he0).trans
      (hcomp.trans (congrArg₂ MonoidHom.comp (heJ j).symm rfl))
  let V : C(Y, diskAttachment f) := ContinuousMap.subtypeVal (pathComponent y)
  have hV : V p = y := componentBasepoint_coe f x
  let E : FundamentalGroup Y p ≃* FundamentalGroup (diskAttachment f) y :=
    pathComponentInclusionMulEquiv y p
  have hE : E.toMonoidHom = mapOfEq V hV :=
    (pathComponentInclusionMulEquiv_toMonoidHom y p).trans
      (mapOfEq_rfl V p).symm
  have hq0 : coreMap f x c0 = y := by
    simp only [c0, y, coreMap_apply, diskAttachmentPuncturedComponentBasepoint_coe,
      diskAttachmentPuncturedInclusion_coe]
  have hqJ : ∀ j, (ContinuousMap.subtypeVal (chartSet f x j))
      (chartCore f x j c0) = y := by
    intro j
    simp only [ContinuousMap.subtypeVal_apply]
    exact (chartCore_coe f x j c0).trans hq0
  let q0 : FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 →*
      FundamentalGroup (diskAttachment f) y := mapOfEq (coreMap f x) hq0
  let qJ : ∀ j, FundamentalGroup (PuncturedChart f x j) (chartCore f x j c0) →*
      FundamentalGroup (diskAttachment f) y := fun j =>
    mapOfEq (x := chartCore f x j c0)
      (ContinuousMap.subtypeVal (chartSet f x j)) (hqJ j)
  -- Both subtype-value levels agree with the inclusions into the entire attachment.
  have hleg0 : E.toMonoidHom.comp (δ0.comp e0.toMonoidHom) = q0 := by
    let i := ContinuousMap.subtypeVal (C.1 : Set Y)
    have hi : i (⟨p, C.2⟩ : C.1) = p := by rfl
    have hpoint : (i.comp l0) c0 = p := (congrArg i hl0).trans hi
    have hwholePoint : (V.comp (i.comp l0)) c0 = y :=
      (congrArg V hpoint).trans hV
    have hwhole : V.comp (i.comp l0) = coreMap f x := by
      apply ContinuousMap.ext
      intro c
      have hinner : (i.comp l0) c = (L c : Y) :=
        (ContinuousMap.comp_apply i l0 c).trans
          ((ContinuousMap.subtypeVal_apply (C.1 : Set Y) (l0 c)).trans
            (congrArg (fun z : C.1 => (z : Y)) (ContinuousMap.coe_apply L c)))
      exact (ContinuousMap.comp_apply V (i.comp l0) c).trans
        ((congrArg V hinner).trans
          ((ContinuousMap.subtypeVal_apply (pathComponent y) (L c : Y)).trans
            ((congrArg (fun z : Y => (z : diskAttachment f)) (hLcoe c)).trans
              (componentCoreMap_coe f x c))))
    have hδ : δ0 = mapOfEq i hi :=
      (openNhdsCocone_ι_app_hom p C).trans
        (mapOfEq_rfl i (⟨p, C.2⟩ : C.1)).symm
    have hcomp : (mapOfEq i hi).comp (mapOfEq l0 hl0) =
        mapOfEq (i.comp l0) hpoint := (mapOfEq_comp i l0 hl0 hi).symm
    have hmap : (mapOfEq V hV).comp (mapOfEq (i.comp l0) hpoint) = q0 :=
      (mapOfEq_comp V (i.comp l0) hpoint hV).symm.trans
        (mapOfEq_congr hwhole hwholePoint hq0)
    exact (congrArg₂ MonoidHom.comp hE (congrArg₂ MonoidHom.comp hδ he0)).trans
      ((congrArg ((mapOfEq V hV).comp) hcomp).trans hmap)
  have hlegJ : ∀ j, E.toMonoidHom.comp ((δJ j).comp (eJ j).toMonoidHom) = qJ j := by
    intro j
    let i := ContinuousMap.subtypeVal ((U j).1 : Set Y)
    have hi : i (⟨p, (U j).2⟩ : (U j).1) = p := by rfl
    have hpoint : (i.comp (lJ j)) (chartCore f x j c0) = p :=
      (congrArg i (hlJ j)).trans hi
    have hwholePoint : (V.comp (i.comp (lJ j))) (chartCore f x j c0) = y :=
      (congrArg V hpoint).trans hV
    have hwhole : V.comp (i.comp (lJ j)) =
        ContinuousMap.subtypeVal (chartSet f x j) := by
      apply ContinuousMap.ext
      intro c
      have hinner : (i.comp (lJ j)) c = (Lj j c : Y) :=
        (ContinuousMap.comp_apply i (lJ j) c).trans
          ((ContinuousMap.subtypeVal_apply ((U j).1 : Set Y) (lJ j c)).trans
            (congrArg (fun z : (U j).1 => (z : Y))
              (ContinuousMap.coe_apply (Lj j) c)))
      exact (ContinuousMap.comp_apply V (i.comp (lJ j)) c).trans
        ((congrArg V hinner).trans
          ((ContinuousMap.subtypeVal_apply (pathComponent y) (Lj j c : Y)).trans
            (((congrArg (fun z : Y => (z : diskAttachment f)) (hLjcoe j c)).trans
              (chartComponentMap_coe f x j (h j) c)).trans
                (ContinuousMap.subtypeVal_apply (chartSet f x j) c).symm)))
    have hδ : δJ j = mapOfEq i hi :=
      (openNhdsCocone_ι_app_hom p (U j)).trans
        (mapOfEq_rfl i (⟨p, (U j).2⟩ : (U j).1)).symm
    have hcomp : (mapOfEq i hi).comp (mapOfEq (lJ j) (hlJ j)) =
        mapOfEq (i.comp (lJ j)) hpoint := (mapOfEq_comp i (lJ j) (hlJ j) hi).symm
    have hmap : (mapOfEq V hV).comp (mapOfEq (i.comp (lJ j)) hpoint) = qJ j :=
      (mapOfEq_comp V (i.comp (lJ j)) hpoint hV).symm.trans
        (mapOfEq_congr hwhole hwholePoint (hqJ j))
    exact (congrArg₂ MonoidHom.comp hE
      (congrArg₂ MonoidHom.comp hδ (heJ j))).trans
        ((congrArg ((mapOfEq V hV).comp) hcomp).trans hmap)
  let b0 := a0.comp e0.symm.toMonoidHom
  let bJ := fun j => (a j).comp (eJ j).symm.toMonoidHom
  have hb : ∀ j, (bJ j).comp (m j) = b0 := by
    intro j
    apply MonoidHom.ext
    intro γ
    obtain ⟨z, rfl⟩ := e0.surjective γ
    have hz := DFunLike.congr_fun (hdiag j) z
    change m j (e0 z) = eJ j (map (chartCore f x j) c0 z) at hz
    change a j ((eJ j).symm (m j (e0 z))) = a0 (e0.symm (e0 z))
    rw [hz, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact DFunLike.congr_fun (ha j) z
  obtain ⟨ψ, hψ, huniq⟩ := existsUnique_hom_of_isOpenCover_of_commonOverlap
    p C U hCU (componentOpenNhds_inf_of_ne f x h)
    (isOpenCover_componentOpenNhds f x h)
    (isPathConnected_componentOpenNhds f x h none)
    (fun j => isPathConnected_componentOpenNhds f x h (some j)) H b0 bJ hb
  change ∃! φ : FundamentalGroup (diskAttachment f) y →* H,
    φ.comp q0 = a0 ∧ ∀ j, φ.comp (qJ j) = a j
  refine ⟨ψ.comp E.symm.toMonoidHom, ?_, ?_⟩
  · constructor
    · apply MonoidHom.ext
      intro z
      have hz : E (δ0 (e0 z)) = q0 z := DFunLike.congr_fun hleg0 z
      have hp : ψ (δ0 (e0 z)) = a0 (e0.symm (e0 z)) :=
        DFunLike.congr_fun hψ.1 (e0 z)
      exact (congrArg (fun t : FundamentalGroup (diskAttachment f) y => ψ (E.symm t))
        hz.symm).trans
          ((congrArg (fun t : FundamentalGroup Y p => ψ t)
            (E.symm_apply_apply (δ0 (e0 z)))).trans
              (hp.trans (congrArg a0 (e0.symm_apply_apply z))))
    · intro j
      apply MonoidHom.ext
      intro z
      have hz : E (δJ j (eJ j z)) = qJ j z := DFunLike.congr_fun (hlegJ j) z
      have hp : ψ (δJ j (eJ j z)) = a j ((eJ j).symm (eJ j z)) :=
        DFunLike.congr_fun (hψ.2 j) (eJ j z)
      exact (congrArg (fun t : FundamentalGroup (diskAttachment f) y => ψ (E.symm t))
        hz.symm).trans
          ((congrArg (fun t : FundamentalGroup Y p => ψ t)
            (E.symm_apply_apply (δJ j (eJ j z)))).trans
              (hp.trans (congrArg (a j) ((eJ j).symm_apply_apply z))))
  · intro g hg
    have hge : g.comp E.toMonoidHom = ψ := by
      apply huniq
      constructor
      · apply MonoidHom.ext
        intro γ
        obtain ⟨z, rfl⟩ := e0.surjective γ
        change g (E (δ0 (e0 z))) = a0 (e0.symm (e0 z))
        rw [MulEquiv.symm_apply_apply]
        have hz := DFunLike.congr_fun hleg0 z
        change E (δ0 (e0 z)) = q0 z at hz
        rw [hz]
        exact DFunLike.congr_fun hg.1 z
      · intro j
        apply MonoidHom.ext
        intro γ
        obtain ⟨z, rfl⟩ := (eJ j).surjective γ
        change g (E (δJ j (eJ j z))) = a j ((eJ j).symm (eJ j z))
        rw [MulEquiv.symm_apply_apply]
        have hz := DFunLike.congr_fun (hlegJ j) z
        change E (δJ j (eJ j z)) = qJ j z at hz
        rw [hz]
        exact DFunLike.congr_fun (hg.2 j) z
    apply MonoidHom.ext
    intro γ
    obtain ⟨z, rfl⟩ := E.surjective γ
    change g (E z) = ψ (E.symm (E z))
    rw [MulEquiv.symm_apply_apply]
    exact DFunLike.congr_fun hge z

end FundamentalGroup
