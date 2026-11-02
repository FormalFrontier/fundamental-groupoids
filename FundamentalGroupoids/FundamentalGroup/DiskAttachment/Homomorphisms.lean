/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup.DiskAttachment.OpenCover
public import FundamentalGroupoids.FundamentalGroup.DiskAttachment.PuncturedChart
public import FundamentalGroupoids.FundamentalGroup.DiskAttachment.PuncturedComponent

/-!
# Homomorphisms killing the attaching loops

Restriction along the inclusion into a disk attachment identifies homomorphisms
from its fundamental group with homomorphisms from the original fundamental
group that kill all positive attaching loop classes. The inverse extends along
the same inclusion. The space, disk family and target group have independent
universes; the family may be empty or infinite.

The proof transports a homomorphism to the punctured component, extends it over
each thickened disk chart, and applies the common-overlap van Kampen theorem.
The relative radial deformation compares the entire core inclusion map with
the original-space inclusion, not just the attaching loop classes.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–7,
  for the van Kampen theorem and the effect of attaching disks.
-/

@[expose] public section

noncomputable section

universe u v w

namespace FundamentalGroup

open TopCat TopCat.DiskAttachment

variable {X : Type u} [TopologicalSpace X] {J : Type v}

private theorem diskAttachment_hom_existsUnique
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x)
    (H : Type w) [Group H] (a : FundamentalGroup X x →* H)
    (ha : ∀ j, a (mapOfEq (f j) (h j)
      (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1)))) = 1) :
    ∃! φ : FundamentalGroup (diskAttachment f) (diskAttachmentInclusion f x) →* H,
      φ.comp (map (diskAttachmentInclusion f) x) = a := by
  let c0 := diskAttachmentPuncturedComponentBasepoint f x
  let e := diskAttachmentPuncturedComponentMulEquiv f x
  let q := map (diskAttachmentInclusion f) x
  have h0 : coreMap f x c0 = diskAttachmentInclusion f x := by
    simp only [c0, coreMap_apply, diskAttachmentPuncturedComponentBasepoint_coe,
      diskAttachmentPuncturedInclusion_coe]
  let m0 := mapOfEq (coreMap f x) h0
  have hJ : ∀ j, (ContinuousMap.subtypeVal (chartSet f x j))
      (chartCore f x j c0) = diskAttachmentInclusion f x := by
    intro j
    exact (ContinuousMap.subtypeVal_apply (chartSet f x j) (chartCore f x j c0)).trans
      ((chartCore_coe f x j c0).trans h0)
  let mJ := fun j => mapOfEq (x := chartCore f x j c0)
    (ContinuousMap.subtypeVal (chartSet f x j)) (hJ j)
  let k := fun j => map (chartCore f x j) c0
  have he : q.comp e.toMonoidHom = m0 := by
    have hwhole :
        (ContinuousMap.subtypeVal ((diskAttachmentCenters f)ᶜ)).comp
            (ContinuousMap.subtypeVal (diskAttachmentPuncturedComponentSet f x)) =
          coreMap f x := by
      apply ContinuousMap.ext
      intro c
      simp only [ContinuousMap.comp_apply, ContinuousMap.subtypeVal_apply, coreMap_apply]
    have hpoint :
        ((ContinuousMap.subtypeVal ((diskAttachmentCenters f)ᶜ)).comp
          (ContinuousMap.subtypeVal (diskAttachmentPuncturedComponentSet f x))) c0 =
          diskAttachmentInclusion f x :=
      (congrArg (fun g : C(diskAttachmentPuncturedComponent f x, diskAttachment f) =>
        g c0) hwhole).trans h0
    exact (map_diskAttachmentInclusion_comp_puncturedComponentMulEquiv f x).trans
      (mapOfEq_congr hwhole hpoint h0)
  have hm : ∀ j, (mJ j).comp (k j) = m0 := by
    intro j
    have hwhole : (ContinuousMap.subtypeVal (chartSet f x j)).comp
        (chartCore f x j) = coreMap f x := by
      apply ContinuousMap.ext
      intro c
      exact (ContinuousMap.comp_apply (ContinuousMap.subtypeVal (chartSet f x j))
        (chartCore f x j) c).trans
          ((ContinuousMap.subtypeVal_apply (chartSet f x j) (chartCore f x j c)).trans
            (chartCore_coe f x j c))
    have hpoint : ((ContinuousMap.subtypeVal (chartSet f x j)).comp
        (chartCore f x j)) c0 = diskAttachmentInclusion f x :=
      (ContinuousMap.comp_apply (ContinuousMap.subtypeVal (chartSet f x j))
        (chartCore f x j) c0).trans (hJ j)
    have hcomp := mapOfEq_comp (ContinuousMap.subtypeVal (chartSet f x j))
      (chartCore f x j) (rfl : chartCore f x j c0 = chartCore f x j c0) (hJ j)
    exact (congrArg (fun l => (mJ j).comp l)
      (mapOfEq_rfl (chartCore f x j) c0).symm).trans
        (hcomp.symm.trans (mapOfEq_congr hwhole hpoint h0))
  let a0 := a.comp e.toMonoidHom
  have ha0 : ∀ j, a0 (diskAttachmentPuncturedComponentGenerator f x j (h j)) = 1 := by
    intro j
    change a (e (diskAttachmentPuncturedComponentGenerator f x j (h j))) = 1
    rw [diskAttachmentPuncturedComponentMulEquiv_generator]
    exact ha j
  let aJ := fun j => (diskAttachmentPuncturedChartHomEquiv f x j (h j) H).symm
    ⟨a0, ha0 j⟩
  have haJ : ∀ j, (aJ j).comp (k j) = a0 := by
    intro j
    exact diskAttachmentPuncturedChartHomEquiv_symm_comp f x j (h j) H ⟨a0, ha0 j⟩
  obtain ⟨φ, hφ, huniq⟩ :=
    existsUnique_hom_of_diskAttachmentChartFamily f x h H a0 aJ haJ
  change φ.comp m0 = a0 ∧ ∀ j, φ.comp (mJ j) = aJ j at hφ
  refine ⟨φ, ?_, ?_⟩
  · apply MonoidHom.ext
    intro z
    obtain ⟨c, rfl⟩ := e.surjective z
    have hc := DFunLike.congr_fun he c
    change q (e c) = m0 c at hc
    change φ (q (e c)) = a (e c)
    rw [hc]
    exact DFunLike.congr_fun hφ.1 c
  · intro g hg
    have hgc : g.comp m0 = a0 := by
      calc
        g.comp m0 = (g.comp q).comp e.toMonoidHom := by
          rw [← he, MonoidHom.comp_assoc]
        _ = a0 := by rw [hg]
    have hgj : ∀ j, g.comp (mJ j) = aJ j := by
      intro j
      apply (diskAttachmentPuncturedChartHomEquiv f x j (h j) H).injective
      apply Subtype.ext
      simp only [diskAttachmentPuncturedChartHomEquiv_apply_val]
      change (g.comp (mJ j)).comp (k j) = (aJ j).comp (k j)
      rw [MonoidHom.comp_assoc, hm j, hgc, haJ j]
    exact huniq g ⟨hgc, hgj⟩

private theorem diskAttachment_restriction_bijective
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x)
    (H : Type w) [Group H] :
    Function.Bijective
      (fun φ : FundamentalGroup (diskAttachment f) (diskAttachmentInclusion f x) →* H =>
        (⟨φ.comp (map (diskAttachmentInclusion f) x), by
          intro j
          change φ (map (diskAttachmentInclusion f) x
            (mapOfEq (f j) (h j)
              (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1))))) = 1
          rw [map_diskAttachmentInclusion_mapOfEq_eq_one, map_one]⟩ :
        {a : FundamentalGroup X x →* H //
          ∀ j, a (mapOfEq (f j) (h j)
            (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1)))) = 1})) := by
  constructor
  · intro φ ψ hφψ
    have hq := congrArg Subtype.val hφψ
    have hψ : ∀ j, (ψ.comp (map (diskAttachmentInclusion f) x))
        (mapOfEq (f j) (h j)
          (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1)))) = 1 := by
      intro j
      change ψ (map (diskAttachmentInclusion f) x
        (mapOfEq (f j) (h j)
          (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1))))) = 1
      rw [map_diskAttachmentInclusion_mapOfEq_eq_one, map_one]
    obtain ⟨χ, _, huniq⟩ := diskAttachment_hom_existsUnique f x h H
      (ψ.comp (map (diskAttachmentInclusion f) x)) hψ
    exact (huniq φ hq).trans (huniq ψ rfl).symm
  · intro a
    obtain ⟨φ, hφ, _⟩ := diskAttachment_hom_existsUnique f x h H a.val a.property
    exact ⟨φ, Subtype.ext hφ⟩

/-- Homomorphisms from the fundamental group of a disk attachment correspond to
homomorphisms from the original fundamental group killing every positive attaching
loop class. Restriction and extension both use the original-space inclusion into
the attachment. No connectedness assumption on the original space, or finiteness
or nonemptiness assumption on the disk family, is required.

This is the disk-attachment form of the van Kampen theorem; see May,
*A Concise Course in Algebraic Topology*, Chapter 2, §§6–7. -/
noncomputable def diskAttachmentFundamentalGroupHomEquiv
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x)
    (H : Type w) [Group H] :
    (FundamentalGroup (diskAttachment f) (diskAttachmentInclusion f x) →* H) ≃
      {a : FundamentalGroup X x →* H //
        ∀ j, a (mapOfEq (f j) (h j)
          (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1)))) = 1} :=
  Equiv.ofBijective
    (fun φ => ⟨φ.comp (map (diskAttachmentInclusion f) x), by
      intro j
      change φ (map (diskAttachmentInclusion f) x
        (mapOfEq (f j) (h j)
          (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1))))) = 1
      rw [map_diskAttachmentInclusion_mapOfEq_eq_one, map_one]⟩)
    (by exact diskAttachment_restriction_bijective f x h H)

/-- The forward equivalence restricts along the inclusion of the original space. -/
@[simp]
theorem diskAttachmentFundamentalGroupHomEquiv_apply_val
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x)
    (H : Type w) [Group H]
    (φ : FundamentalGroup (diskAttachment f) (diskAttachmentInclusion f x) →* H) :
    (diskAttachmentFundamentalGroupHomEquiv f x h H φ).val =
      φ.comp (map (diskAttachmentInclusion f) x) := by
  rfl

/-- The inverse equivalence extends along the same original-space inclusion. -/
@[simp]
theorem diskAttachmentFundamentalGroupHomEquiv_symm_comp
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x)
    (H : Type w) [Group H]
    (a : {a : FundamentalGroup X x →* H //
      ∀ j, a (mapOfEq (f j) (h j)
        (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1)))) = 1}) :
    ((diskAttachmentFundamentalGroupHomEquiv f x h H).symm a).comp
      (map (diskAttachmentInclusion f) x) = a.val := by
  have h := congrArg Subtype.val
    ((diskAttachmentFundamentalGroupHomEquiv f x h H).apply_symm_apply a)
  rw [diskAttachmentFundamentalGroupHomEquiv_apply_val] at h
  exact h

end FundamentalGroup
