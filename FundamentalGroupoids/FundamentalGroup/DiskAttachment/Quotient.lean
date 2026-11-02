/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup.DiskAttachment.Homomorphisms
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# The fundamental group of a disk attachment as a quotient

The inclusion of the original space into a disk attachment induces a surjective
fundamental-group homomorphism. Its kernel is the normal closure of the positive
attaching loop classes. The induced quotient isomorphism and its inverse commute
with the original-space inclusion and the quotient projection.

The argument uses the homomorphism equivalence for disk attachments at two target
groups: the quotient of the original fundamental group by the attaching relators,
and the fundamental group of the attachment. No connectedness assumption on the
original space or finiteness or nonemptiness assumption on the disk family is needed.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–7,
  for the van Kampen theorem and the effect of attaching disks.
-/

@[expose] public section

noncomputable section

universe u v

namespace FundamentalGroup

open TopCat

variable {X : Type u} [TopologicalSpace X] {J : Type v}

private theorem diskAttachment_surjective_and_ker
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x) :
    Function.Surjective (map (diskAttachmentInclusion f) x) ∧
      (map (diskAttachmentInclusion f) x).ker =
        Subgroup.normalClosure
          (Set.range fun j => mapOfEq (f j) (h j)
            (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1)))) := by
  let q := map (diskAttachmentInclusion f) x
  let N : Subgroup (FundamentalGroup X x) := Subgroup.normalClosure
    (Set.range fun j => mapOfEq (f j) (h j)
      (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1))))
  have hN : N ≤ q.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j, rfl⟩
    exact MonoidHom.mem_ker.mpr
      (map_diskAttachmentInclusion_mapOfEq_eq_one f x j (h j) _)
  let p := QuotientGroup.mk' N
  have hp : ∀ j, p (mapOfEq (f j) (h j)
    (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1)))) = 1 := by
    intro j
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨j, rfl⟩
  let d := (diskAttachmentFundamentalGroupHomEquiv f x h
    (FundamentalGroup X x ⧸ N)).symm ⟨p, hp⟩
  have hd : d.comp q = p :=
    diskAttachmentFundamentalGroupHomEquiv_symm_comp f x h
      (FundamentalGroup X x ⧸ N) ⟨p, hp⟩
  let l := QuotientGroup.lift N q hN
  have hl : l.comp p = q := QuotientGroup.lift_comp_mk' N q hN
  have hinj : Function.Injective
      (fun φ : FundamentalGroup (diskAttachment f) (diskAttachmentInclusion f x) →*
        FundamentalGroup (diskAttachment f) (diskAttachmentInclusion f x) =>
          φ.comp q) := by
    intro φ ψ hφψ
    apply (diskAttachmentFundamentalGroupHomEquiv f x h
      (FundamentalGroup (diskAttachment f) (diskAttachmentInclusion f x))).injective
    apply Subtype.ext
    simpa only [diskAttachmentFundamentalGroupHomEquiv_apply_val] using hφψ
  have hld : l.comp d = MonoidHom.id _ := by
    apply hinj
    exact Eq.trans (MonoidHom.comp_assoc q d l)
      (Eq.trans
        (congrArg (fun ψ : FundamentalGroup X x →* (FundamentalGroup X x ⧸ N) =>
          l.comp ψ) hd)
        (Eq.trans hl (MonoidHom.id_comp q).symm))
  have hsurj : Function.Surjective q := by
    intro b
    obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N (d b)
    refine ⟨a, ?_⟩
    have he := DFunLike.congr_fun hl a
    change l (p a) = q a at he
    rw [← he, ha]
    exact DFunLike.congr_fun hld b
  have hker : q.ker = N := by
    apply le_antisymm ?_ hN
    intro a ha
    have hpa : p a = 1 := by
      have he := DFunLike.congr_fun hd a
      change d (q a) = p a at he
      rw [← he, MonoidHom.mem_ker.mp ha, map_one]
    exact (QuotientGroup.eq_one_iff a).mp hpa
  exact ⟨hsurj, hker⟩

/-- Attaching disks induces a surjection on the fundamental group at any common
basepoint of the attaching maps; see May, *A Concise Course in Algebraic Topology*,
Chapter 2, §§6–7. -/
theorem surjective_map_diskAttachmentInclusion
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x) :
    Function.Surjective (map (diskAttachmentInclusion f) x) := by
  exact (diskAttachment_surjective_and_ker f x h).1

/-- The kernel of the inclusion-induced fundamental-group homomorphism is the
normal closure of the positive attaching loop classes; see May,
*A Concise Course in Algebraic Topology*, Chapter 2, §§6–7. -/
theorem ker_map_diskAttachmentInclusion
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x) :
    (map (diskAttachmentInclusion f) x).ker =
      Subgroup.normalClosure
        (Set.range fun j => mapOfEq (f j) (h j)
          (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1)))) := by
  exact (diskAttachment_surjective_and_ker f x h).2

/-- The fundamental group after attaching disks is the quotient of the original
fundamental group by the normal closure of the positive attaching loop classes.
The isomorphism is induced by the inclusion of the original space; see May,
*A Concise Course in Algebraic Topology*, Chapter 2, §§6–7. -/
noncomputable def diskAttachmentFundamentalGroupQuotientEquiv
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x) :
    (FundamentalGroup X x ⧸ Subgroup.normalClosure
      (Set.range fun j => mapOfEq (f j) (h j)
        (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1))))) ≃*
      FundamentalGroup (diskAttachment f) (diskAttachmentInclusion f x) :=
  QuotientGroup.liftEquiv _ (surjective_map_diskAttachmentInclusion f x h)
    (ker_map_diskAttachmentInclusion f x h).symm

/-- On quotient representatives, the quotient isomorphism is the homomorphism
induced by the inclusion of the original space. -/
@[simp]
theorem diskAttachmentFundamentalGroupQuotientEquiv_mk
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x)
    (a : FundamentalGroup X x) :
    diskAttachmentFundamentalGroupQuotientEquiv f x h a =
      map (diskAttachmentInclusion f) x a := by
  exact QuotientGroup.liftEquiv_mk _ _ _ a

/-- The quotient isomorphism followed after the quotient projection equals the
homomorphism induced by inclusion of the original space. -/
@[simp]
theorem diskAttachmentFundamentalGroupQuotientEquiv_comp_mk
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x) :
    (diskAttachmentFundamentalGroupQuotientEquiv f x h : _ →* _).comp
      (QuotientGroup.mk' (Subgroup.normalClosure
        (Set.range fun j => mapOfEq (f j) (h j)
          (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1)))))) =
      map (diskAttachmentInclusion f) x := by
  apply MonoidHom.ext
  intro a
  exact diskAttachmentFundamentalGroupQuotientEquiv_mk f x h a

/-- The inverse quotient isomorphism followed after the inclusion-induced
homomorphism equals the quotient projection. -/
@[simp]
theorem diskAttachmentFundamentalGroupQuotientEquiv_symm_comp
    (f : J → C(Circle, X)) (x : X) (h : ∀ j, f j 1 = x) :
    ((diskAttachmentFundamentalGroupQuotientEquiv f x h).symm : _ →* _).comp
      (map (diskAttachmentInclusion f) x) =
        QuotientGroup.mk' (Subgroup.normalClosure
          (Set.range fun j => mapOfEq (f j) (h j)
            (fromPath (Path.Homotopic.Quotient.mk (Circle.loop 1))))) := by
  apply MonoidHom.ext
  intro a
  have hproj := diskAttachmentFundamentalGroupQuotientEquiv_mk f x h a
  exact Eq.trans
    (congrArg (diskAttachmentFundamentalGroupQuotientEquiv f x h).symm hproj).symm
    ((diskAttachmentFundamentalGroupQuotientEquiv f x h).symm_apply_apply _)

end FundamentalGroup
