/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup
public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.PuncturedComponent

/-!
# Fundamental group of a punctured attachment component

The radial retraction identifies the fundamental group of the punctured part of
an attachment component with that of the original space. The forward map is the
restricted retraction followed by inclusion of the original-space path component.
The inverse is induced by the component inclusion, after the inverse of the
path-component inclusion isomorphism.

The relative deformation and the strict retraction identity give inverse induced
homomorphisms on the fundamental groups of the two components. Composing with the
path-component inclusion isomorphism gives the comparison with the original space.
No basedness assumption on the attaching maps, or openness assumption on path components, is
needed. The two spaces and the disk-index type retain their natural universes.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 1, §4, for
  homotopy invariance of fundamental groups. The relative form is
  `FundamentalGroup.mapOfEq_eq_of_homotopicRel`.
-/

@[expose] public section

universe u v

namespace FundamentalGroup

open TopCat

variable {X : Type u} [TopologicalSpace X] {J : Type v}

/-- Retraction from the punctured part of an attachment component induces an
isomorphism with the fundamental group of the original space. Its inverse first
lifts to the original-space path component and then applies the component
inclusion. No attaching map is required to preserve the basepoint. -/
noncomputable def diskAttachmentPuncturedComponentMulEquiv
    (f : J → C(Circle, X)) (x : X) :
    FundamentalGroup (diskAttachmentPuncturedComponent f x)
        (diskAttachmentPuncturedComponentBasepoint f x) ≃*
      FundamentalGroup X x := by
  let c : ↥(pathComponent x) := ⟨x, mem_pathComponent_self x⟩
  let c0 : diskAttachmentPuncturedComponent f x :=
    diskAttachmentPuncturedComponentBasepoint f x
  let i : C(↥(pathComponent x), diskAttachmentPuncturedComponent f x) :=
    diskAttachmentPuncturedComponentInclusion f x
  let r : C(diskAttachmentPuncturedComponent f x, ↥(pathComponent x)) :=
    diskAttachmentPuncturedComponentRetraction f x
  have hi : i c = c0 := by
    apply Subtype.ext
    exact (diskAttachmentPuncturedComponentInclusion_coe f x c).trans
      (diskAttachmentPuncturedComponentBasepoint_coe f x).symm
  have hr : r c0 = c := diskAttachmentPuncturedComponentRetraction_basepoint f x
  let F : FundamentalGroup (↥(pathComponent x)) c →*
      FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 := map i c
  let G : FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 →*
      FundamentalGroup (↥(pathComponent x)) c := mapOfEq r hr
  let E : FundamentalGroup (↥(pathComponent x)) c ≃* FundamentalGroup X x :=
    pathComponentInclusionMulEquiv x c
  let K : FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 →*
      FundamentalGroup X x :=
    mapOfEq ((ContinuousMap.subtypeVal (pathComponent x)).comp r)
      (diskAttachmentPuncturedComponentRetraction_basepoint_coe f x)
  have hri : r.comp i = ContinuousMap.id ↥(pathComponent x) :=
    diskAttachmentPuncturedComponentRetraction_comp_inclusion f x
  have hri_rel : (r.comp i).HomotopicRel (ContinuousMap.id _) Set.univ := by
    simpa only [hri] using
      (ContinuousMap.HomotopicRel.refl (S := Set.univ)
        (ContinuousMap.id ↥(pathComponent x)))
  have hF : mapOfEq i hi = F := mapOfEq_rfl i c
  have hGF : G.comp F = MonoidHom.id (FundamentalGroup (↥(pathComponent x)) c) := by
    have hcomp :
        (mapOfEq (r.comp i) ((congrArg r hi).trans hr) :
          FundamentalGroup (↥(pathComponent x)) c →*
            FundamentalGroup (↥(pathComponent x)) c) = G.comp F := by
      exact (mapOfEq_comp r i (x := c) (y := c0) (z := c) hi hr).trans
        (congrArg (fun k : FundamentalGroup (↥(pathComponent x)) c →*
          FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 => G.comp k) hF)
    have hrel :
        (mapOfEq (r.comp i) ((congrArg r hi).trans hr) :
          FundamentalGroup (↥(pathComponent x)) c →*
            FundamentalGroup (↥(pathComponent x)) c) =
          mapOfEq (ContinuousMap.id ↥(pathComponent x))
            (rfl : ContinuousMap.id ↥(pathComponent x) c = c) := by
      exact mapOfEq_eq_of_homotopicRel hri_rel (Set.mem_univ c)
        ((congrArg r hi).trans hr) rfl
    have hid :
        (mapOfEq (ContinuousMap.id ↥(pathComponent x))
          (rfl : ContinuousMap.id ↥(pathComponent x) c = c) :
          FundamentalGroup (↥(pathComponent x)) c →*
            FundamentalGroup (↥(pathComponent x)) c) =
          MonoidHom.id (FundamentalGroup (↥(pathComponent x)) c) := by
      exact mapOfEq_id c
    exact hcomp.symm.trans (hrel.trans hid)
  have hFG : F.comp G =
      MonoidHom.id (FundamentalGroup (diskAttachmentPuncturedComponent f x) c0) := by
    have hcomp :
        (mapOfEq (i.comp r) ((congrArg i hr).trans hi) :
          FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 →*
            FundamentalGroup (diskAttachmentPuncturedComponent f x) c0) = F.comp G := by
      exact (mapOfEq_comp i r (x := c0) (y := c) (z := c0) hr hi).trans
        (congrArg (fun k : FundamentalGroup (↥(pathComponent x)) c →*
          FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 => k.comp G) hF)
    have hrel :
        (mapOfEq (ContinuousMap.id (diskAttachmentPuncturedComponent f x))
          (rfl : ContinuousMap.id (diskAttachmentPuncturedComponent f x) c0 = c0) :
          FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 →*
            FundamentalGroup (diskAttachmentPuncturedComponent f x) c0) =
          mapOfEq (i.comp r) ((congrArg i hr).trans hi) := by
      exact mapOfEq_eq_of_homotopicRel
        ⟨diskAttachmentPuncturedComponentDeformation f x⟩
        ⟨c, hi⟩ rfl ((congrArg i hr).trans hi)
    have hid :
        (mapOfEq (ContinuousMap.id (diskAttachmentPuncturedComponent f x))
          (rfl : ContinuousMap.id (diskAttachmentPuncturedComponent f x) c0 = c0) :
          FundamentalGroup (diskAttachmentPuncturedComponent f x) c0 →*
            FundamentalGroup (diskAttachmentPuncturedComponent f x) c0) =
          MonoidHom.id (FundamentalGroup (diskAttachmentPuncturedComponent f x) c0) := by
      exact mapOfEq_id c0
    exact hcomp.symm.trans (hrel.symm.trans hid)
  have hK : K = E.toMonoidHom.comp G := by
    have hcomp : K =
        (mapOfEq (ContinuousMap.subtypeVal (pathComponent x))
          (rfl : ContinuousMap.subtypeVal (pathComponent x) c = x)).comp G := by
      dsimp only [K, G, c]
      exact mapOfEq_comp (ContinuousMap.subtypeVal (pathComponent x)) r
        (x := c0) (y := c) (z := x) hr rfl
    have hsub :
        (mapOfEq (ContinuousMap.subtypeVal (pathComponent x))
          (rfl : ContinuousMap.subtypeVal (pathComponent x) c = x) :
          FundamentalGroup (↥(pathComponent x)) c →* FundamentalGroup X x) =
          map (ContinuousMap.subtypeVal (pathComponent x)) c := by
      dsimp only [c]
      exact mapOfEq_rfl (ContinuousMap.subtypeVal (pathComponent x))
        ⟨x, mem_pathComponent_self x⟩
    have hE :
        (map (ContinuousMap.subtypeVal (pathComponent x)) c :
          FundamentalGroup (↥(pathComponent x)) c →* FundamentalGroup X x) =
          E.toMonoidHom := by
      dsimp only [E, c]
      exact (pathComponentInclusionMulEquiv_toMonoidHom x
        ⟨x, mem_pathComponent_self x⟩).symm
    exact hcomp.trans
      (congrArg (fun k : FundamentalGroup (↥(pathComponent x)) c →*
        FundamentalGroup X x => k.comp G) (hsub.trans hE))
  exact
    { toFun := K
      invFun := fun a => F (E.symm a)
      left_inv := fun a => by
        change F (E.symm (K a)) = a
        rw [hK]
        change F (E.symm (E (G a))) = a
        rw [E.symm_apply_apply]
        exact DFunLike.congr_fun hFG a
      right_inv := fun a => by
        change K (F (E.symm a)) = a
        rw [hK]
        change E (G (F (E.symm a))) = a
        have h : G (F (E.symm a)) = E.symm a := DFunLike.congr_fun hGF _
        rw [h, E.apply_symm_apply]
      map_mul' := K.map_mul }

/-- The forward homomorphism is exactly the based map of the restricted radial
retraction followed by inclusion into the original space. -/
@[simp]
theorem diskAttachmentPuncturedComponentMulEquiv_toMonoidHom
    (f : J → C(Circle, X)) (x : X) :
    (diskAttachmentPuncturedComponentMulEquiv f x :
      FundamentalGroup (diskAttachmentPuncturedComponent f x)
          (diskAttachmentPuncturedComponentBasepoint f x) →* FundamentalGroup X x) =
      mapOfEq
        ((ContinuousMap.subtypeVal (pathComponent x)).comp
          (diskAttachmentPuncturedComponentRetraction f x))
        (diskAttachmentPuncturedComponentRetraction_basepoint_coe f x) := by
  rfl

/-- Evaluation of the retraction isomorphism is the induced based map. -/
theorem diskAttachmentPuncturedComponentMulEquiv_apply
    (f : J → C(Circle, X)) (x : X)
    (a : FundamentalGroup (diskAttachmentPuncturedComponent f x)
      (diskAttachmentPuncturedComponentBasepoint f x)) :
    diskAttachmentPuncturedComponentMulEquiv f x a =
      mapOfEq
        ((ContinuousMap.subtypeVal (pathComponent x)).comp
          (diskAttachmentPuncturedComponentRetraction f x))
        (diskAttachmentPuncturedComponentRetraction_basepoint_coe f x) a := by
  rfl

/-- On loop classes the retraction isomorphism maps the loop and casts its
endpoints using the proved basepoint equation. -/
theorem diskAttachmentPuncturedComponentMulEquiv_apply_fromPath
    (f : J → C(Circle, X)) (x : X)
    (p : Path (diskAttachmentPuncturedComponentBasepoint f x)
      (diskAttachmentPuncturedComponentBasepoint f x)) :
    diskAttachmentPuncturedComponentMulEquiv f x (fromPath ⟦p⟧) =
      fromPath ⟦(p.map
        (((ContinuousMap.subtypeVal (pathComponent x)).comp
          (diskAttachmentPuncturedComponentRetraction f x)).continuous)).cast
        (diskAttachmentPuncturedComponentRetraction_basepoint_coe f x).symm
        (diskAttachmentPuncturedComponentRetraction_basepoint_coe f x).symm⟧ := by
  rw [diskAttachmentPuncturedComponentMulEquiv_apply]
  exact mapOfEq_fromPath _ _ p

/-- Inclusion into the attachment after the retraction isomorphism equals direct
inclusion of the punctured component, on the whole fundamental group. The radial
deformation is relative to the included original-space component, which contains
the chosen basepoint, so its basepoint track is constant. -/
theorem map_diskAttachmentInclusion_comp_puncturedComponentMulEquiv
    (f : J → C(Circle, X)) (x : X) :
    (map (diskAttachmentInclusion f) x).comp
        (diskAttachmentPuncturedComponentMulEquiv f x).toMonoidHom =
      mapOfEq
        ((ContinuousMap.subtypeVal ((diskAttachmentCenters f)ᶜ)).comp
          (ContinuousMap.subtypeVal (diskAttachmentPuncturedComponentSet f x)))
        (by
          exact (congrArg Subtype.val
            (diskAttachmentPuncturedComponentBasepoint_coe f x)).trans
              (diskAttachmentPuncturedInclusion_coe f x)) := by
  let k : C(diskAttachmentPuncturedComponent f x, diskAttachment f) :=
    (ContinuousMap.subtypeVal ((diskAttachmentCenters f)ᶜ)).comp
      (ContinuousMap.subtypeVal (diskAttachmentPuncturedComponentSet f x))
  let r : C(diskAttachmentPuncturedComponent f x, X) :=
    (ContinuousMap.subtypeVal (pathComponent x)).comp
      (diskAttachmentPuncturedComponentRetraction f x)
  have hk : k (diskAttachmentPuncturedComponentBasepoint f x) =
      diskAttachmentInclusion f x :=
    (congrArg Subtype.val (diskAttachmentPuncturedComponentBasepoint_coe f x)).trans
      (diskAttachmentPuncturedInclusion_coe f x)
  have hr : r (diskAttachmentPuncturedComponentBasepoint f x) = x :=
    diskAttachmentPuncturedComponentRetraction_basepoint_coe f x
  have H : k.HomotopicRel ((diskAttachmentInclusion f).comp r)
      (Set.range (diskAttachmentPuncturedComponentInclusion f x)) := by
    refine ⟨((diskAttachmentPuncturedComponentDeformation f x).compContinuousMap k).cast
      (ContinuousMap.comp_id k) ?_⟩
    apply ContinuousMap.ext
    intro w
    exact (congrArg Subtype.val (diskAttachmentPuncturedComponentInclusion_coe f x
      (diskAttachmentPuncturedComponentRetraction f x w))).trans
        (diskAttachmentPuncturedInclusion_coe f _)
  have hc : diskAttachmentPuncturedComponentBasepoint f x ∈
      Set.range (diskAttachmentPuncturedComponentInclusion f x) := by
    refine ⟨⟨x, Joined.refl x⟩, ?_⟩
    apply Subtype.ext
    exact (diskAttachmentPuncturedComponentInclusion_coe f x _).trans
      (diskAttachmentPuncturedComponentBasepoint_coe f x).symm
  have hmap : mapOfEq k hk =
      mapOfEq ((diskAttachmentInclusion f).comp r)
        (congrArg (diskAttachmentInclusion f) hr) :=
    mapOfEq_eq_of_homotopicRel H hc hk (congrArg (diskAttachmentInclusion f) hr)
  rw [MulEquiv.toMonoidHom_eq_coe,
    diskAttachmentPuncturedComponentMulEquiv_toMonoidHom]
  calc
    (map (diskAttachmentInclusion f) x).comp (mapOfEq r hr) =
        mapOfEq ((diskAttachmentInclusion f).comp r)
          (congrArg (diskAttachmentInclusion f) hr) := by
      simpa only [mapOfEq_rfl] using
        (mapOfEq_comp (diskAttachmentInclusion f) r hr
          (rfl : diskAttachmentInclusion f x = diskAttachmentInclusion f x)).symm
    _ = mapOfEq k hk := hmap.symm

/-- The inverse homomorphism is induced by inclusion of the original-space
component, composed with the inverse path-component inclusion isomorphism. -/
theorem diskAttachmentPuncturedComponentMulEquiv_symm_toMonoidHom
    (f : J → C(Circle, X)) (x : X) :
    ((diskAttachmentPuncturedComponentMulEquiv f x).symm : FundamentalGroup X x →*
      FundamentalGroup (diskAttachmentPuncturedComponent f x)
        (diskAttachmentPuncturedComponentBasepoint f x)) =
      (map (diskAttachmentPuncturedComponentInclusion f x)
        (⟨x, Joined.refl x⟩ : ↥(pathComponent x))).comp
        ((pathComponentInclusionMulEquiv x ⟨x, Joined.refl x⟩).symm :
          FundamentalGroup X x →*
            FundamentalGroup (↥(pathComponent x)) ⟨x, Joined.refl x⟩) := by
  apply MonoidHom.ext
  intro a
  rfl

/-- Evaluation of the inverse lifts a class to the original-space component and
then includes it into the punctured attachment component. -/
theorem diskAttachmentPuncturedComponentMulEquiv_symm_apply
    (f : J → C(Circle, X)) (x : X) (a : FundamentalGroup X x) :
    (diskAttachmentPuncturedComponentMulEquiv f x).symm a =
      map (diskAttachmentPuncturedComponentInclusion f x)
        (⟨x, Joined.refl x⟩ : ↥(pathComponent x))
        ((pathComponentInclusionMulEquiv x ⟨x, Joined.refl x⟩).symm a) := by
  rfl

/-- The based map of the restricted radial retraction into the original space
is bijective. -/
theorem mapOfEq_diskAttachmentPuncturedComponentRetraction_bijective
    (f : J → C(Circle, X)) (x : X) :
    Function.Bijective
      (mapOfEq
        ((ContinuousMap.subtypeVal (pathComponent x)).comp
          (diskAttachmentPuncturedComponentRetraction f x))
        (diskAttachmentPuncturedComponentRetraction_basepoint_coe f x)) := by
  rw [← diskAttachmentPuncturedComponentMulEquiv_toMonoidHom]
  exact (diskAttachmentPuncturedComponentMulEquiv f x).bijective

/-- Retraction after the inverse isomorphism is the identity homomorphism. -/
@[simp]
theorem mapOfEq_diskAttachmentPuncturedComponentRetraction_comp_symm
    (f : J → C(Circle, X)) (x : X) :
    (mapOfEq
      ((ContinuousMap.subtypeVal (pathComponent x)).comp
        (diskAttachmentPuncturedComponentRetraction f x))
      (diskAttachmentPuncturedComponentRetraction_basepoint_coe f x)).comp
      ((diskAttachmentPuncturedComponentMulEquiv f x).symm : FundamentalGroup X x →*
        FundamentalGroup (diskAttachmentPuncturedComponent f x)
          (diskAttachmentPuncturedComponentBasepoint f x)) =
      MonoidHom.id (FundamentalGroup X x) := by
  apply MonoidHom.ext
  intro a
  rw [MonoidHom.comp_apply, MonoidHom.id_apply,
    ← diskAttachmentPuncturedComponentMulEquiv_apply]
  exact (diskAttachmentPuncturedComponentMulEquiv f x).apply_symm_apply a

/-- The inverse isomorphism after retraction is the identity homomorphism. -/
@[simp]
theorem diskAttachmentPuncturedComponentMulEquiv_symm_comp_mapOfEq
    (f : J → C(Circle, X)) (x : X) :
    ((diskAttachmentPuncturedComponentMulEquiv f x).symm : FundamentalGroup X x →*
      FundamentalGroup (diskAttachmentPuncturedComponent f x)
        (diskAttachmentPuncturedComponentBasepoint f x)).comp
      (mapOfEq
        ((ContinuousMap.subtypeVal (pathComponent x)).comp
          (diskAttachmentPuncturedComponentRetraction f x))
        (diskAttachmentPuncturedComponentRetraction_basepoint_coe f x)) =
      MonoidHom.id (FundamentalGroup (diskAttachmentPuncturedComponent f x)
        (diskAttachmentPuncturedComponentBasepoint f x)) := by
  apply MonoidHom.ext
  intro a
  rw [MonoidHom.comp_apply, MonoidHom.id_apply,
    ← diskAttachmentPuncturedComponentMulEquiv_apply]
  exact (diskAttachmentPuncturedComponentMulEquiv f x).symm_apply_apply a

/-- Under the retraction isomorphism, inclusion of the original-space component
induces its usual inclusion homomorphism into the original space. -/
theorem diskAttachmentPuncturedComponentMulEquiv_comp_map_inclusion
    (f : J → C(Circle, X)) (x : X) :
    (diskAttachmentPuncturedComponentMulEquiv f x :
      FundamentalGroup (diskAttachmentPuncturedComponent f x)
          (diskAttachmentPuncturedComponentBasepoint f x) →* FundamentalGroup X x).comp
      (map (diskAttachmentPuncturedComponentInclusion f x)
        (⟨x, Joined.refl x⟩ : ↥(pathComponent x))) =
      map (ContinuousMap.subtypeVal (pathComponent x)) ⟨x, Joined.refl x⟩ := by
  let c : ↥(pathComponent x) := ⟨x, mem_pathComponent_self x⟩
  let e : FundamentalGroup (diskAttachmentPuncturedComponent f x)
      (diskAttachmentPuncturedComponentBasepoint f x) ≃* FundamentalGroup X x :=
    diskAttachmentPuncturedComponentMulEquiv f x
  let F : FundamentalGroup (↥(pathComponent x)) c →*
      FundamentalGroup (diskAttachmentPuncturedComponent f x)
        (diskAttachmentPuncturedComponentBasepoint f x) :=
    map (diskAttachmentPuncturedComponentInclusion f x) c
  let E : FundamentalGroup (↥(pathComponent x)) c ≃* FundamentalGroup X x :=
    pathComponentInclusionMulEquiv x c
  change e.toMonoidHom.comp F =
    (map (ContinuousMap.subtypeVal (pathComponent x)) c :
      FundamentalGroup (↥(pathComponent x)) c →* FundamentalGroup X x)
  apply MonoidHom.ext
  intro a
  change e (F a) = map (ContinuousMap.subtypeVal (pathComponent x)) c a
  have hsymm : e.symm (E a) = F (E.symm (E a)) := by
    exact DFunLike.congr_fun
      (diskAttachmentPuncturedComponentMulEquiv_symm_toMonoidHom f x) (E a)
  have h : e.symm (E a) = F a :=
    hsymm.trans (congrArg F (E.symm_apply_apply a))
  have hE : E a = map (ContinuousMap.subtypeVal (pathComponent x)) c a := by
    dsimp only [E, c]
    exact pathComponentInclusionMulEquiv_apply x ⟨x, mem_pathComponent_self x⟩ a
  exact (congrArg e h.symm).trans ((e.apply_symm_apply (E a)).trans hE)

end FundamentalGroup
