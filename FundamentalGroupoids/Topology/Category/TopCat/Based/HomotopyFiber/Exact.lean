/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based.HomotopyFiber
import FundamentalGroupoids.Topology.Homotopy.Fiber.Exact

/-!
# Exactness of the homotopy-fiber sequence on based homotopy classes

For any based source `(Z, z₀)`, the projection, loop inclusion,
and loop map in the homotopy-fiber sequence give three range–constant-preimage
identities on the entire hom-sets of `BasedTopCat.HomotopyCategory`. The source
and the two original target spaces may have independent universes. Ordinary
universe lifts put their original models in a common based category; equality
of lifted classes is homotopy of original continuous maps relative to `{z₀}`.

The proofs use relative nullhomotopies on the original source. A nullhomotopy
of the composite with `f` lifts to its homotopy fiber; a nullhomotopy of the
projection produces a family of loops; and a nullhomotopy of
the loop inclusion produces a preimage under the original loop map. These are
the three successive exactness positions in May, Chapter 8, §6, pp. 61–62.

## Limitations

Products, subspaces, and compact-open mapping spaces here have their ordinary
topologies, and based homotopy fixes the selected source point. No local
compactness, separation, closed-basepoint, or fibration assumption is imposed.
We do not identify these arbitrary-source quotient hom-sets with components of
mapping spaces or with May's kified, compactly generated model, and do not
assert a full signed or group-valued long exact sequence.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, §6,
  "Fiber sequences", printed pp. 61–62 (PDF pp. 69–70).
* The relative nullhomotopy constructions in `ContinuousMap.HomotopyFiber`
  and the original-map universe-lift comparison in `BasedTopCat`.
-/

@[expose] public section

open CategoryTheory
open scoped Topology

namespace BasedTopCat

-- Membership in a quotient range can be witnessed by an original based map.
private theorem mem_range_homotopyPostcomp_ofHomULift_iff.{w, uZ, uX, uY}
    {Z : Type uZ} {X : Type uX} {Y : Type uY}
    [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]
    (z₀ : Z) (x₀ : X) (y₀ : Y) (k : C(X, Y)) (hk : k x₀ = y₀)
    (a : C(Z, Y)) (ha : a z₀ = y₀) :
    homotopyQuotient.map (ofHomULift.{max w uZ uX uY} a ha) ∈
        Set.range (homotopyPostcomp (ofULift.{max w uZ uX uY} Z z₀)
          (ofHomULift.{max w uZ uX uY} k hk)) ↔
      ∃ d : C(Z, X), d z₀ = x₀ ∧ (k.comp d).HomotopicRel a {z₀} := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨d, hd, rfl⟩ :=
      exists_homotopyQuotient_map_ofHomULift_eq.{max w uZ uX uY} Z X z₀ x₀ q
    rw [homotopyPostcomp_ofHomULift] at hq
    exact ⟨d, hd,
      (homotopyQuotient_map_ofHomULift_eq_iff.{max w uZ uX uY} _ _ _ _).mp hq⟩
  · rintro ⟨d, hd, H⟩
    refine ⟨homotopyQuotient.map (ofHomULift.{max w uZ uX uY} d hd), ?_⟩
    rw [homotopyPostcomp_ofHomULift]
    exact (homotopyQuotient_map_ofHomULift_eq_iff.{max w uZ uX uY} _ _ _ _).mpr H

-- Membership in the constant preimage is an original relative nullhomotopy.
private theorem mem_preimage_homotopyPostcomp_ofHomULift_const_iff.{w, uZ, uX, uY}
    {Z : Type uZ} {X : Type uX} {Y : Type uY}
    [TopologicalSpace Z] [TopologicalSpace X] [TopologicalSpace Y]
    (z₀ : Z) (x₀ : X) (y₀ : Y) (k : C(X, Y)) (hk : k x₀ = y₀)
    (a : C(Z, X)) (ha : a z₀ = x₀) :
    homotopyQuotient.map (ofHomULift.{max w uZ uX uY} a ha) ∈
        (homotopyPostcomp (ofULift.{max w uZ uX uY} Z z₀)
          (ofHomULift.{max w uZ uX uY} k hk)) ⁻¹'
            {homotopyQuotient.map
              (ofHomULift.{max w uZ uX uY} (ContinuousMap.const Z y₀) rfl)} ↔
      (k.comp a).HomotopicRel (ContinuousMap.const Z y₀) {z₀} := by
  change
    homotopyPostcomp (ofULift.{max w uZ uX uY} Z z₀)
        (ofHomULift.{max w uZ uX uY} k hk)
        (homotopyQuotient.map (ofHomULift.{max w uZ uX uY} a ha)) =
      homotopyQuotient.map
        (ofHomULift.{max w uZ uX uY} (x := z₀) (y := y₀)
          (ContinuousMap.const Z y₀) rfl) ↔
      (k.comp a).HomotopicRel (ContinuousMap.const Z y₀) {z₀}
  rw [homotopyPostcomp_ofHomULift]
  exact homotopyQuotient_map_ofHomULift_eq_iff.{max w uZ uX uY} _ _ _ _

/-- For every based source, the image of the homotopy-fiber projection consists
exactly of classes whose composite with the original map is constant.
This is the projection position of May's fiber-sequence exactness
(Chapter 8, §6, pp. 61–62), on arbitrary-source based quotient hom-sets. -/
theorem range_homotopyFiberProjection.{uZ, uE, uB}
    (Z : Type uZ) (E : Type uE) (B : Type uB)
    [TopologicalSpace Z] [TopologicalSpace E] [TopologicalSpace B]
    (z₀ : Z) (e₀ : E) (b : B) (f : C(E, B)) (h : f e₀ = b) :
    let Z' : BasedTopCat.{max uZ uE uB} := ofULift.{max uZ uE uB} Z z₀
    let E' : BasedTopCat.{max uZ uE uB} := ofULift.{max uZ uE uB} E e₀
    let B' : BasedTopCat.{max uZ uE uB} := ofULift.{max uZ uE uB} B b
    let F' : BasedTopCat.{max uZ uE uB} :=
      ofULift.{max uZ uE uB} (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h)
    let p : F' ⟶ E' := homotopyFiberPoint.{max uZ uE uB} f b e₀ h
    let f' : E' ⟶ B' := ofHomULift.{max uZ uE uB} f h
    let c : homotopyQuotient.obj Z' ⟶ homotopyQuotient.obj B' :=
      homotopyQuotient.map (ofHomULift.{max uZ uE uB} (ContinuousMap.const Z b) rfl)
    Set.range (homotopyPostcomp Z' p) = (homotopyPostcomp Z' f') ⁻¹' {c} := by
  dsimp only
  ext q
  obtain ⟨a, ha, rfl⟩ :=
    exists_homotopyQuotient_map_ofHomULift_eq.{max uZ uE uB} Z E z₀ e₀ q
  refine (mem_range_homotopyPostcomp_ofHomULift_iff.{max uZ uE uB}
    z₀ (ContinuousMap.HomotopyFiber.const e₀ h) e₀
    (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
    (ContinuousMap.HomotopyFiber.point_const e₀ h) a ha).trans ?_
  refine Iff.trans ?_
    (mem_preimage_homotopyPostcomp_ofHomULift_const_iff.{max uZ uE uB}
      z₀ e₀ b f h a ha).symm
  constructor
  · rintro ⟨k, hk, Hk⟩
    have Hnull := ContinuousMap.HomotopicRel.precomp_continuousMap
      (ContinuousMap.HomotopyFiber.homotopicRel_comp_point_const f b e₀ h) k
      (Set.mapsTo_singleton.mpr (Set.mem_singleton_iff.mpr hk))
    exact (Hk.comp_continuousMap f).symm.trans Hnull
  · rintro ⟨H⟩
    obtain ⟨k, hk, hpk, _⟩ :=
      ContinuousMap.HomotopyFiber.exists_lift_of_nullhomotopyRel
        {z₀} f b e₀ h a (Set.forall_mem_singleton.mpr ha) H.symm
    refine ⟨k, hk z₀ (Set.mem_singleton z₀), ?_⟩
    rw [hpk]
    exact ContinuousMap.HomotopicRel.refl a

/-- For every based source, the image of the loop inclusion
consists exactly of classes with constant homotopy-fiber projection.
This is the fiber position of May's fiber-sequence exactness
(Chapter 8, §6, pp. 61–62), on arbitrary-source based quotient hom-sets. -/
theorem range_homotopyFiberLoopInclusion.{uZ, uE, uB}
    (Z : Type uZ) (E : Type uE) (B : Type uB)
    [TopologicalSpace Z] [TopologicalSpace E] [TopologicalSpace B]
    (z₀ : Z) (e₀ : E) (b : B) (f : C(E, B)) (h : f e₀ = b) :
    let Z' : BasedTopCat.{max uZ uE uB} := ofULift.{max uZ uE uB} Z z₀
    let E' : BasedTopCat.{max uZ uE uB} := ofULift.{max uZ uE uB} E e₀
    let F' : BasedTopCat.{max uZ uE uB} :=
      ofULift.{max uZ uE uB} (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h)
    let ΩB : BasedTopCat.{max uZ uE uB} :=
      ofULift.{max uZ uE uB} (Path b b) (Path.refl b)
    let J : ΩB ⟶ F' := homotopyFiberLoopInclusion.{max uZ uE uB} f b e₀ h
    let p : F' ⟶ E' := homotopyFiberPoint.{max uZ uE uB} f b e₀ h
    let c : homotopyQuotient.obj Z' ⟶ homotopyQuotient.obj E' :=
      homotopyQuotient.map (ofHomULift.{max uZ uE uB} (ContinuousMap.const Z e₀) rfl)
    Set.range (homotopyPostcomp Z' J) = (homotopyPostcomp Z' p) ⁻¹' {c} := by
  dsimp only
  ext q
  obtain ⟨g, hg, rfl⟩ :=
    exists_homotopyQuotient_map_ofHomULift_eq.{max uZ uE uB}
      Z (ContinuousMap.HomotopyFiber f b) z₀ (ContinuousMap.HomotopyFiber.const e₀ h) q
  refine (mem_range_homotopyPostcomp_ofHomULift_iff.{max uZ uE uB}
    z₀ (Path.refl b) (ContinuousMap.HomotopyFiber.const e₀ h)
    (ContinuousMap.HomotopyFiber.loopInclusion f b e₀ h)
    (ContinuousMap.HomotopyFiber.loopInclusion_refl f b e₀ h) g hg).trans ?_
  refine Iff.trans ?_
    (mem_preimage_homotopyPostcomp_ofHomULift_const_iff.{max uZ uE uB}
      z₀ (ContinuousMap.HomotopyFiber.const e₀ h) e₀
      (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
      (ContinuousMap.HomotopyFiber.point_const e₀ h) g hg).symm
  constructor
  · rintro ⟨γ, _, Hγ⟩
    have Hpoint := Hγ.comp_continuousMap
      (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
    rw [← ContinuousMap.comp_assoc,
      ContinuousMap.HomotopyFiber.point_comp_loopInclusion, ContinuousMap.const_comp] at Hpoint
    exact Hpoint.symm
  · rintro ⟨H⟩
    obtain ⟨γ, hγ, Hγ⟩ :=
      ContinuousMap.HomotopyFiber.exists_loop_of_projection_nullhomotopyRel
        {z₀} f b e₀ h g (Set.forall_mem_singleton.mpr hg) H
    exact ⟨γ, hγ z₀ (Set.mem_singleton z₀), Hγ⟩

/-- For every based source, the image of the original loop map consists exactly
of classes whose loop inclusion is constant. This is the loop
position of May's fiber-sequence exactness (Chapter 8, §6, pp. 61–62), stated as
a range identity without a sign or a group structure on these hom-sets. -/
theorem range_homotopyFiberLoopMap.{uZ, uE, uB}
    (Z : Type uZ) (E : Type uE) (B : Type uB)
    [TopologicalSpace Z] [TopologicalSpace E] [TopologicalSpace B]
    (z₀ : Z) (e₀ : E) (b : B) (f : C(E, B)) (h : f e₀ = b) :
    let Z' : BasedTopCat.{max uZ uE uB} := ofULift.{max uZ uE uB} Z z₀
    let F' : BasedTopCat.{max uZ uE uB} :=
      ofULift.{max uZ uE uB} (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h)
    let ΩE : BasedTopCat.{max uZ uE uB} :=
      ofULift.{max uZ uE uB} (Path e₀ e₀) (Path.refl e₀)
    let ΩB : BasedTopCat.{max uZ uE uB} :=
      ofULift.{max uZ uE uB} (Path b b) (Path.refl b)
    let Ωf : ΩE ⟶ ΩB := loopMapHom.{max uZ uE uB} f e₀ b h
    let J : ΩB ⟶ F' := homotopyFiberLoopInclusion.{max uZ uE uB} f b e₀ h
    let c : homotopyQuotient.obj Z' ⟶ homotopyQuotient.obj F' :=
      homotopyQuotient.map (ofHomULift.{max uZ uE uB}
        (ContinuousMap.const Z (ContinuousMap.HomotopyFiber.const e₀ h)) rfl)
    Set.range (homotopyPostcomp Z' Ωf) = (homotopyPostcomp Z' J) ⁻¹' {c} := by
  dsimp only
  ext q
  obtain ⟨γ, hγ, rfl⟩ :=
    exists_homotopyQuotient_map_ofHomULift_eq.{max uZ uE uB}
      Z (Path b b) z₀ (Path.refl b) q
  refine (mem_range_homotopyPostcomp_ofHomULift_iff.{max uZ uE uB}
    z₀ (Path.refl e₀) (Path.refl b) (f.loopMap e₀ b h) (f.loopMap_refl e₀ b h) γ hγ).trans ?_
  refine Iff.trans ?_
    (mem_preimage_homotopyPostcomp_ofHomULift_const_iff.{max uZ uE uB}
      z₀ (Path.refl b) (ContinuousMap.HomotopyFiber.const e₀ h)
      (ContinuousMap.HomotopyFiber.loopInclusion f b e₀ h)
      (ContinuousMap.HomotopyFiber.loopInclusion_refl f b e₀ h) γ hγ).symm
  constructor
  · rintro ⟨α, hα, Hα⟩
    have Hnull := ContinuousMap.HomotopicRel.precomp_continuousMap
      (ContinuousMap.HomotopyFiber.homotopicRel_loopInclusion_comp_loopMap_const f b e₀ h) α
      (Set.mapsTo_singleton.mpr (Set.mem_singleton_iff.mpr hα))
    exact (Hα.comp_continuousMap
      (ContinuousMap.HomotopyFiber.loopInclusion f b e₀ h)).symm.trans Hnull
  · rintro ⟨H⟩
    obtain ⟨α, hα, Hα⟩ :=
      ContinuousMap.HomotopyFiber.exists_loop_preimage_of_inclusion_nullhomotopyRel
        f b e₀ h {z₀} γ (Set.forall_mem_singleton.mpr hγ) H
    exact ⟨α, hα z₀ (Set.mem_singleton z₀), Hα⟩

end BasedTopCat
