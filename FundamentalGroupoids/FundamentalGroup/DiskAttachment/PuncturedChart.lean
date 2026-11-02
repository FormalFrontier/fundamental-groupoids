/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCoverCyclicIntersection
public import FundamentalGroupoids.FundamentalGroup.ComplexPuncturedBall
public import FundamentalGroupoids.FundamentalGroup.DiskAttachment
public import FundamentalGroupoids.FundamentalGroup.HomotopyEquiv
public import FundamentalGroupoids.Topology.Category.TopCat.DiskAttachment.PuncturedChart
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Fundamental-group homomorphisms of a punctured attachment chart

The punctured unit ball parametrizes the intersection of the two pieces of a
punctured attachment chart. Composing this parametrization with inclusion into
the core piece and the inverse core homeomorphism gives a map to the punctured
attachment component. On the half-radius circle this composite is the component
half-circle.

Consequently the inverse integer classification of the punctured ball, followed
by this induced based homomorphism, is the inverse circle classification followed
by the half-circle homomorphism. Evaluating this equality gives the image of every
integer class as the corresponding half-circle loop class. The basepoint is the
image of `1 : Circle` on that half-circle; no change of basepoint to the original
attachment basepoint is asserted by these two identities.

The positive integer class, transported back along the component radial path,
is the component generator. Inclusion into the chart kills this generator:
the half-circle factors through the open disk, whose fundamental group is
trivial, and naturality of change of basepoint transports this calculation
to the component basepoint.

The core and overlap homeomorphisms also give a commutative square of whole
fundamental-group homomorphisms, with the core basepoint equality derived from
the half-circle identity. Only the forward maps of the resulting equivalences
are used.

The whole change-of-basepoint square for the chart inclusion uses the radial
path in the component and its mapped path in the chart. The latter ends at the
chosen point of the overlap parametrization, using the equality of the overlap
and core maps on the half-radius circle.

Restriction along the component inclusion identifies homomorphisms from the
chart fundamental group with homomorphisms from the component fundamental group
that kill its selected positive generator. The forward and inverse projection
laws use that same inclusion at the component basepoint.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–7:
  the based van Kampen theorem.
* `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCoverCyclicIntersection`
  supplies the two-open homomorphism equivalence.
-/

@[expose] public section

noncomputable section

universe u v w

namespace FundamentalGroup

open TopCat TopCat.DiskAttachment

variable {X : Type u} [TopologicalSpace X] {J : Type v}

/-- The overlap-to-core homomorphism intertwines the inverse punctured-ball and
circle classifications, with the component half-circle as target map. -/
theorem mapOfEq_chartCoreOverlap_comp_puncturedBallFundamentalGroupEquivInt_symm
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    let μ : C(↥(Metric.ball (0 : ℂ) 1 \ {0}), diskAttachmentPuncturedComponent f x) :=
      (((isEmbedding_chartCore f x j).toHomeomorph.trans
          (Homeomorph.setCongr (range_chartCore f x j))).symm :
        C(↥(coreCover f x j), diskAttachmentPuncturedComponent f x)).comp
        ((ContinuousMap.inclusion
            (Set.inter_subset_left :
              coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j)).comp
          (overlapHomeomorph f x j hj :
            C(↥(Metric.ball (0 : ℂ) 1 \ {0}), ↥(coreCover f x j ∩ diskCover f x j))))
    (mapOfEq μ
        (congrArg (fun m : C(Circle, diskAttachmentPuncturedComponent f x) => m 1)
          (chartCoreHomeomorph_symm_comp_overlap_halfCircle f x j hj))).comp
        (Complex.puncturedBallFundamentalGroupEquivInt
          (1 / 2) 1 one_half_pos one_half_lt_one).symm.toMonoidHom =
      (map (diskAttachmentPuncturedComponentHalfCircle f x j hj) (1 : Circle)).comp
        Circle.fundamentalGroupEquivInt.symm.toMonoidHom := by
  let μ : C(↥(Metric.ball (0 : ℂ) 1 \ {0}), diskAttachmentPuncturedComponent f x) :=
    (((isEmbedding_chartCore f x j).toHomeomorph.trans
        (Homeomorph.setCongr (range_chartCore f x j))).symm :
      C(↥(coreCover f x j), diskAttachmentPuncturedComponent f x)).comp
      ((ContinuousMap.inclusion
          (Set.inter_subset_left :
            coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j)).comp
        (overlapHomeomorph f x j hj :
          C(↥(Metric.ball (0 : ℂ) 1 \ {0}), ↥(coreCover f x j ∩ diskCover f x j))))
  let σ := Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one
  let γ := diskAttachmentPuncturedComponentHalfCircle f x j hj
  have hμ : μ (σ 1) = γ 1 :=
    congrArg (fun m : C(Circle, diskAttachmentPuncturedComponent f x) => m 1)
      (chartCoreHomeomorph_symm_comp_overlap_halfCircle f x j hj)
  change (mapOfEq μ hμ).comp
      (Complex.puncturedBallFundamentalGroupEquivInt
        (1 / 2) 1 one_half_pos one_half_lt_one).symm.toMonoidHom =
    (map γ (1 : Circle)).comp Circle.fundamentalGroupEquivInt.symm.toMonoidHom
  have hwhole : μ.comp σ = γ := by
    simpa only [μ, σ, γ, ContinuousMap.comp_assoc] using
      chartCoreHomeomorph_symm_comp_overlap_halfCircle f x j hj
  have hcomp : (mapOfEq μ hμ).comp (map σ (1 : Circle)) = map γ (1 : Circle) := by
    simpa only [hwhole, mapOfEq_rfl] using
      (mapOfEq_comp μ σ (rfl : σ 1 = σ 1) hμ).symm
  rw [Complex.puncturedBallFundamentalGroupEquivInt_symm_toMonoidHom,
    ← MonoidHom.comp_assoc, hcomp]

/-- Every integer class of the overlap annulus maps to the corresponding loop
on the component half-circle, based at its image of `1 : Circle`. -/
theorem mapOfEq_chartCoreOverlap_puncturedBallFundamentalGroupEquivInt_symm_ofAdd
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) (n : ℤ) :
    let μ : C(↥(Metric.ball (0 : ℂ) 1 \ {0}), diskAttachmentPuncturedComponent f x) :=
      (((isEmbedding_chartCore f x j).toHomeomorph.trans
          (Homeomorph.setCongr (range_chartCore f x j))).symm :
        C(↥(coreCover f x j), diskAttachmentPuncturedComponent f x)).comp
        ((ContinuousMap.inclusion
            (Set.inter_subset_left :
              coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j)).comp
          (overlapHomeomorph f x j hj :
            C(↥(Metric.ball (0 : ℂ) 1 \ {0}), ↥(coreCover f x j ∩ diskCover f x j))))
    mapOfEq μ
        (congrArg (fun m : C(Circle, diskAttachmentPuncturedComponent f x) => m 1)
          (chartCoreHomeomorph_symm_comp_overlap_halfCircle f x j hj))
        ((Complex.puncturedBallFundamentalGroupEquivInt
          (1 / 2) 1 one_half_pos one_half_lt_one).symm (Multiplicative.ofAdd n)) =
      fromPath ⟦(Circle.loop n).map
        (diskAttachmentPuncturedComponentHalfCircle f x j hj).continuous⟧ := by
  have h := DFunLike.congr_fun
    (mapOfEq_chartCoreOverlap_comp_puncturedBallFundamentalGroupEquivInt_symm f x j hj)
    (Multiplicative.ofAdd n)
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Complex.puncturedBallFundamentalGroupEquivInt_symm_ofAdd,
    Circle.fundamentalGroupEquivInt_symm_apply, map_fromPath] using h

/-- The positive annulus class, mapped into the component and transported back
along the radial path, is the component generator. -/
theorem diskAttachmentPuncturedComponentOverlap_generator
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    let μ : C(↥(Metric.ball (0 : ℂ) 1 \ {0}), diskAttachmentPuncturedComponent f x) :=
      (((isEmbedding_chartCore f x j).toHomeomorph.trans
          (Homeomorph.setCongr (range_chartCore f x j))).symm :
        C(↥(coreCover f x j), diskAttachmentPuncturedComponent f x)).comp
        ((ContinuousMap.inclusion
            (Set.inter_subset_left :
              coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j)).comp
          (overlapHomeomorph f x j hj :
            C(↥(Metric.ball (0 : ℂ) 1 \ {0}), ↥(coreCover f x j ∩ diskCover f x j))))
    fundamentalGroupMulEquivOfPath
        (diskAttachmentPuncturedComponentRadialPath f x j hj).symm
        (mapOfEq μ
          (congrArg (fun m : C(Circle, diskAttachmentPuncturedComponent f x) => m 1)
            (chartCoreHomeomorph_symm_comp_overlap_halfCircle f x j hj))
          ((Complex.puncturedBallFundamentalGroupEquivInt
            (1 / 2) 1 one_half_pos one_half_lt_one).symm
            (Multiplicative.ofAdd (1 : ℤ)))) =
      diskAttachmentPuncturedComponentGenerator f x j hj := by
  have h := congrArg
    (fundamentalGroupMulEquivOfPath
      (diskAttachmentPuncturedComponentRadialPath f x j hj).symm)
    (mapOfEq_chartCoreOverlap_puncturedBallFundamentalGroupEquivInt_symm_ofAdd
      f x j hj (1 : ℤ))
  exact h.trans (by
    simpa only [map_fromPath] using
      diskAttachmentPuncturedComponentHalfCircle_transport f x j hj)

/-- The component half-circle followed into the chart induces the trivial
homomorphism, because it factors through the open disk. -/
theorem map_chartCore_comp_halfCircle_eq_one
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (z : Circle) (a : FundamentalGroup Circle z) :
    map ((chartCore f x j).comp
        (diskAttachmentPuncturedComponentHalfCircle f x j hj)) z a = 1 := by
  let : ContractibleSpace ↥(Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) (1 : ℝ)).contractibleSpace ⟨0, by simp⟩
  -- Transport the assertion, including its target basepoint, along the whole map.
  apply Eq.mp (congrArg
    (fun g : C(Circle, PuncturedChart f x j) => map g z a = 1)
    (chartOverlap_comp_halfCircle f x j hj))
  have hOverlap : chartOverlap f x j = (chartDisk f x j).comp puncturedBallInclusion :=
    ContinuousMap.ext fun q => chartOverlap_apply f x j q
  rw [hOverlap, ContinuousMap.comp_assoc, map_comp, MonoidHom.comp_apply]
  have ha : map (puncturedBallInclusion.comp
      (Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one)) z a = 1 :=
    Subsingleton.elim _ _
  rw [ha, map_one]

/-- Inclusion of the punctured component into a chart kills the generator of
that chart at the component basepoint. -/
theorem map_chartCore_diskAttachmentPuncturedComponentGenerator_eq_one
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    map (chartCore f x j) (diskAttachmentPuncturedComponentBasepoint f x)
        (diskAttachmentPuncturedComponentGenerator f x j hj) = 1 := by
  have hhalf := map_chartCore_comp_halfCircle_eq_one f x j hj (1 : Circle)
    (fromPath ⟦Circle.loop 1⟧)
  rw [map_comp, MonoidHom.comp_apply] at hhalf
  rw [← diskAttachmentPuncturedComponentHalfCircle_transport f x j hj,
    map_fundamentalGroupMulEquivOfPath, hhalf, map_one]

/-- The core and overlap homeomorphisms intertwine the overlap-to-component
homomorphism with inclusion of the intersection into the core piece. The core
basepoint adjustment is determined by the whole half-circle identity. -/
theorem chartCoreOverlap_mulEquivEnd_square
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    let L := (isEmbedding_chartCore f x j).toHomeomorph.trans
      (Homeomorph.setCongr (range_chartCore f x j))
    let O := overlapHomeomorph f x j hj
    let σ := Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one
    let γ := diskAttachmentPuncturedComponentHalfCircle f x j hj
    let i := ContinuousMap.inclusion
      (Set.inter_subset_left : coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j)
    let μ : C(↥(Metric.ball (0 : ℂ) 1 \ {0}), diskAttachmentPuncturedComponent f x) :=
      (L.symm : C(↥(coreCover f x j), diskAttachmentPuncturedComponent f x)).comp
        (i.comp (O : C(↥(Metric.ball (0 : ℂ) 1 \ {0}),
          ↥(coreCover f x j ∩ diskCover f x j))))
    let hμ : μ (σ 1) = γ 1 :=
      congrArg (fun m : C(Circle, diskAttachmentPuncturedComponent f x) => m 1)
        (chartCoreHomeomorph_symm_comp_overlap_halfCircle f x j hj)
    let hU : L (γ 1) = i (O (σ 1)) :=
      (congrArg L hμ).symm.trans (L.apply_symm_apply (i (O (σ 1))))
    let μO : FundamentalGroup ↥(Metric.ball (0 : ℂ) 1 \ {0}) (σ 1) ≃*
        FundamentalGroup ↥(coreCover f x j ∩ diskCover f x j) (O (σ 1)) :=
      (CategoryTheory.Functor.FullyFaithful.mulEquivEnd
        (C := FundamentalGroupoid ↥(Metric.ball (0 : ℂ) 1 \ {0}))
        (D := FundamentalGroupoid ↥(coreCover f x j ∩ diskCover f x j))
        (f := FundamentalGroupoid.map O.toHomotopyEquiv.toFun)
        (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
          O.toHomotopyEquiv).fullyFaithfulFunctor
        (FundamentalGroupoid.mk (σ 1))).trans
          (CategoryTheory.Iso.conj
            (C := FundamentalGroupoid ↥(coreCover f x j ∩ diskCover f x j))
            (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk
              (rfl : O (σ 1) = O (σ 1)))))
    let μU : FundamentalGroup (diskAttachmentPuncturedComponent f x) (γ 1) ≃*
        FundamentalGroup ↥(coreCover f x j) (i (O (σ 1))) :=
      (CategoryTheory.Functor.FullyFaithful.mulEquivEnd
        (C := FundamentalGroupoid (diskAttachmentPuncturedComponent f x))
        (D := FundamentalGroupoid ↥(coreCover f x j))
        (f := FundamentalGroupoid.map L.toHomotopyEquiv.toFun)
        (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
          L.toHomotopyEquiv).fullyFaithfulFunctor
        (FundamentalGroupoid.mk (γ 1))).trans
          (CategoryTheory.Iso.conj (C := FundamentalGroupoid ↥(coreCover f x j))
            (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk hU)))
    μU.toMonoidHom.comp (mapOfEq μ hμ) =
      (map i (O (σ 1))).comp μO.toMonoidHom := by
  let L := (isEmbedding_chartCore f x j).toHomeomorph.trans
    (Homeomorph.setCongr (range_chartCore f x j))
  let O := overlapHomeomorph f x j hj
  let σ := Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one
  let γ := diskAttachmentPuncturedComponentHalfCircle f x j hj
  let i := ContinuousMap.inclusion
    (Set.inter_subset_left : coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j)
  have hμ : L.symm (i (O (σ 1))) = γ 1 := by
    simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_coe] using
      congrArg (fun m : C(Circle, diskAttachmentPuncturedComponent f x) => m 1)
        (chartCoreHomeomorph_symm_comp_overlap_halfCircle f x j hj)
  have hLPoint : L (γ 1) = i (O (σ 1)) :=
    (congrArg L hμ).symm.trans (L.apply_symm_apply (i (O (σ 1))))
  have hOPoint : O.toHomotopyEquiv.toFun (σ 1) = O (σ 1) :=
    congrFun (Homeomorph.coe_toHomotopyEquiv O) (σ 1)
  have hLHomotopyPoint : L.toHomotopyEquiv.toFun (γ 1) = i (O (σ 1)) :=
    (congrFun (Homeomorph.coe_toHomotopyEquiv L) (γ 1)).trans hLPoint
  dsimp only
  rw [homotopyEquiv_mulEquivEnd_trans_conj_toMonoidHom
      L.toHomotopyEquiv (γ 1) (i (O (σ 1))) hLHomotopyPoint,
    homotopyEquiv_mulEquivEnd_trans_conj_toMonoidHom
      O.toHomotopyEquiv (σ 1) (O (σ 1)) hOPoint]
  rw [← mapOfEq_comp, ← mapOfEq_rfl, ← mapOfEq_comp]
  congr 1
  apply ContinuousMap.ext
  intro q
  simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_coe,
    Homeomorph.coe_toHomotopyEquiv] using
    (((isEmbedding_chartCore f x j).toHomeomorph.trans
      (Homeomorph.setCongr (range_chartCore f x j))).apply_symm_apply
        ((ContinuousMap.inclusion
          (Set.inter_subset_left : coreCover f x j ∩ diskCover f x j ⊆ coreCover f x j))
          (overlapHomeomorph f x j hj q)))

/-- The chart inclusion commutes with transport along the component radial path,
with the image path ending at the half-radius point of the overlap parametrization. -/
theorem mapOfEq_chartCore_comp_radialPath
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x) :
    let k := chartCore f x j
    let β := diskAttachmentPuncturedComponentRadialPath f x j hj
    let σ := Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one
    let h₁ : k (diskAttachmentPuncturedComponentHalfCircle f x j hj 1) =
        chartOverlap f x j (σ 1) :=
      congrArg (fun m : C(Circle, PuncturedChart f x j) => m 1)
        (chartOverlap_comp_halfCircle f x j hj).symm
    (mapOfEq k h₁).comp (fundamentalGroupMulEquivOfPath β).toMonoidHom =
      (fundamentalGroupMulEquivOfPath
        ((β.map k.continuous).cast rfl h₁.symm)).toMonoidHom.comp
          (map k (diskAttachmentPuncturedComponentBasepoint f x)) := by
  simpa only [mapOfEq_rfl] using
    (mapOfEq_comp_fundamentalGroupMulEquivOfPath (chartCore f x j)
      (diskAttachmentPuncturedComponentRadialPath f x j hj) rfl
      (congrArg (fun m : C(Circle, PuncturedChart f x j) => m 1)
        (chartOverlap_comp_halfCircle f x j hj).symm))

private theorem diskAttachmentPuncturedChart_restriction_bijective
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (H : Type w) [Group H] :
    Function.Bijective
      (fun φ : FundamentalGroup (PuncturedChart f x j)
          (chartCore f x j (diskAttachmentPuncturedComponentBasepoint f x)) →* H =>
        (⟨φ.comp (map (chartCore f x j) (diskAttachmentPuncturedComponentBasepoint f x)),
          by
            change φ (map (chartCore f x j) _
              (diskAttachmentPuncturedComponentGenerator f x j hj)) = 1
            rw [map_chartCore_diskAttachmentPuncturedComponentGenerator_eq_one, map_one]⟩ :
          {a : FundamentalGroup (diskAttachmentPuncturedComponent f x)
            (diskAttachmentPuncturedComponentBasepoint f x) →* H //
            a (diskAttachmentPuncturedComponentGenerator f x j hj) = 1})) := by
  let U : TopologicalSpace.Opens (PuncturedChart f x j) :=
    ⟨coreCover f x j, isOpen_coreCover f x j hj⟩
  let V : TopologicalSpace.Opens (PuncturedChart f x j) :=
    ⟨diskCover f x j, isOpen_diskCover f x j⟩
  have hcover : U ⊔ V = ⊤ := by
    apply SetLike.coe_injective
    exact coreCover_union_diskCover f x j
  let : PathConnectedSpace (diskAttachmentPuncturedComponent f x) :=
    diskAttachmentPuncturedComponent_pathConnectedSpace f x
  have hU : IsPathConnected (U : Set (PuncturedChart f x j)) := by
    change IsPathConnected (coreCover f x j)
    rw [← range_chartCore f x j]
    exact isPathConnected_range (chartCore f x j).continuous
  let : ContractibleSpace V := contractibleSpace_diskCover f x j
  let : SimplyConnectedSpace V := SimplyConnectedSpace.ofContractible V
  have hV : IsPathConnected (V : Set (PuncturedChart f x j)) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hI : IsPathConnected (↑(U ⊓ V) : Set (PuncturedChart f x j)) :=
    isPathConnected_overlap f x j hj
  let L : diskAttachmentPuncturedComponent f x ≃ₜ U :=
    (isEmbedding_chartCore f x j).toHomeomorph.trans
      (Homeomorph.setCongr (range_chartCore f x j))
  let O : ↥(Metric.ball (0 : ℂ) 1 \ {0}) ≃ₜ ↑(U ⊓ V) :=
    overlapHomeomorph f x j hj
  let σ := Complex.circleToPuncturedBall (1 / 2) 1 one_half_pos one_half_lt_one
  let γ := diskAttachmentPuncturedComponentHalfCircle f x j hj
  let β := diskAttachmentPuncturedComponentRadialPath f x j hj
  let k := chartCore f x j
  let p : ↑(U ⊓ V) := O (σ 1)
  let : Subsingleton (FundamentalGroup V (⟨p.1, p.2.2⟩ : V)) := inferInstance
  let pU : U := ⟨p.1, p.2.1⟩
  let i : C(↑(U ⊓ V), U) := ContinuousMap.inclusion Set.inter_subset_left
  let vU : C(U, PuncturedChart f x j) :=
    ContinuousMap.subtypeVal (U : Set (PuncturedChart f x j))
  let μ : C(↥(Metric.ball (0 : ℂ) 1 \ {0}), diskAttachmentPuncturedComponent f x) :=
    (L.symm : C(U, diskAttachmentPuncturedComponent f x)).comp
      (i.comp (O : C(↥(Metric.ball (0 : ℂ) 1 \ {0}), ↑(U ⊓ V))))
  let hμ : μ (σ 1) = γ 1 :=
    congrArg (fun m : C(Circle, diskAttachmentPuncturedComponent f x) => m 1)
      (chartCoreHomeomorph_symm_comp_overlap_halfCircle f x j hj)
  let hLPoint : L (γ 1) = pU :=
    (congrArg L hμ).symm.trans (L.apply_symm_apply (i (O (σ 1))))
  let μO : FundamentalGroup ↥(Metric.ball (0 : ℂ) 1 \ {0}) (σ 1) ≃*
      FundamentalGroup ↑(U ⊓ V) p :=
    (CategoryTheory.Functor.FullyFaithful.mulEquivEnd
      (C := FundamentalGroupoid ↥(Metric.ball (0 : ℂ) 1 \ {0}))
      (D := FundamentalGroupoid ↑(U ⊓ V))
      (f := FundamentalGroupoid.map O.toHomotopyEquiv.toFun)
      (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
        O.toHomotopyEquiv).fullyFaithfulFunctor
      (FundamentalGroupoid.mk (σ 1))).trans
        (CategoryTheory.Iso.conj (C := FundamentalGroupoid ↑(U ⊓ V))
          (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk
            (rfl : O (σ 1) = p))))
  let μU : FundamentalGroup (diskAttachmentPuncturedComponent f x) (γ 1) ≃*
      FundamentalGroup U pU :=
    (CategoryTheory.Functor.FullyFaithful.mulEquivEnd
      (C := FundamentalGroupoid (diskAttachmentPuncturedComponent f x))
      (D := FundamentalGroupoid U)
      (f := FundamentalGroupoid.map L.toHomotopyEquiv.toFun)
      (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
        L.toHomotopyEquiv).fullyFaithfulFunctor
      (FundamentalGroupoid.mk (γ 1))).trans
        (CategoryTheory.Iso.conj (C := FundamentalGroupoid U)
          (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk hLPoint)))
  let Eann := Complex.puncturedBallFundamentalGroupEquivInt
    (1 / 2) 1 one_half_pos one_half_lt_one
  let ε : FundamentalGroup ↑(U ⊓ V) p ≃* Multiplicative ℤ := μO.symm.trans Eann
  let rU := map i p (ε.symm (Multiplicative.ofAdd (1 : ℤ)))
  let dC := fundamentalGroupMulEquivOfPath β.symm
  let D : FundamentalGroup U pU ≃*
      FundamentalGroup (diskAttachmentPuncturedComponent f x)
        (diskAttachmentPuncturedComponentBasepoint f x) := μU.symm.trans dC
  -- Use the whole forward square; no inverse-map formula for an unbased
  -- homotopy equivalence is needed to identify the positive relation.
  have hrelation : μU (mapOfEq μ hμ (Eann.symm (Multiplicative.ofAdd (1 : ℤ)))) =
      rU := by
    change μU (mapOfEq μ hμ (Eann.symm (Multiplicative.ofAdd (1 : ℤ)))) =
      map i p (μO (Eann.symm (Multiplicative.ofAdd (1 : ℤ))))
    exact DFunLike.congr_fun (chartCoreOverlap_mulEquivEnd_square f x j hj)
      (Eann.symm (Multiplicative.ofAdd (1 : ℤ)))
  have hgen : D rU = diskAttachmentPuncturedComponentGenerator f x j hj := by
    change dC (μU.symm rU) = _
    rw [← hrelation, μU.symm_apply_apply]
    exact diskAttachmentPuncturedComponentOverlap_generator f x j hj
  have hL : vU.comp (L : C(diskAttachmentPuncturedComponent f x, U)) = k := by
    ext z
    rfl
  have h₁ : k (γ 1) = p.1 := by
    calc
      k (γ 1) = vU (L (γ 1)) := by
        simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_coe] using
          (DFunLike.congr_fun hL (γ 1)).symm
      _ = vU pU := congrArg vU hLPoint
      _ = p.1 := by rfl
  let dT : FundamentalGroup (PuncturedChart f x j) p.1 ≃*
      FundamentalGroup (PuncturedChart f x j)
        (k (diskAttachmentPuncturedComponentBasepoint f x)) :=
    fundamentalGroupMulEquivOfPath ((β.symm.map k.continuous).cast h₁.symm rfl)
  let q₀ := map k (diskAttachmentPuncturedComponentBasepoint f x)
  let mU : FundamentalGroup U pU →*
      FundamentalGroup (PuncturedChart f x j) p.1 := map vU pU
  have hpU : vU pU = p.1 := by rfl
  have hmU : mU = mapOfEq vU hpU := (mapOfEq_rfl vU pU).symm
  have hLMap : L.toHomotopyEquiv.toFun =
      (L : C(diskAttachmentPuncturedComponent f x, U)) := by
    apply ContinuousMap.ext
    intro z
    exact congrFun (Homeomorph.coe_toHomotopyEquiv L) z
  have hLHomotopyPoint : L.toHomotopyEquiv.toFun (γ 1) = pU :=
    (congrFun (Homeomorph.coe_toHomotopyEquiv L) (γ 1)).trans hLPoint
  have hμU : μU.toMonoidHom =
      mapOfEq (L : C(diskAttachmentPuncturedComponent f x, U)) hLPoint := by
    dsimp only [μU]
    exact (homotopyEquiv_mulEquivEnd_trans_conj_toMonoidHom
      L.toHomotopyEquiv (γ 1) pU hLHomotopyPoint).trans
        (mapOfEq_congr hLMap hLHomotopyPoint hLPoint)
  have hcore : mU.comp μU.toMonoidHom = mapOfEq k h₁ := by
    calc
      mU.comp μU.toMonoidHom = (mapOfEq vU hpU).comp
          (mapOfEq (L : C(diskAttachmentPuncturedComponent f x, U)) hLPoint) := by
        rw [hmU, hμU]
      _ = mapOfEq (vU.comp (L : C(diskAttachmentPuncturedComponent f x, U)))
          ((congrArg vU hLPoint).trans hpU) :=
        (mapOfEq_comp vU (L : C(diskAttachmentPuncturedComponent f x, U))
          hLPoint hpU).symm
      _ = mapOfEq k h₁ :=
        mapOfEq_congr hL ((congrArg vU hLPoint).trans hpU) h₁
  have hback : q₀.comp dC.toMonoidHom =
      dT.toMonoidHom.comp (mapOfEq k h₁) := by
    simpa only [mapOfEq_rfl] using
      (mapOfEq_comp_fundamentalGroupMulEquivOfPath k β.symm h₁ rfl)
  have hsquare : q₀.comp D.toMonoidHom = dT.toMonoidHom.comp mU := by
    apply MonoidHom.ext
    intro a
    have ht : mapOfEq k h₁ (μU.symm a) = mU a := by
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        μU.apply_symm_apply] using
        (DFunLike.congr_fun hcore (μU.symm a)).symm
    exact (DFunLike.congr_fun hback (μU.symm a)).trans (congrArg dT ht)
  let E := homEquivOfIsOpenCoverCyclicIntersection U V hcover hU hV hI p ε H
  constructor
  · intro φ ψ h
    have hrestrict : φ.comp q₀ = ψ.comp q₀ := congrArg Subtype.val h
    have hraw : φ.comp dT.toMonoidHom = ψ.comp dT.toMonoidHom := by
      apply E.injective
      apply Subtype.ext
      simp only [E, homEquivOfIsOpenCoverCyclicIntersection_apply_val]
      apply MonoidHom.ext
      intro a
      change φ (dT (mU a)) = ψ (dT (mU a))
      exact (congrArg φ (DFunLike.congr_fun hsquare a).symm).trans
        ((DFunLike.congr_fun hrestrict (D a)).trans
          (congrArg ψ (DFunLike.congr_fun hsquare a)))
    apply MonoidHom.ext
    intro z
    obtain ⟨a, rfl⟩ := dT.surjective z
    exact DFunLike.congr_fun hraw a
  · intro a
    let aU : FundamentalGroup U pU →* H := a.val.comp D.toMonoidHom
    have haU : aU rU = 1 := by
      change a.val (D rU) = 1
      rw [hgen]
      exact a.property
    let φraw := E.symm ⟨aU, haU⟩
    have hraw : φraw.comp mU = aU :=
      homEquivOfIsOpenCoverCyclicIntersection_symm_comp
        U V hcover hU hV hI p ε H ⟨aU, haU⟩
    refine ⟨φraw.comp dT.symm.toMonoidHom, Subtype.ext ?_⟩
    apply MonoidHom.ext
    intro z
    obtain ⟨b, rfl⟩ := D.surjective z
    change φraw (dT.symm (q₀ (D b))) = a.val (D b)
    have hsquare_b : q₀ (D b) = dT (mU b) := by
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using
        DFunLike.congr_fun hsquare b
    rw [hsquare_b, dT.symm_apply_apply]
    exact DFunLike.congr_fun hraw b

/-- The based van Kampen theorem for a punctured attachment chart: restriction
identifies chart homomorphisms with component homomorphisms killing the selected
positive attachment generator. The target group has an independent universe.

This uses the two-open form of van Kampen; see May, *A Concise Course in
Algebraic Topology*, Chapter 2, §§6–7. -/
noncomputable def diskAttachmentPuncturedChartHomEquiv
    {X : Type u} [tX : TopologicalSpace X] {J : Type v}
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (H : Type w) [gH : Group H] :
    (FundamentalGroup (TopCat.DiskAttachment.PuncturedChart f x j)
      (TopCat.DiskAttachment.chartCore f x j
        (TopCat.diskAttachmentPuncturedComponentBasepoint f x)) →* H) ≃
    {a : FundamentalGroup (TopCat.diskAttachmentPuncturedComponent f x)
      (TopCat.diskAttachmentPuncturedComponentBasepoint f x) →* H //
      a (diskAttachmentPuncturedComponentGenerator f x j hj) = 1} :=
  Equiv.ofBijective
    (fun φ => ⟨φ.comp (map (chartCore f x j)
      (diskAttachmentPuncturedComponentBasepoint f x)), by
        change φ (map (chartCore f x j) _
          (diskAttachmentPuncturedComponentGenerator f x j hj)) = 1
        rw [map_chartCore_diskAttachmentPuncturedComponentGenerator_eq_one, map_one]⟩)
    (by exact diskAttachmentPuncturedChart_restriction_bijective f x j hj H)

/-- The forward equivalence is restriction along the component inclusion. -/
@[simp]
theorem diskAttachmentPuncturedChartHomEquiv_apply_val
    {X : Type u} [tX : TopologicalSpace X] {J : Type v}
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (H : Type w) [gH : Group H]
    (φ : FundamentalGroup (TopCat.DiskAttachment.PuncturedChart f x j)
      (TopCat.DiskAttachment.chartCore f x j
        (TopCat.diskAttachmentPuncturedComponentBasepoint f x)) →* H) :
    (diskAttachmentPuncturedChartHomEquiv f x j hj H φ).val =
      φ.comp (FundamentalGroup.map (TopCat.DiskAttachment.chartCore f x j)
        (TopCat.diskAttachmentPuncturedComponentBasepoint f x)) := by
  rfl

/-- The inverse equivalence extends the supplied homomorphism along the same
component inclusion. -/
@[simp]
theorem diskAttachmentPuncturedChartHomEquiv_symm_comp
    {X : Type u} [tX : TopologicalSpace X] {J : Type v}
    (f : J → C(Circle, X)) (x : X) (j : J) (hj : f j 1 = x)
    (H : Type w) [gH : Group H]
    (a : {a : FundamentalGroup (TopCat.diskAttachmentPuncturedComponent f x)
      (TopCat.diskAttachmentPuncturedComponentBasepoint f x) →* H //
      a (diskAttachmentPuncturedComponentGenerator f x j hj) = 1}) :
    ((diskAttachmentPuncturedChartHomEquiv f x j hj H).symm a).comp
      (FundamentalGroup.map (TopCat.DiskAttachment.chartCore f x j)
        (TopCat.diskAttachmentPuncturedComponentBasepoint f x)) = a.val := by
  have h := congrArg Subtype.val
    ((diskAttachmentPuncturedChartHomEquiv f x j hj H).apply_symm_apply a)
  rw [diskAttachmentPuncturedChartHomEquiv_apply_val] at h
  exact h

end FundamentalGroup
