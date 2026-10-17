/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover
import all FundamentalGroupoidsTest.FundamentalGroup
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Order.SupClosed
import Mathlib.Topology.Category.TopCat.OpenNhds
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Tactic

/-!
# An increasing cover of the circle cylinder

The strips `AddCircle 1 × (-(n + 1), n + 1)`, indexed by the natural numbers, form an
infinite cover of `AddCircle 1 × ℝ` by proper path-connected open neighborhoods of
`(0, 0)`. The intersection of two strips is the strip with the smaller index, so their
range is closed under every nonempty finite intersection.

Projection to the circle and the zero-height section give compatible homomorphisms
on the fundamental groups of all the strips. Their target is the function group
`ULift.{2} Bool → FundamentalGroup (AddCircle 1) 0`, in a higher universe than the
cylinder. The section images of a specified nonidentity circle class remain
nonidentity, and their images in this target agree. No orientation of the circle
class is asserted.

## References

* `FundamentalGroupoidsTest.AlgebraicTopology.FundamentalGroup.OpenCover` supplies
  the circle-cylinder strip construction and its projection-section method.
* `FundamentalGroupoidsTest.FundamentalGroup` supplies the nonidentity circle class,
  constructed using Mathlib's quotient covering of the circle.
* Mathlib supplies open neighborhoods, convex-interval path connectedness, induced
  fundamental-group homomorphisms, and function groups.
-/

noncomputable section

open TopologicalSpace

namespace CircleCylinderIndexedCover

private abbrev A := AddCircle (1 : ℝ)
private abbrev X := A × ℝ
private abbrev point : X := (0, 0)

private def U (n : ℕ) : Opens X :=
  ⟨{q | -((n : ℝ) + 1) < q.2 ∧ q.2 < (n : ℝ) + 1},
    (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)⟩

private theorem commonPoint (n : ℕ) : point ∈ U n := by
  change -((n : ℝ) + 1) < 0 ∧ (0 : ℝ) < (n : ℝ) + 1
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor <;> linarith

private def localPoint (n : ℕ) : U n := ⟨point, commonPoint n⟩

private def W (n : ℕ) : OpenNhds (X := TopCat.of X) point :=
  ⟨U n, commonPoint n⟩

private theorem cover : IsOpenCover U := by
  apply IsOpenCover.mk
  apply top_unique
  intro q _
  apply Opens.mem_iSup.mpr
  obtain ⟨n, hn⟩ := exists_nat_gt |q.2|
  refine ⟨n, ?_⟩
  change -((n : ℝ) + 1) < q.2 ∧ q.2 < (n : ℝ) + 1
  have hupper := le_abs_self q.2
  have hlower := neg_abs_le q.2
  constructor <;> linarith

private theorem pathConnected (n : ℕ) : IsPathConnected (U n : Set X) := by
  have hU : (U n : Set X) =
      Set.univ ×ˢ Set.Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1) := by
    ext q
    simp [U]
  rw [hU]
  exact (isPathConnected_univ : IsPathConnected (Set.univ : Set A)).prod
    ((convex_Ioo (𝕜 := ℝ) (-((n : ℝ) + 1)) ((n : ℝ) + 1)).isPathConnected
      ⟨0, commonPoint n⟩)

private theorem monotone_U : Monotone U := by
  intro m n hmn q hq
  change -((m : ℝ) + 1) < q.2 ∧ q.2 < (m : ℝ) + 1 at hq
  change -((n : ℝ) + 1) < q.2 ∧ q.2 < (n : ℝ) + 1
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  constructor <;> linarith [hq.1, hq.2]

private theorem inf_eq (m n : ℕ) : U m ⊓ U n = U (min m n) := by
  rcases le_total m n with hmn | hnm
  · rw [min_eq_left hmn, inf_eq_left.mpr (monotone_U hmn)]
  · rw [min_eq_right hnm, inf_eq_right.mpr (monotone_U hnm)]

private theorem infClosed : InfClosed (Set.range U) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨min m n, (inf_eq m n).symm⟩

private theorem nhds_inf_eq (m n : ℕ) : W m ⊓ W n = W (min m n) := by
  apply Subtype.ext
  exact inf_eq m n

private theorem nhds_infClosed : InfClosed (Set.range W) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨min m n, (nhds_inf_eq m n).symm⟩

private theorem positive_finite_intersection (s : Finset ℕ) (hs : s.Nonempty) :
    s.inf W ∈ Set.range W :=
  nhds_infClosed.finsetInf_mem hs (fun n _ => ⟨n, rfl⟩)

private theorem proper (n : ℕ) : U n ≠ ⊤ := by
  intro h
  have hq : ((0, (n : ℝ) + 2) : X) ∈ U n := by
    rw [h]
    trivial
  have hlt : (n : ℝ) + 2 < (n : ℝ) + 1 := hq.2
  linarith

private theorem strictMono_U : StrictMono U := by
  intro m n hmn
  refine lt_iff_le_not_ge.mpr ⟨monotone_U hmn.le, ?_⟩
  intro hnm
  have hq : ((0, (m : ℝ) + 1) : X) ∈ U n := by
    change -((n : ℝ) + 1) < (m : ℝ) + 1 ∧
      (m : ℝ) + 1 < (n : ℝ) + 1
    have hmn' : (m : ℝ) < n := by exact_mod_cast hmn
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    constructor <;> linarith
  have hmem : ((0, (m : ℝ) + 1) : X) ∈ U m := hnm hq
  exact (lt_irrefl ((m : ℝ) + 1)) hmem.2

private theorem infinite_range : (Set.range U).Infinite :=
  Set.infinite_range_of_injective strictMono_U.injective

private theorem infinite_nhds_range : (Set.range W).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  apply strictMono_U.injective
  exact congrArg (fun V : OpenNhds (X := TopCat.of X) point => V.1) h

-- A cover of a space with the displayed point cannot have an empty index type.
private theorem empty_index_boundary (V : Empty → Opens X) : ¬ IsOpenCover V := by
  intro hV
  obtain ⟨i, _⟩ := hV.exists_mem point
  exact i.elim

private def inclusion {m n : ℕ} (h : U m ≤ U n) : C(U m, U n) :=
  ContinuousMap.inclusion h

private def j (n : ℕ) : C(U n, X) := ContinuousMap.subtypeVal (U n : Set X)

private def rX : C(X, A) := ContinuousMap.fst
private def r (n : ℕ) : C(U n, A) := rX.comp (j n)

private def sX : C(A, X) :=
  (ContinuousMap.id A).prodMk (ContinuousMap.const A (0 : ℝ))

private def s (n : ℕ) : C(A, U n) where
  toFun z := ⟨(z, 0), commonPoint n⟩
  continuous_toFun := (continuous_id.prodMk continuous_const).subtype_mk (by
    intro z
    exact commonPoint n)

private theorem group_retraction_X :
    (FundamentalGroup.map rX point).comp (FundamentalGroup.map sX (0 : A)) =
      MonoidHom.id (FundamentalGroup A 0) :=
  (FundamentalGroup.map_comp rX sX (0 : A)).symm.trans (FundamentalGroup.map_id (0 : A))

private theorem group_retraction (n : ℕ) :
    (FundamentalGroup.map (r n) (localPoint n)).comp
        (FundamentalGroup.map (s n) (0 : A)) =
      MonoidHom.id (FundamentalGroup A 0) :=
  (FundamentalGroup.map_comp (r n) (s n) (0 : A)).symm.trans
    (FundamentalGroup.map_id (0 : A))

private abbrev TargetIndex : Type 2 := ULift.{2} Bool
private abbrev G : Type 2 := TargetIndex → FundamentalGroup A 0

private def φX : FundamentalGroup X point →* G :=
  MonoidHom.pi (fun _ => FundamentalGroup.map rX point)

private def φ (n : ℕ) : FundamentalGroup (U n) (localPoint n) →* G :=
  MonoidHom.pi (fun _ => FundamentalGroup.map (r n) (localPoint n))

-- Compatibility is for every inclusion between members, not just consecutive indices.
private theorem hom_compatible {m n : ℕ} (h : U m ≤ U n) :
    (φ n).comp (FundamentalGroup.map (inclusion h) (localPoint m)) = φ m := by
  apply MonoidHom.ext
  intro γ
  funext b
  exact DFunLike.congr_fun
    (FundamentalGroup.map_comp (r n) (inclusion h) (localPoint m)).symm γ

private theorem hom_restrict (n : ℕ) :
    φX.comp (FundamentalGroup.map (j n) (localPoint n)) = φ n := by
  apply MonoidHom.ext
  intro γ
  funext b
  exact DFunLike.congr_fun
    (FundamentalGroup.map_comp rX (j n) (localPoint n)).symm γ

private def axisX : FundamentalGroup X point :=
  FundamentalGroup.map sX (0 : A) CircleTransport.loopClass

private def axis (n : ℕ) : FundamentalGroup (U n) (localPoint n) :=
  FundamentalGroup.map (s n) (0 : A) CircleTransport.loopClass

private theorem projection_axisX :
    FundamentalGroup.map rX point axisX = CircleTransport.loopClass :=
  DFunLike.congr_fun group_retraction_X CircleTransport.loopClass

private theorem projection_axis (n : ℕ) :
    FundamentalGroup.map (r n) (localPoint n) (axis n) = CircleTransport.loopClass :=
  DFunLike.congr_fun (group_retraction n) CircleTransport.loopClass

private theorem axis_inclusion {m n : ℕ} (h : U m ≤ U n) :
    FundamentalGroup.map (inclusion h) (localPoint m) (axis m) = axis n :=
  DFunLike.congr_fun (FundamentalGroup.map_comp (inclusion h) (s m) (0 : A)).symm
    CircleTransport.loopClass

private theorem axis_global (n : ℕ) :
    FundamentalGroup.map (j n) (localPoint n) (axis n) = axisX :=
  DFunLike.congr_fun (FundamentalGroup.map_comp (j n) (s n) (0 : A)).symm
    CircleTransport.loopClass

private def targetClass : G := fun _ => CircleTransport.loopClass

private theorem targetClass_ne_one : targetClass ≠ 1 := by
  intro h
  exact CircleTransport.loopClass_ne_one (congrFun h (ULift.up false))

private theorem hom_axisX : φX axisX = targetClass := by
  funext b
  exact projection_axisX

private theorem hom_axis (n : ℕ) : φ n (axis n) = targetClass := by
  funext b
  exact projection_axis n

private theorem axes_ne_one : axisX ≠ 1 ∧ ∀ n, axis n ≠ 1 := by
  constructor
  · intro h
    have hr := projection_axisX
    rw [h, map_one] at hr
    exact CircleTransport.loopClass_ne_one hr.symm
  · intro n h
    have hr := projection_axis n
    rw [h, map_one] at hr
    exact CircleTransport.loopClass_ne_one hr.symm

private theorem cylinder_model :
    IsOpenCover (fun n => (W n).1) ∧
      (∀ n, point ∈ U n) ∧ (∀ n, IsPathConnected (U n : Set X)) ∧
      InfClosed (Set.range W) ∧
      (∀ (s : Finset ℕ), s.Nonempty → s.inf W ∈ Set.range W) ∧
      (∀ n, U n ≠ ⊤) ∧ (Set.range U).Infinite ∧ (Set.range W).Infinite :=
  ⟨cover, commonPoint, pathConnected, nhds_infClosed,
    positive_finite_intersection, proper, infinite_range, infinite_nhds_range⟩

private theorem hom_model :
    (∀ (m n : ℕ) (h : U m ≤ U n),
      (φ n).comp (FundamentalGroup.map (inclusion h) (localPoint m)) = φ m) ∧
      (∀ n, φX.comp (FundamentalGroup.map (j n) (localPoint n)) = φ n) ∧
      targetClass ≠ 1 ∧ φX axisX = targetClass ∧
      (∀ n, φ n (axis n) = targetClass) ∧ axisX ≠ 1 ∧ ∀ n, axis n ≠ 1 :=
  ⟨fun _ _ h => hom_compatible h, hom_restrict,
    targetClass_ne_one, hom_axisX, hom_axis, axes_ne_one.1, axes_ne_one.2⟩

-- The presentation index and target group lie in independent higher universes;
-- the cylinder and its chart spaces remain unlifted.
private abbrev CoverIndex : Type 1 := ULift.{1} ℕ

private def V (n : CoverIndex) : OpenNhds (X := TopCat.of X) point := W n.down

private theorem cover_V : IsOpenCover (fun n => (V n).1) := by
  apply IsOpenCover.mk
  apply top_unique
  intro q _
  obtain ⟨n, hn⟩ := cover.exists_mem q
  exact Opens.mem_iSup.mpr ⟨ULift.up n, hn⟩

private theorem infClosed_V : InfClosed (Set.range V) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨ULift.up (min m.down n.down), (nhds_inf_eq m.down n.down).symm⟩

private theorem universalProperty :
    ∃! ψ : FundamentalGroup X point →* G,
      ∀ n : CoverIndex,
        ψ.comp (FundamentalGroup.map (j n.down) (localPoint n.down)) = φ n.down := by
  have hUP :=
    FundamentalGroup.existsUnique_hom_of_isOpenCover_of_infClosed point V cover_V
      (fun n => pathConnected n.down) infClosed_V G (fun n => φ n.down) (by
        intro m n h
        rw [FundamentalGroup.openNhdsFunctor_map_hom]
        change (φ n.down).comp
          (FundamentalGroup.map (inclusion h) (localPoint m.down)) = φ m.down
        exact hom_compatible h)
  simp only [FundamentalGroup.openNhdsCocone_ι_app_hom] at hUP
  change ∃! ψ : FundamentalGroup X point →* G,
    ∀ n : CoverIndex,
      ψ.comp (FundamentalGroup.map (j n.down) (localPoint n.down)) = φ n.down at hUP
  exact hUP

private def colimit : CategoryTheory.Limits.IsColimit
    ((FundamentalGroup.openNhdsCocone point).whisker (CategoryTheory.inducedFunctor V)) :=
  FundamentalGroup.isColimit_of_isOpenCover point V cover_V
    (fun n => pathConnected n.down) infClosed_V

end CircleCylinderIndexedCover
