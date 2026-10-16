/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.OpenCoverDescent
import Mathlib.CategoryTheory.PEmpty
import Mathlib.Tactic

/-!
# Open-cover descent on a mixed arrow and on the empty space

The real line has the proper cover `(-∞, 1), (-1, ∞)`. Two explicit local paths
compose to an arrow from `-2` to `2`, whose endpoints are not together in either chart.
The local functors take values in `Type w`, not a groupoid: each object is a lifted
copy of the integers, and an arrow acts by an endpoint-potential translation.
Their descended mixed arrow is translation by one, not the identity.

The empty-space client uses an empty index and an arbitrary target category, including
the empty category. Colimit clients use `IsColimit.desc`, `fac` and `uniq` directly.
-/

@[expose] public section

noncomputable section

universe w w'

open CategoryTheory CategoryTheory.Limits TopologicalSpace FundamentalGroupoid
open scoped unitInterval

namespace FundamentalGroupoid

private def realCover : Bool → Opens ℝ
  | false => ⟨Set.Iio 1, isOpen_Iio⟩
  | true => ⟨Set.Ioi (-1), isOpen_Ioi⟩

private theorem realCover_isOpenCover : IsOpenCover realCover := by
  apply top_unique
  intro x _
  apply Opens.mem_iSup.mpr
  by_cases hx : x < 1
  · exact ⟨false, hx⟩
  · exact ⟨true, by change (-1 : ℝ) < x; linarith⟩

private theorem realCover_proper_and_mixed_endpoints :
    (∀ i, realCover i ≠ ⊤) ∧ ¬ ∃ i, (-2 : ℝ) ∈ realCover i ∧ (2 : ℝ) ∈ realCover i := by
  constructor
  · intro i hi
    cases i with
    | false =>
      have h := congrArg (fun V : Opens ℝ => (2 : ℝ) ∈ V) hi
      norm_num [realCover] at h
    | true =>
      have h := congrArg (fun V : Opens ℝ => (-2 : ℝ) ∈ V) hi
      norm_num [realCover] at h
  · rintro ⟨i, hi⟩
    cases i <;> norm_num [realCover] at hi

private def leftPoint : realCover false := ⟨-2, by norm_num [realCover]⟩
private def leftMiddle : realCover false := ⟨0, by norm_num [realCover]⟩
private def rightMiddle : realCover true := ⟨0, by norm_num [realCover]⟩
private def rightPoint : realCover true := ⟨2, by norm_num [realCover]⟩

private def leftPath : Path leftPoint leftMiddle where
  toFun t := ⟨-2 + 2 * (t : ℝ), by
    change -2 + 2 * (t : ℝ) < 1
    have ht := unitInterval.le_one t
    linarith⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; norm_num [leftPoint]
  target' := by apply Subtype.ext; norm_num [leftMiddle]

private def rightPath : Path rightMiddle rightPoint where
  toFun t := ⟨2 * (t : ℝ), by
    change (-1 : ℝ) < 2 * (t : ℝ)
    have ht := unitInterval.nonneg t
    linarith⟩
  continuous_toFun := by fun_prop
  source' := by apply Subtype.ext; norm_num [rightMiddle]
  target' := by apply Subtype.ext; norm_num [rightPoint]

private def potential (x : ℝ) : ℤ := if x ≤ 0 then 0 else 1

-- Only local functors are prescribed; no global descent functor is an input.
private def localTranslations (i : Bool) : FundamentalGroupoid (realCover i) ⥤ Type w where
  obj _ := ULift.{w} ℤ
  map {a b} _ := ↾fun n =>
    ULift.up (n.down + potential b.as.1 - potential a.as.1)
  map_id := by
    intro a
    apply ConcreteCategory.hom_ext
    intro n
    apply ULift.ext
    simp
  map_comp := by
    intro a b c f g
    apply ConcreteCategory.hom_ext
    intro n
    apply ULift.ext
    change n.down + potential c.as.1 - potential a.as.1 =
      (n.down + potential b.as.1 - potential a.as.1) + potential c.as.1 - potential b.as.1
    omega

private theorem localTranslations_compatible (i j : Bool) :
    (openCoverDiagram realCover).map (Pairwise.Hom.left i j) ⋙ localTranslations.{w} i =
      (openCoverDiagram realCover).map (Pairwise.Hom.right i j) ⋙ localTranslations.{w} j := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  rfl

private def mixedArrow : mk (-2 : ℝ) ⟶ mk (2 : ℝ) :=
  (map (ContinuousMap.subtypeVal (realCover false : Set ℝ))).map
      (fromPath (Path.Homotopic.Quotient.mk leftPath)) ≫
    (map (ContinuousMap.subtypeVal (realCover true : Set ℝ))).map
      (fromPath (Path.Homotopic.Quotient.mk rightPath))

private def realDesc : FundamentalGroupoid ℝ ⥤ Type w :=
  descOfIsOpenCover realCover_isOpenCover localTranslations.{w} localTranslations_compatible

-- Keep the constant local object explicit in transport types, without unfolding the functor.
private theorem realDesc_obj (i : Bool) (x : ℝ) (hx : x ∈ realCover i) :
    realDesc.{w}.obj (mk x) = ULift.{w} ℤ :=
  descOfIsOpenCover_obj realCover_isOpenCover localTranslations.{w}
    localTranslations_compatible i x hx

private theorem realDesc_map (i : Bool) {a b : FundamentalGroupoid (realCover i)}
    (f : a ⟶ b) :
    realDesc.{w}.map ((map (ContinuousMap.subtypeVal (realCover i : Set ℝ))).map f) =
      eqToHom (realDesc_obj i a.as.1 a.as.2) ≫
        (↾fun n : ULift.{w} ℤ =>
          ULift.up (n.down + potential b.as.1 - potential a.as.1)) ≫
          eqToHom (realDesc_obj i b.as.1 b.as.2).symm :=
  descOfIsOpenCover_map realCover_isOpenCover localTranslations.{w}
    localTranslations_compatible i f

private def transportedMixed : ULift.{w} ℤ ⟶ ULift.{w} ℤ :=
  eqToHom (realDesc_obj false (-2) leftPoint.2).symm ≫
    realDesc.map mixedArrow ≫ eqToHom (realDesc_obj true 2 rightPoint.2)

private theorem transportedMixed_eq_translation :
    transportedMixed.{w} = ↾(fun n : ULift.{w} ℤ => ULift.up (n.down + 1)) := by
  -- Infer each included arrow before fixing the three ambient endpoints.
  let leftIncluded := (map (ContinuousMap.subtypeVal (realCover false : Set ℝ))).map
    (fromPath (Path.Homotopic.Quotient.mk leftPath))
  let rightIncluded := (map (ContinuousMap.subtypeVal (realCover true : Set ℝ))).map
    (fromPath (Path.Homotopic.Quotient.mk rightPath))
  let leftArrow : mk (-2 : ℝ) ⟶ mk (0 : ℝ) := leftIncluded
  let rightArrow : mk (0 : ℝ) ⟶ mk (2 : ℝ) := rightIncluded
  have left_map := realDesc_map.{w} false (fromPath (Path.Homotopic.Quotient.mk leftPath))
  change realDesc.{w}.map leftArrow = _ at left_map
  have right_map := realDesc_map.{w} true (fromPath (Path.Homotopic.Quotient.mk rightPath))
  change realDesc.{w}.map rightArrow = _ at right_map
  have hcomp := realDesc.{w}.map_comp leftArrow rightArrow
  change realDesc.{w}.map mixedArrow = _ at hcomp
  unfold transportedMixed
  rw [hcomp, left_map, right_map]
  simp only [leftPoint, leftMiddle, rightMiddle, rightPoint]
  have cancel {A B : Type w} (p : A = B) (x : B) :
      (eqToHom p) ((eqToHom p.symm) x) = x := by
    simpa only [CategoryTheory.comp_apply, eqToHom_refl, CategoryTheory.id_apply] using
      ConcreteCategory.congr_hom (eqToHom_trans p.symm p) x
  apply ConcreteCategory.hom_ext
  intro n
  apply ULift.ext
  norm_num [cancel, potential, leftPoint, leftMiddle, rightMiddle, rightPoint]
  let pneg := realDesc_obj.{w} false (-2) leftPoint.2
  let pzero := realDesc_obj.{w} false 0 leftMiddle.2
  change (eqToHom pzero) ((eqToHom pzero.symm)
    (ULift.up (((eqToHom pneg) ((eqToHom pneg.symm) n)).down))) = n
  simp only [cancel]

-- An explicit proper-cover client in a non-groupoid category with object universe w+1
-- and hom universe w; the mixed arrow is nonidentity even though neither chart contains it.
private theorem proper_cover_nonidentity_mixed_translation :
    (∀ i, realCover i ≠ ⊤) ∧
      (¬ ∃ i, (-2 : ℝ) ∈ realCover i ∧ (2 : ℝ) ∈ realCover i) ∧
      transportedMixed.{w} ≠ 𝟙 (ULift.{w} ℤ) := by
  refine ⟨realCover_proper_and_mixed_endpoints.1,
    realCover_proper_and_mixed_endpoints.2, ?_⟩
  intro h
  have he := congrArg (fun f : ULift.{w} ℤ ⟶ ULift.{w} ℤ => (f (ULift.up 0)).down) h
  rw [transportedMixed_eq_translation] at he
  norm_num at he

private def emptyCover.{u, v} : PEmpty.{v + 1} → Opens PEmpty.{u + 1} := PEmpty.elim

universe u v

private theorem emptyCover_isOpenCover : IsOpenCover emptyCover.{u, v} := by
  apply top_unique
  intro x
  exact x.elim

private def emptyLocal (D : Type w) [Category.{w'} D] :
    ∀ i, FundamentalGroupoid (emptyCover.{u, v} i) ⥤ D := fun i => i.elim

private theorem emptyLocal_compatible (D : Type w) [Category.{w'} D]
    (i j : PEmpty.{v + 1}) :
    (openCoverDiagram emptyCover.{u, v}).map (Pairwise.Hom.left i j) ⋙ emptyLocal D i =
      (openCoverDiagram emptyCover.{u, v}).map (Pairwise.Hom.right i j) ⋙ emptyLocal D j :=
  i.elim

-- Independent source/index/target object/target hom sizes, without choosing a target object.
private theorem empty_descent (D : Type w) [Category.{w'} D] :
    descOfIsOpenCover (U := emptyCover.{u, v}) emptyCover_isOpenCover
        (emptyLocal D) (emptyLocal_compatible D) =
      functorOfIsEmpty (FundamentalGroupoid PEmpty.{u + 1}) D := by
  refine CategoryTheory.Functor.ext (fun x => x.as.elim) ?_
  intro x y f
  exact x.as.elim

private theorem empty_descent_to_empty :
    descOfIsOpenCover (U := emptyCover.{u, v}) emptyCover_isOpenCover
        (emptyLocal (Discrete PEmpty.{w + 1})) (emptyLocal_compatible (Discrete PEmpty.{w + 1})) =
      functorOfIsEmpty (FundamentalGroupoid PEmpty.{u + 1}) (Discrete PEmpty.{w + 1}) :=
  empty_descent _

-- The empty diagram has the empty fundamental groupoid as its vertex in both categories.
-- These clients use equality uniqueness, rather than equivalences of category objects.
private theorem empty_groupoid_colimit_desc_unique :
    (isColimitOpenCoverCocone emptyCover_isOpenCover).desc
        (openCoverCocone emptyCover.{u, v}) = 𝟭 (FundamentalGroupoid PEmpty.{u + 1}) := by
  apply ((isColimitOpenCoverCocone emptyCover_isOpenCover).uniq _ _ ?_).symm
  intro j
  cases j with
  | single i => exact i.elim
  | pair i j => exact i.elim

private theorem empty_category_colimit_fac_unique :
    let h := isColimitOpenCoverCatCocone (U := emptyCover.{u, v}) emptyCover_isOpenCover
    let s := openCoverCatCocone emptyCover.{u, v}
    (∀ j, s.ι.app j ≫ h.desc s = s.ι.app j) ∧ h.desc s = 𝟙 s.pt := by
  dsimp only
  refine ⟨(isColimitOpenCoverCatCocone emptyCover_isOpenCover).fac _, ?_⟩
  apply ((isColimitOpenCoverCatCocone emptyCover_isOpenCover).uniq _ _ ?_).symm
  intro j
  cases j with
  | single i => exact i.elim
  | pair i j => exact i.elim

end FundamentalGroupoid
