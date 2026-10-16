/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.OpenCover

/-!
# Crossing paths and the composition-stability boundary

The unit interval is covered by the two proper relative opens `t < 2/3` and `t > 1/3`.
Its endpoint path is in neither strict local inclusion image but is in their multiplicative
closure. The endpoint-in-one-member property shows why composition stability is essential:
it holds on all local images and fails on the composite through `1/2`.

An empty-space client constructs a natural transformation using an empty indexed cover.
The examples use Mathlib's canonical interval, subtype topologies and path-homotopy classes.
-/

@[expose] public section

universe w w'

open CategoryTheory TopologicalSpace
open scoped unitInterval

private def overlapCover : Bool → Opens I
  | false => ⟨{t | (t : ℝ) < (2 / 3 : ℝ)}, isOpen_lt continuous_subtype_val continuous_const⟩
  | true => ⟨{t | (1 / 3 : ℝ) < (t : ℝ)}, isOpen_lt continuous_const continuous_subtype_val⟩

private theorem overlapCover_isOpenCover : IsOpenCover overlapCover := by
  apply IsOpenCover.mk
  apply top_le_iff.mp
  intro t _
  rw [Opens.mem_iSup]
  by_cases ht : (t : ℝ) < (2 / 3 : ℝ)
  · exact ⟨false, ht⟩
  · exact ⟨true, lt_of_lt_of_le (by norm_num) (le_of_not_gt ht)⟩

-- The global property here is not top: the crossing arrow is not a single local image.
-- The positive assertion uses the generated-arrow API, not a chosen partition.
private theorem overlapCover_crossing_not_local_and_generated :
    let L : MorphismProperty (FundamentalGroupoid I) :=
      ⨆ i : Bool, (⊤ : MorphismProperty (FundamentalGroupoid (overlapCover i))).strictMap
        (FundamentalGroupoid.map (ContinuousMap.subtypeVal (overlapCover i : Set I)))
    ¬ L (Path.Homotopic.Quotient.mk Path.id :
      FundamentalGroupoid.mk (0 : I) ⟶ FundamentalGroupoid.mk (1 : I)) ∧
    L.multiplicativeClosure (Path.Homotopic.Quotient.mk Path.id :
      FundamentalGroupoid.mk (0 : I) ⟶ FundamentalGroupoid.mk (1 : I)) := by
  dsimp only
  constructor
  · intro h
    have hEndpoints (i : Bool) :
        (⊤ : MorphismProperty (FundamentalGroupoid (overlapCover i))).strictMap
          (FundamentalGroupoid.map (ContinuousMap.subtypeVal (overlapCover i : Set I))) ≤
        (fun x y _ => x.as ∈ overlapCover i ∧ y.as ∈ overlapCover i) := by
      exact (MorphismProperty.strictMap_le_iff_le_inverseImage
        (FundamentalGroupoid.map (ContinuousMap.subtypeVal (overlapCover i : Set I)))
        (⊤ : MorphismProperty (FundamentalGroupoid (overlapCover i)))
        (fun x y _ => x.as ∈ overlapCover i ∧ y.as ∈ overlapCover i)).mpr (by
          intro x y f _
          exact ⟨x.as.property, y.as.property⟩)
    obtain ⟨i, hi⟩ := (MorphismProperty.iSup_iff _ _).mp h
    have hend := hEndpoints i _ hi
    cases i <;> norm_num [overlapCover] at hend
  · rw [FundamentalGroupoid.multiplicativeClosure_iSup_strictMap_eq_top_of_isOpenCover
      overlapCover_isOpenCover]
    trivial

-- Every local image has endpoints in a common cover member, but composing the two
-- subpaths through 1/2 loses this property. Local truth alone cannot replace stability.
private theorem overlapCover_common_member_not_closed_under_composition :
    let P : MorphismProperty (FundamentalGroupoid I) :=
      fun x y _ => ∃ i : Bool, x.as ∈ overlapCover i ∧ y.as ∈ overlapCover i
    (∀ (i : Bool) ⦃x y : FundamentalGroupoid (overlapCover i)⦄ (f : x ⟶ y),
      P ((FundamentalGroupoid.map (ContinuousMap.subtypeVal (overlapCover i : Set I))).map f)) ∧
    ∃ (m : FundamentalGroupoid I)
      (f : FundamentalGroupoid.mk (0 : I) ⟶ m)
      (g : m ⟶ FundamentalGroupoid.mk (1 : I)),
      (m.as : ℝ) = (1 / 2 : ℝ) ∧ P f ∧ P g ∧ ¬ P (f ≫ g) := by
  dsimp only
  constructor
  · intro i x y f
    exact ⟨i, x.as.property, y.as.property⟩
  · let t : I := ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
    refine ⟨FundamentalGroupoid.mk t,
      Path.Homotopic.Quotient.mk (Path.id.subpath 0 t),
      Path.Homotopic.Quotient.mk (Path.id.subpath t 1), rfl, ?_, ?_, ?_⟩
    · refine ⟨false, ?_, ?_⟩ <;> norm_num [overlapCover, t]
    · refine ⟨true, ?_, ?_⟩ <;> norm_num [overlapCover, t]
    · rintro ⟨i, hi⟩
      cases i <;> norm_num [overlapCover] at hi

/-- Any two functors out of the empty fundamental groupoid admit a natural transformation. -/
theorem FundamentalGroupoidsTest.FundamentalGroupoid.natTrans_nonempty_empty
    {C : Type w} [Category.{w'} C] (F G : FundamentalGroupoid Empty ⥤ C) :
    Nonempty (F ⟶ G) := by
  let U : Empty → Opens Empty := fun i => i.elim
  have hU : IsOpenCover U :=
    IsOpenCover.mk (Subsingleton.elim _ _)
  exact ⟨FundamentalGroupoid.natTransOfIsOpenCover hU (fun x => x.as.elim)
    (fun i => i.elim)⟩
