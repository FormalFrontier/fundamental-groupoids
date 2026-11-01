/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Affine
public import FundamentalGroupoids.Topology.Homotopy.Cube.Radius

/-!
# Deforming a cylinder onto its bottom and sides

For a finite coordinate type, `Cube.cylinderRetraction` retracts the cylinder
`I × (N → I)` onto its bottom together with its coordinate-face sides.
`Cube.cylinderDeformation` is a homotopy from the identity to this retraction,
relative to the bottom and sides. The construction also includes the empty
coordinate type, when the cylinder retracts onto its bottom point.

The retraction follows rays from the point with time coordinate `2` and all
spatial coordinates `1 / 2`. The deformation uses
`ContinuousMap.HomotopyRel.affine` in the ambient real product space, restricted
to the source cylinder using convexity of the unit interval. No operations on a
target space are involved.

## References

The affine homotopy and interval convex combinations are supplied by Mathlib;
relative affine interpolation is supplied by
`FundamentalGroupoids.Topology.Homotopy.Affine`.
-/

public section

noncomputable section

universe u

open scoped unitInterval

namespace Cube

/-- The bottom and coordinate-face sides of a cylinder, without its top interior. -/
@[expose]
def bottomSides (N : Type u) : Set (I × (N → I)) :=
  {p | p.1 = 0 ∨ p.2 ∈ boundary N}

@[simp]
theorem mem_bottomSides {N : Type u} (p : I × (N → I)) :
    p ∈ bottomSides N ↔ p.1 = 0 ∨ p.2 ∈ boundary N :=
  Iff.rfl

private def cylinderDenom (N : Type u) [Finite N] (p : I × (N → I)) : ℝ :=
  max (2 - (p.1 : ℝ)) (2 * (radius N p.2 : ℝ))

private theorem cylinderDenom_bounds (N : Type u) [Finite N] (p : I × (N → I)) :
    1 ≤ cylinderDenom N p ∧ cylinderDenom N p ≤ 2 := by
  constructor
  · calc
      1 ≤ 2 - (p.1 : ℝ) := by linarith [p.1.property.2]
      _ ≤ cylinderDenom N p := le_max_left _ _
  · apply max_le <;> linarith [p.1.property.1, (radius N p.2).property.2]

private theorem cylinderDenom_pos (N : Type u) [Finite N] (p : I × (N → I)) :
    0 < cylinderDenom N p :=
  lt_of_lt_of_le zero_lt_one (cylinderDenom_bounds N p).1

private def cylinderScale (N : Type u) [Finite N] (p : I × (N → I)) : ℝ :=
  2 / cylinderDenom N p

private theorem cylinderScale_bounds (N : Type u) [Finite N] (p : I × (N → I)) :
    1 ≤ cylinderScale N p ∧ cylinderScale N p ≤ 2 := by
  have hd := cylinderDenom_bounds N p
  have hdpos := cylinderDenom_pos N p
  constructor
  · exact (le_div_iff₀ hdpos).2 (by nlinarith [hd.2])
  · exact (div_le_iff₀ hdpos).2 (by nlinarith [hd.1])

private theorem cylinderScale_nonneg (N : Type u) [Finite N] (p : I × (N → I)) :
    0 ≤ cylinderScale N p :=
  le_trans zero_le_one (cylinderScale_bounds N p).1

private theorem cylinderScale_mul_denom (N : Type u) [Finite N]
    (p : I × (N → I)) : cylinderScale N p * cylinderDenom N p = 2 :=
  div_mul_cancel₀ _ (ne_of_gt (cylinderDenom_pos N p))

private theorem cylinderScale_mul_radius_le (N : Type u) [Finite N]
    (p : I × (N → I)) : cylinderScale N p * (radius N p.2 : ℝ) ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left
    (le_max_right (2 - (p.1 : ℝ)) (2 * (radius N p.2 : ℝ)))
    (cylinderScale_nonneg N p)
  have hd := cylinderScale_mul_denom N p
  change cylinderScale N p * (2 * (radius N p.2 : ℝ)) ≤
    cylinderScale N p * cylinderDenom N p at h
  nlinarith

private theorem cylinderTime_mem (N : Type u) [Finite N] (p : I × (N → I)) :
    2 - cylinderScale N p * (2 - (p.1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hscale := cylinderScale_bounds N p
  have hd := cylinderScale_mul_denom N p
  have hlo := mul_le_mul_of_nonneg_left
    (le_max_left (2 - (p.1 : ℝ)) (2 * (radius N p.2 : ℝ)))
    (cylinderScale_nonneg N p)
  change cylinderScale N p * (2 - (p.1 : ℝ)) ≤
    cylinderScale N p * cylinderDenom N p at hlo
  have ht : 1 ≤ 2 - (p.1 : ℝ) := by linarith [p.1.property.2]
  have hhi := mul_le_mul_of_nonneg_right hscale.1
    (by linarith : 0 ≤ 2 - (p.1 : ℝ))
  constructor <;> nlinarith

private theorem cylinderCoord_mem (N : Type u) [Finite N] (p : I × (N → I)) (i : N) :
    1 / 2 + cylinderScale N p * ((p.2 i : ℝ) - 1 / 2) ∈ Set.Icc (0 : ℝ) 1 := by
  have hz := abs_le.mp (abs_le_radius (N := N) p.2 i)
  have hlo := mul_le_mul_of_nonneg_left hz.1 (cylinderScale_nonneg N p)
  have hhi := mul_le_mul_of_nonneg_left hz.2 (cylinderScale_nonneg N p)
  have hr := cylinderScale_mul_radius_le N p
  constructor <;> nlinarith

private def cylinderPoint (N : Type u) [Finite N] (p : I × (N → I)) : I × (N → I) :=
  (⟨2 - cylinderScale N p * (2 - (p.1 : ℝ)), cylinderTime_mem N p⟩,
    fun i => ⟨1 / 2 + cylinderScale N p * ((p.2 i : ℝ) - 1 / 2),
      cylinderCoord_mem N p i⟩)

private theorem cylinderPoint_mem (N : Type u) [Finite N] (p : I × (N → I)) :
    cylinderPoint N p ∈ bottomSides N := by
  have hd := cylinderScale_mul_denom N p
  rcases le_total (2 - (p.1 : ℝ)) (2 * (radius N p.2 : ℝ)) with h | h
  · right
    have hd' : cylinderDenom N p = 2 * (radius N p.2 : ℝ) := max_eq_right h
    have hr : cylinderScale N p * (radius N p.2 : ℝ) = 1 := by
      rw [hd'] at hd
      nlinarith
    apply (radius_eq_one_iff (N := N) (cylinderPoint N p).2).mp
    apply Subtype.ext
    change (radius N (cylinderPoint N p).2 : ℝ) = (1 : ℝ)
    rw [radius_scale (N := N) p.2 (cylinderPoint N p).2 (cylinderScale N p)
      (cylinderScale_nonneg N p) (fun i => by dsimp [cylinderPoint]; ring)]
    exact hr
  · left
    apply Subtype.ext
    change 2 - cylinderScale N p * (2 - (p.1 : ℝ)) = (0 : ℝ)
    have hd' : cylinderDenom N p = 2 - (p.1 : ℝ) := max_eq_left h
    rw [hd'] at hd
    linarith

private theorem cylinderPoint_eq_of_mem (N : Type u) [Finite N]
    (p : I × (N → I)) (hp : p ∈ bottomSides N) : cylinderPoint N p = p := by
  have hd : cylinderDenom N p = 2 := by
    rcases hp with ht | hz
    · have ht' : (p.1 : ℝ) = 0 := congrArg (fun t : I => (t : ℝ)) ht
      change max (2 - (p.1 : ℝ)) (2 * (radius N p.2 : ℝ)) = 2
      rw [ht', sub_zero]
      exact max_eq_left (by linarith [(radius N p.2).property.2])
    · have hr := (radius_eq_one_iff (N := N) p.2).2 hz
      change max (2 - (p.1 : ℝ)) (2 * (radius N p.2 : ℝ)) = 2
      rw [hr]
      simp only [Set.Icc.coe_one, mul_one]
      exact max_eq_right (by linarith [p.1.property.1])
  have hs : cylinderScale N p = 1 := by simp [cylinderScale, hd]
  apply Prod.ext
  · apply Subtype.ext
    change 2 - cylinderScale N p * (2 - (p.1 : ℝ)) = (p.1 : ℝ)
    rw [hs]
    ring
  · funext i
    apply Subtype.ext
    change 1 / 2 + cylinderScale N p * ((p.2 i : ℝ) - 1 / 2) = (p.2 i : ℝ)
    rw [hs]
    ring

private theorem continuous_cylinderPoint (N : Type u) [Finite N] :
    Continuous (cylinderPoint N) := by
  have hd : Continuous (cylinderDenom N) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).max
      (continuous_const.mul
        ((continuous_subtype_val.comp (radius N).continuous).comp continuous_snd))
  have hs : Continuous (cylinderScale N) :=
    continuous_const.div hd (fun p => ne_of_gt (cylinderDenom_pos N p))
  apply Continuous.prodMk
  · exact (continuous_const.sub
      (hs.mul (continuous_const.sub (continuous_subtype_val.comp continuous_fst)))).subtype_mk _
  · apply continuous_pi
    intro i
    exact (continuous_const.add
      (hs.mul ((continuous_subtype_val.comp
        ((continuous_apply i).comp continuous_snd)).sub continuous_const))).subtype_mk _

/-- The radial retraction of a finite cylinder onto its bottom and sides. -/
def cylinderRetraction (N : Type u) [Finite N] :
    C(I × (N → I), bottomSides N) where
  toFun p := ⟨cylinderPoint N p, cylinderPoint_mem N p⟩
  continuous_toFun := (continuous_cylinderPoint N).subtype_mk _

/-- The time coordinate of the radial cylinder retraction. -/
theorem cylinderRetraction_apply_fst (N : Type u) [Finite N] (p : I × (N → I)) :
    (((cylinderRetraction N p).val.1 : I) : ℝ) =
      2 - (2 / max (2 - (p.1 : ℝ)) (2 * (radius N p.2 : ℝ))) * (2 - (p.1 : ℝ)) := by
  unfold cylinderRetraction cylinderPoint cylinderScale cylinderDenom
  rfl

/-- A spatial coordinate of the radial cylinder retraction. -/
theorem cylinderRetraction_apply_snd (N : Type u) [Finite N] (p : I × (N → I)) (i : N) :
    (((cylinderRetraction N p).val.2 i : I) : ℝ) =
      1 / 2 + (2 / max (2 - (p.1 : ℝ)) (2 * (radius N p.2 : ℝ))) *
        ((p.2 i : ℝ) - 1 / 2) := by
  unfold cylinderRetraction cylinderPoint cylinderScale cylinderDenom
  rfl

/-- The retraction takes values in the bottom and sides. -/
theorem cylinderRetraction_mem (N : Type u) [Finite N] (p : I × (N → I)) :
    (cylinderRetraction N p).val ∈ bottomSides N :=
  (cylinderRetraction N p).property

/-- Every point of the bottom and sides is fixed by the retraction. -/
@[simp]
theorem cylinderRetraction_coe_of_mem (N : Type u) [Finite N]
    (p : I × (N → I)) (hp : p ∈ bottomSides N) :
    (cylinderRetraction N p).val = p :=
  cylinderPoint_eq_of_mem N p hp

/-- Restricting the retraction to the bottom and sides is the identity. -/
@[simp]
theorem cylinderRetraction_subtype (N : Type u) [Finite N] (p : bottomSides N) :
    cylinderRetraction N p.val = p :=
  Subtype.ext (cylinderRetraction_coe_of_mem N p.val p.property)

private def cylinderCoordinates (N : Type u) :
    C(I × (N → I), ℝ × (N → ℝ)) where
  toFun p := ((p.1 : ℝ), fun i => (p.2 i : ℝ))
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_pi fun i => continuous_subtype_val.comp
      ((continuous_apply i).comp continuous_snd))

private theorem cylinderCoordinates_eqOn (N : Type u) [Finite N] :
    Set.EqOn (cylinderCoordinates N)
      ((cylinderCoordinates N).comp
        ((ContinuousMap.subtypeVal (bottomSides N)).comp (cylinderRetraction N)))
      (bottomSides N) := by
  intro p hp
  exact congrArg (cylinderCoordinates N) (cylinderRetraction_coe_of_mem N p hp).symm

private def cylinderAffine (N : Type u) [Finite N] :
    ContinuousMap.HomotopyRel (cylinderCoordinates N)
      ((cylinderCoordinates N).comp
        ((ContinuousMap.subtypeVal (bottomSides N)).comp (cylinderRetraction N)))
      (bottomSides N) :=
  ContinuousMap.HomotopyRel.affine _ _ (cylinderCoordinates_eqOn N)

private theorem cylinderAffine_apply (N : Type u) [Finite N]
    (q : I × (I × (N → I))) :
    cylinderAffine N q = AffineMap.lineMap ((cylinderCoordinates N) q.2)
      ((cylinderCoordinates N) (cylinderRetraction N q.2).val) (q.1 : ℝ) :=
  ContinuousMap.HomotopyRel.affine_apply (cylinderCoordinates N)
    ((cylinderCoordinates N).comp
      ((ContinuousMap.subtypeVal (bottomSides N)).comp (cylinderRetraction N)))
    (cylinderCoordinates_eqOn N) q

private theorem cylinderAffine_fst (N : Type u) [Finite N] (q : I × (I × (N → I))) :
    (cylinderAffine N q).1 = (1 - (q.1 : ℝ)) * (q.2.1 : ℝ) +
      (q.1 : ℝ) * ((cylinderRetraction N q.2).val.1 : ℝ) :=
  congrArg (fun z : ℝ × (N → ℝ) => z.1)
    ((cylinderAffine_apply N q).trans (AffineMap.lineMap_apply_module _ _ _))

private theorem cylinderAffine_snd (N : Type u) [Finite N]
    (q : I × (I × (N → I))) (i : N) :
    (cylinderAffine N q).2 i = (1 - (q.1 : ℝ)) * (q.2.2 i : ℝ) +
      (q.1 : ℝ) * ((cylinderRetraction N q.2).val.2 i : ℝ) :=
  congrArg (fun z : ℝ × (N → ℝ) => z.2 i)
    ((cylinderAffine_apply N q).trans (AffineMap.lineMap_apply_module _ _ _))

/-- Straight-line deformation of a finite cylinder onto its bottom and sides,
fixing that subset throughout. -/
def cylinderDeformation (N : Type u) [Finite N] :
    ContinuousMap.HomotopyRel (ContinuousMap.id (I × (N → I)))
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(bottomSides N, I × (N → I))).comp
        (cylinderRetraction N)) (bottomSides N) where
  toHomotopy :=
    { toFun := fun q =>
        (⟨(cylinderAffine N q).1, by
          rw [cylinderAffine_fst]
          simpa only [Set.Icc.coe_convexComb] using
            (Set.Icc.convexComb q.2.1 (cylinderRetraction N q.2).val.1 q.1).property⟩,
          fun i => ⟨(cylinderAffine N q).2 i, by
            rw [cylinderAffine_snd]
            simpa only [Set.Icc.coe_convexComb] using
              (Set.Icc.convexComb (q.2.2 i)
                ((cylinderRetraction N q.2).val.2 i) q.1).property⟩)
      continuous_toFun := by
        apply Continuous.prodMk
        · exact (continuous_fst.comp (cylinderAffine N).continuous).subtype_mk _
        · exact continuous_pi fun i =>
            ((continuous_apply i).comp
              (continuous_snd.comp (cylinderAffine N).continuous)).subtype_mk _
      map_zero_left := by
        intro p
        apply Prod.ext
        · apply Subtype.ext
          change (cylinderAffine N (0, p)).1 = (p.1 : ℝ)
          rw [(cylinderAffine N).apply_zero]
          rfl
        · funext i
          apply Subtype.ext
          change (cylinderAffine N (0, p)).2 i = (p.2 i : ℝ)
          rw [(cylinderAffine N).apply_zero]
          rfl
      map_one_left := by
        intro p
        apply Prod.ext
        · apply Subtype.ext
          change (cylinderAffine N (1, p)).1 = ((cylinderRetraction N p).val.1 : ℝ)
          rw [(cylinderAffine N).apply_one]
          rfl
        · funext i
          apply Subtype.ext
          change (cylinderAffine N (1, p)).2 i = ((cylinderRetraction N p).val.2 i : ℝ)
          rw [(cylinderAffine N).apply_one]
          rfl }
  prop' := by
    intro t p hp
    apply Prod.ext
    · apply Subtype.ext
      change (cylinderAffine N (t, p)).1 = (p.1 : ℝ)
      rw [(cylinderAffine N).eq_fst t hp]
      rfl
    · funext i
      apply Subtype.ext
      change (cylinderAffine N (t, p)).2 i = (p.2 i : ℝ)
      rw [(cylinderAffine N).eq_fst t hp]
      rfl

/-- The deformation interpolates each interval coordinate by its convex combination. -/
theorem cylinderDeformation_apply (N : Type u) [Finite N]
    (t : I) (p : I × (N → I)) :
    cylinderDeformation N (t, p) =
      (Set.Icc.convexComb p.1 (cylinderRetraction N p).val.1 t,
        fun i => Set.Icc.convexComb (p.2 i) ((cylinderRetraction N p).val.2 i) t) := by
  apply Prod.ext
  · apply Subtype.ext
    change (cylinderAffine N (t, p)).1 =
      (Set.Icc.convexComb p.1 (cylinderRetraction N p).val.1 t : ℝ)
    simpa only [Set.Icc.coe_convexComb] using cylinderAffine_fst N (t, p)
  · funext i
    apply Subtype.ext
    change (cylinderAffine N (t, p)).2 i =
      (Set.Icc.convexComb (p.2 i) ((cylinderRetraction N p).val.2 i) t : ℝ)
    simpa only [Set.Icc.coe_convexComb] using cylinderAffine_snd N (t, p) i

/-- The deformation is stationary on the bottom and sides. -/
@[simp]
theorem cylinderDeformation_apply_of_mem (N : Type u) [Finite N]
    (t : I) (p : I × (N → I)) (hp : p ∈ bottomSides N) :
    cylinderDeformation N (t, p) = p :=
  (cylinderDeformation N).eq_fst t hp

end Cube
