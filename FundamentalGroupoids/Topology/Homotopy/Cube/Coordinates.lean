/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Cube
public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.Linarith

/-!
# Real coordinates on the complement of a cube boundary

The complement of the coordinate-face boundary consists of cube points whose
coordinates lie strictly between zero and one. With its subtype topology, this
complement is homeomorphic to the product `N → ℝ` for every index type `N`.
No finiteness assumption is needed for these coordinates. In particular, this
is not a description of the ambient topological interior for an infinite cube.

The coordinate convention is increasing: first rescale `(0, 1)` to `(-1, 1)`
by `t ↦ 2 * t - 1`, then use the inverse of `orderIsoIooNegOneOne ℝ`.
For finite `N`, transport of local compactness from `N → ℝ` gives local
compactness of the boundary complement, without declaring a new instance.

## References

* Mathlib's `Mathlib.Order.Interval.Set.IsoIoo` supplies
  `orderIsoIooNegOneOne`, the increasing order isomorphism from `ℝ` to `(-1, 1)`.
* Mathlib supplies the positive affine order isomorphisms, subtype and product
  equivalences, `OrderIso.toHomeomorph`, and `Homeomorph.piCongrRight` used below.
-/

@[expose] public section

noncomputable section

universe u

open scoped unitInterval Topology

/-- The inverse coordinate on the symmetric open unit interval commutes with
negation over an ordered field. -/
theorem orderIsoIooNegOneOne_symm_apply_neg {K : Type u} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (x : Set.Ioo (-1 : K) 1) :
    (orderIsoIooNegOneOne K).symm
        ⟨-(x : K), by constructor <;> linarith [x.property.1, x.property.2]⟩ =
      -(orderIsoIooNegOneOne K).symm x := by
  unfold orderIsoIooNegOneOne
  change -(x : K) / (1 - |-(x : K)|) = -((x : K) / (1 - |(x : K)|))
  simp only [abs_neg, neg_div]

namespace Cube

/-- A cube point avoids the coordinate-face boundary exactly when every real
coordinate lies strictly between zero and one. -/
theorem mem_boundary_compl_iff {N : Type u} {x : I^N} :
    x ∈ (boundary N)ᶜ ↔ ∀ i, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1 := by
  simp only [Set.mem_compl_iff, boundary, Set.mem_ofPred_eq, not_exists, not_or,
    unitInterval.coe_pos, unitInterval.coe_lt_one, unitInterval.pos_iff_ne_zero,
    unitInterval.lt_one_iff_ne_one]

/-- Increasing real coordinates on `(0, 1)`, obtained by positive affine rescaling
and the inverse of Mathlib's `orderIsoIooNegOneOne ℝ`. -/
def openIntervalOrderIsoReal : Set.Ioo (0 : ℝ) 1 ≃o ℝ :=
  let affine : ℝ ≃o ℝ :=
    (OrderIso.mulLeft₀ (2 : ℝ) (by norm_num)).trans (OrderIso.addRight (-1))
  let intervalAffine : Set.Ioo (0 : ℝ) 1 ≃o Set.Ioo (-1 : ℝ) 1 :=
    { toEquiv := affine.toEquiv.subtypeEquiv
        (p := fun t : ℝ => t ∈ Set.Ioo (0 : ℝ) 1)
        (q := fun t : ℝ => t ∈ Set.Ioo (-1 : ℝ) 1) (by
          intro t
          change (0 < t ∧ t < 1) ↔ (-1 < 2 * t + -1 ∧ 2 * t + -1 < 1)
          constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith)
      map_rel_iff' := affine.le_iff_le }
  intervalAffine.trans (orderIsoIooNegOneOne ℝ).symm

/-- The forward coordinate first sends `t` to `2 * t - 1` in `(-1, 1)`. -/
theorem openIntervalOrderIsoReal_apply (x : Set.Ioo (0 : ℝ) 1) :
    openIntervalOrderIsoReal x = (orderIsoIooNegOneOne ℝ).symm
      ⟨2 * (x : ℝ) + -1, by constructor <;> linarith [x.property.1, x.property.2]⟩ :=
  rfl

/-- The inverse coordinate rescales Mathlib's increasing `(-1, 1)` coordinate
back to `(0, 1)`. -/
theorem openIntervalOrderIsoReal_symm_apply_coe (x : ℝ) :
    (openIntervalOrderIsoReal.symm x : ℝ) =
      (2 : ℝ)⁻¹ * ((orderIsoIooNegOneOne ℝ x : ℝ) + 1) := by
  change (2 : ℝ)⁻¹ * ((orderIsoIooNegOneOne ℝ x : ℝ) + -(-1)) = _
  simp

/-- Reversing the open unit interval negates its increasing real coordinate. -/
theorem openIntervalOrderIsoReal_one_sub (x : Set.Ioo (0 : ℝ) 1) :
    openIntervalOrderIsoReal
        ⟨1 - (x : ℝ), Set.Ioo.one_sub_mem x.property⟩ =
      -openIntervalOrderIsoReal x := by
  simp only [openIntervalOrderIsoReal_apply]
  rw [← orderIsoIooNegOneOne_symm_apply_neg]
  apply congrArg (orderIsoIooNegOneOne ℝ).symm
  apply Subtype.ext
  change 2 * (1 - (x : ℝ)) + -1 = -(2 * (x : ℝ) + -1)
  ring

/-- The increasing real coordinate on the open unit interval vanishes exactly at
its midpoint. -/
theorem openIntervalOrderIsoReal_eq_zero_iff (x : Set.Ioo (0 : ℝ) 1) :
    openIntervalOrderIsoReal x = 0 ↔ (x : ℝ) = 1 / 2 := by
  constructor
  · intro hx
    have h : (⟨1 - (x : ℝ), Set.Ioo.one_sub_mem x.property⟩ :
        Set.Ioo (0 : ℝ) 1) = x :=
      openIntervalOrderIsoReal.injective (by
        simp only [openIntervalOrderIsoReal_one_sub, hx, neg_zero])
    have hcoe : 1 - (x : ℝ) = (x : ℝ) := congrArg Subtype.val h
    linarith
  · intro hx
    have h : (⟨1 - (x : ℝ), Set.Ioo.one_sub_mem x.property⟩ :
        Set.Ioo (0 : ℝ) 1) = x := by
      apply Subtype.ext
      change 1 - (x : ℝ) = (x : ℝ)
      linarith
    have hneg := openIntervalOrderIsoReal_one_sub x
    rw [h] at hneg
    linarith

/-- The complement of the coordinate-face boundary of any cube is homeomorphic
to the real product with the same index type. Each coordinate is increasing.
The topology on the complement is the subtype topology, including for infinite
and empty index types. -/
def boundaryComplHomeomorphPi (N : Type u) :
    ((boundary N)ᶜ : Set (I^N)) ≃ₜ (N → ℝ) :=
  let coordinatePi :
      {x : I^N // ∀ i, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1} ≃ₜ
        (N → {t : I // 0 < (t : ℝ) ∧ (t : ℝ) < 1}) :=
    ⟨Equiv.subtypePiEquivPi (β := fun _ : N => I)
        (p := fun (_ : N) (t : I) => 0 < (t : ℝ) ∧ (t : ℝ) < 1),
      by
        change Continuous (fun x : {x : I^N // ∀ i, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1} =>
          fun i => (⟨x.1 i, x.2 i⟩ : {t : I // 0 < (t : ℝ) ∧ (t : ℝ) < 1}))
        exact continuous_pi fun i =>
          ((continuous_apply i).comp continuous_subtype_val).subtype_mk
            (fun x : {x : I^N // ∀ j, 0 < (x j : ℝ) ∧ (x j : ℝ) < 1} => x.2 i),
      by
        change Continuous (fun x : N → {t : I // 0 < (t : ℝ) ∧ (t : ℝ) < 1} =>
          (⟨fun i => (x i).1, fun i => (x i).2⟩ :
            {x : I^N // ∀ i, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1}))
        exact (continuous_pi fun i =>
          continuous_subtype_val.comp (continuous_apply i)).subtype_mk (fun x i => (x i).2)⟩
  let coordinateIoo :
      {t : I // 0 < (t : ℝ) ∧ (t : ℝ) < 1} ≃ₜ Set.Ioo (0 : ℝ) 1 :=
    ⟨Equiv.subtypeSubtypeEquivSubtype
        (p := fun t : ℝ => t ∈ Set.Icc (0 : ℝ) 1)
        (q := fun t : ℝ => t ∈ Set.Ioo (0 : ℝ) 1)
        (fun {t : ℝ} (h : t ∈ Set.Ioo (0 : ℝ) 1) => ⟨h.1.le, h.2.le⟩),
      by
        change Continuous (fun t : {t : I // 0 < (t : ℝ) ∧ (t : ℝ) < 1} =>
          (⟨(t.1 : ℝ), t.2⟩ : Set.Ioo (0 : ℝ) 1))
        exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun t => t.2),
      by
        change Continuous (fun t : Set.Ioo (0 : ℝ) 1 =>
          (⟨⟨t.1, ⟨t.2.1.le, t.2.2.le⟩⟩, t.2⟩ :
            {t : I // 0 < (t : ℝ) ∧ (t : ℝ) < 1}))
        exact (continuous_subtype_val.subtype_mk
          (p := fun t : ℝ => t ∈ Set.Icc (0 : ℝ) 1)
          (fun t : Set.Ioo (0 : ℝ) 1 => ⟨t.2.1.le, t.2.2.le⟩)).subtype_mk (fun t => t.2)⟩
  (Homeomorph.setCongr (show (boundary N)ᶜ =
      {x : I^N | ∀ i, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1} from
    Set.ext fun _ => mem_boundary_compl_iff)).trans <|
      coordinatePi.trans <|
        Homeomorph.piCongrRight fun _ =>
          coordinateIoo.trans openIntervalOrderIsoReal.toHomeomorph

/-- The forward map applies `openIntervalOrderIsoReal` to each real coordinate. -/
@[simp]
theorem boundaryComplHomeomorphPi_apply (N : Type u)
    (x : ((boundary N)ᶜ : Set (I^N))) (i : N) :
    boundaryComplHomeomorphPi N x i = openIntervalOrderIsoReal
      ⟨(x.1 i : ℝ), (mem_boundary_compl_iff.mp x.property) i⟩ :=
  rfl

/-- The inverse map applies the inverse interval coordinate independently in
each factor. -/
@[simp]
theorem boundaryComplHomeomorphPi_symm_apply_coe (N : Type u) (x : N → ℝ) (i : N) :
    (((boundaryComplHomeomorphPi N).symm x).1 i : ℝ) =
      (openIntervalOrderIsoReal.symm (x i) : ℝ) :=
  rfl

/-- For a finite index type, the boundary complement is locally compact, by
transport from the finite real product through `boundaryComplHomeomorphPi`. -/
theorem locallyCompactSpace_boundaryCompl (N : Type u) [Finite N] :
    LocallyCompactSpace ((boundary N)ᶜ : Set (I^N)) :=
  (boundaryComplHomeomorphPi N).locallyCompactSpace_iff.mpr inferInstance

end Cube
