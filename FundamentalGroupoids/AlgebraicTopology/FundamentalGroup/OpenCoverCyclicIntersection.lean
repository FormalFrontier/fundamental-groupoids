/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Killing a generator of an infinite cyclic intersection

Suppose two path-connected open subsets cover a space, their intersection is path
connected with infinite cyclic fundamental group, and the fundamental group of the
second open subset is trivial. A homomorphism from the fundamental group of the
first open subset extends uniquely precisely when it kills the inclusion image of
the intersection's chosen generator.

`FundamentalGroup.homEquivOfIsOpenCoverCyclicIntersection` packages this criterion
as an equivalence whose forward map is restriction along the first inclusion.
The two projection laws identify restriction and extension without unfolding the
equivalence. The target group universe is independent of the space universe.

The chosen generator is the inverse image of `Multiplicative.ofAdd (1 : ℤ)`
under the supplied classification of the intersection group. No geometric
orientation is specified by an arbitrary classification.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–7,
  printed pp. 16–19: group colimits and the based van Kampen theorem.
* `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover` supplies
  the two-open universal property used here.
-/

@[expose] public section

universe u w

open TopologicalSpace

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X]

private theorem restriction_comp_inclusion_eq_one
    (U V : Opens X) (p : ↑(U ⊓ V))
    [Subsingleton (FundamentalGroup V (⟨p.1, p.2.2⟩ : V))]
    (G : Type w) [Group G] (φ : FundamentalGroup X p.1 →* G) :
    (φ.comp (map (X := U) (Y := X) (ContinuousMap.subtypeVal (U : Set X))
        (⟨p.1, p.2.1⟩ : U))).comp
      (map (X := ↥((U : Set X) ∩ (V : Set X))) (Y := U) (ContinuousMap.inclusion
        (s := (U : Set X) ∩ (V : Set X)) (t := (U : Set X))
        Set.inter_subset_left) p) = 1 := by
  rcases p with ⟨z, hzU, hzV⟩
  let pI : ↑(U ⊓ V) := ⟨z, ⟨hzU, hzV⟩⟩
  let pU : U := ⟨z, hzU⟩
  let pV : V := ⟨z, hzV⟩
  let iU : C(↑(U ⊓ V), U) := ContinuousMap.inclusion Set.inter_subset_left
  let iV : C(↑(U ⊓ V), V) := ContinuousMap.inclusion Set.inter_subset_right
  let instV : Subsingleton (FundamentalGroup V (iV pI)) := by
    change Subsingleton (FundamentalGroup V pV)
    infer_instance
  have hsquare :
      (map (ContinuousMap.subtypeVal (U : Set X)) pU).comp (map iU pI) =
        (map (ContinuousMap.subtypeVal (V : Set X)) pV).comp (map iV pI) :=
    (map_comp (ContinuousMap.subtypeVal (U : Set X)) iU pI).symm.trans
      (map_comp (ContinuousMap.subtypeVal (V : Set X)) iV pI)
  apply MonoidHom.ext
  intro a
  change φ (map (ContinuousMap.subtypeVal (U : Set X)) pU (map iU pI a)) = 1
  calc
    _ = φ (map (ContinuousMap.subtypeVal (V : Set X)) pV (map iV pI a)) :=
      congrArg φ (DFunLike.congr_fun hsquare a)
    _ = φ (map (ContinuousMap.subtypeVal (V : Set X)) pV 1) := by
      have htriv : map iV pI a = (1 : FundamentalGroup V (iV pI)) :=
        @Subsingleton.elim (FundamentalGroup V (iV pI)) instV _ _
      exact congrArg
        (fun b : FundamentalGroup V pV =>
          φ (map (ContinuousMap.subtypeVal (V : Set X)) pV b)) htriv
    _ = φ 1 := congrArg φ (map (ContinuousMap.subtypeVal (V : Set X)) pV).map_one
    _ = 1 := φ.map_one

/-- When the second member of a path-connected two-open cover has trivial
fundamental group, homomorphisms from the ambient fundamental group are determined
by their restriction to the first member. No cyclicity assumption is needed. -/
theorem hom_ext_of_isOpenCover_of_subsingleton
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X))
    (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X))
    (p : ↑(U ⊓ V))
    [Subsingleton (FundamentalGroup V (⟨p.1, p.2.2⟩ : V))]
    (G : Type w) [Group G]
    (φ ψ : FundamentalGroup X p.1 →* G)
    (h : φ.comp (map (X := U) (Y := X) (ContinuousMap.subtypeVal (U : Set X))
        (⟨p.1, p.2.1⟩ : U)) =
      ψ.comp (map (X := U) (Y := X) (ContinuousMap.subtypeVal (U : Set X))
        (⟨p.1, p.2.1⟩ : U))) :
    φ = ψ := by
  have hcompat :
      (φ.comp (map (ContinuousMap.subtypeVal (U : Set X))
        (⟨p.1, p.2.1⟩ : U))).comp
          (map (ContinuousMap.inclusion
            (s := (↑(U ⊓ V) : Set X)) (t := (U : Set X))
            Set.inter_subset_left) p) =
        (1 : FundamentalGroup V (⟨p.1, p.2.2⟩ : V) →* G).comp
          (map (ContinuousMap.inclusion
            (s := (↑(U ⊓ V) : Set X)) (t := (V : Set X))
            Set.inter_subset_right) p) :=
    (restriction_comp_inclusion_eq_one U V p G φ).trans (MonoidHom.one_comp _).symm
  obtain ⟨χ, _, huniq⟩ := existsUnique_hom_of_isOpenCover U V hcover hU hV hI p G
    (φ.comp (map (ContinuousMap.subtypeVal (U : Set X)) (⟨p.1, p.2.1⟩ : U)))
    (1 : FundamentalGroup V (⟨p.1, p.2.2⟩ : V) →* G) hcompat
  exact (huniq φ ⟨rfl, Subsingleton.elim _ _⟩).trans
    (huniq ψ ⟨h.symm, Subsingleton.elim _ _⟩).symm

/-- A homomorphism from the first member of a path-connected two-open cover
extends uniquely if and only if it kills the inclusion image of the chosen
infinite cyclic intersection generator. The second member has trivial fundamental
group, and the generator is specified by an isomorphism with `Multiplicative ℤ`.

This is a consequence of the based van Kampen theorem; see May,
*A Concise Course in Algebraic Topology*, Chapter 2, §§6–7. -/
theorem existsUnique_hom_of_isOpenCover_iff_generator_eq_one
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X))
    (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X))
    (p : ↑(U ⊓ V))
    [Subsingleton (FundamentalGroup V (⟨p.1, p.2.2⟩ : V))]
    (ε : FundamentalGroup ↑(U ⊓ V) p ≃* Multiplicative ℤ)
    (G : Type w) [Group G]
    (φU : FundamentalGroup U (⟨p.1, p.2.1⟩ : U) →* G) :
    (φU (map (X := ↥((U : Set X) ∩ (V : Set X))) (Y := U) (ContinuousMap.inclusion
        (s := (U : Set X) ∩ (V : Set X)) (t := (U : Set X))
        Set.inter_subset_left) p
      (ε.symm (Multiplicative.ofAdd (1 : ℤ)))) = 1) ↔
    ∃! φ : FundamentalGroup X p.1 →* G,
      φ.comp (map (X := U) (Y := X) (ContinuousMap.subtypeVal (U : Set X))
        (⟨p.1, p.2.1⟩ : U)) = φU := by
  constructor
  · intro hkill
    let iU : C(↑(U ⊓ V), U) := ContinuousMap.inclusion Set.inter_subset_left
    let iV : C(↑(U ⊓ V), V) := ContinuousMap.inclusion Set.inter_subset_right
    have hgen : (φU.comp (map iU p)).comp ε.symm.toMonoidHom =
        (1 : Multiplicative ℤ →* G) := by
      apply MonoidHom.ext_mint
      change φU (map iU p (ε.symm (Multiplicative.ofAdd (1 : ℤ)))) = 1
      exact hkill
    have hcompat : φU.comp (map iU p) =
        (1 : FundamentalGroup V (⟨p.1, p.2.2⟩ : V) →* G).comp (map iV p) := by
      apply MonoidHom.ext
      intro a
      have ha := DFunLike.congr_fun hgen (ε a)
      change φU (map iU p (ε.symm (ε a))) = 1 at ha
      change φU (map iU p a) = 1
      simpa only [ε.symm_apply_apply] using ha
    obtain ⟨φ, hφ, huniq⟩ := existsUnique_hom_of_isOpenCover
      U V hcover hU hV hI p G φU
      (1 : FundamentalGroup V (⟨p.1, p.2.2⟩ : V) →* G) hcompat
    refine ⟨φ, hφ.1, ?_⟩
    intro ψ hψ
    exact huniq ψ ⟨hψ, Subsingleton.elim _ _⟩
  · rintro ⟨φ, hφ, _⟩
    rw [← hφ]
    exact DFunLike.congr_fun (restriction_comp_inclusion_eq_one U V p G φ)
      (ε.symm (Multiplicative.ofAdd (1 : ℤ)))

/-- Restriction to the first member of a path-connected two-open cover identifies
ambient homomorphisms with the homomorphisms killing the chosen infinite cyclic
intersection generator, when the second member has trivial fundamental group. -/
noncomputable def homEquivOfIsOpenCoverCyclicIntersection
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    (hU : IsPathConnected (U : Set X))
    (hV : IsPathConnected (V : Set X))
    (hI : IsPathConnected (↑(U ⊓ V) : Set X))
    (p : ↑(U ⊓ V))
    [Subsingleton (FundamentalGroup V (⟨p.1, p.2.2⟩ : V))]
    (ε : FundamentalGroup ↑(U ⊓ V) p ≃* Multiplicative ℤ)
    (G : Type w) [Group G] :
    (FundamentalGroup X p.1 →* G) ≃
      {φU : FundamentalGroup U (⟨p.1, p.2.1⟩ : U) →* G //
        φU (map (X := ↥((U : Set X) ∩ (V : Set X))) (Y := U) (ContinuousMap.inclusion
          (s := (U : Set X) ∩ (V : Set X)) (t := (U : Set X))
          Set.inter_subset_left) p
          (ε.symm (Multiplicative.ofAdd (1 : ℤ)))) = 1} := by
  let restrict :
      (FundamentalGroup X p.1 →* G) →
        {φU : FundamentalGroup U (⟨p.1, p.2.1⟩ : U) →* G //
          φU (map (X := ↥((U : Set X) ∩ (V : Set X))) (Y := U) (ContinuousMap.inclusion
            (s := (U : Set X) ∩ (V : Set X)) (t := (U : Set X))
            Set.inter_subset_left) p
            (ε.symm (Multiplicative.ofAdd (1 : ℤ)))) = 1} :=
    fun φ => ⟨φ.comp (map (X := U) (Y := X) (ContinuousMap.subtypeVal (U : Set X))
      (⟨p.1, p.2.1⟩ : U)), by
        exact DFunLike.congr_fun (restriction_comp_inclusion_eq_one U V p G φ)
          (ε.symm (Multiplicative.ofAdd (1 : ℤ)))⟩
  have hrestrict : Function.Bijective restrict := by
    constructor
    · intro φ ψ h
      exact hom_ext_of_isOpenCover_of_subsingleton U V hcover hU hV hI p G
        φ ψ (congrArg Subtype.val h)
    · intro φU
      obtain ⟨φ, hφ, _⟩ :=
        (existsUnique_hom_of_isOpenCover_iff_generator_eq_one
          U V hcover hU hV hI p ε G φU.val).mp φU.property
      exact ⟨φ, Subtype.ext hφ⟩
  exact Equiv.ofBijective restrict hrestrict

variable (U V : Opens X) (hcover : U ⊔ V = ⊤)
  (hU : IsPathConnected (U : Set X))
  (hV : IsPathConnected (V : Set X))
  (hI : IsPathConnected (↑(U ⊓ V) : Set X))
  (p : ↑(U ⊓ V))
  [Subsingleton (FundamentalGroup V (⟨p.1, p.2.2⟩ : V))]
  (ε : FundamentalGroup ↑(U ⊓ V) p ≃* Multiplicative ℤ)
  (G : Type w) [Group G]

/-- The forward equivalence is restriction along the inclusion of the first open. -/
@[simp]
theorem homEquivOfIsOpenCoverCyclicIntersection_apply_val
    (φ : FundamentalGroup X p.1 →* G) :
    (homEquivOfIsOpenCoverCyclicIntersection
      U V hcover hU hV hI p ε G φ).val =
      φ.comp (map (X := U) (Y := X) (ContinuousMap.subtypeVal (U : Set X))
        (⟨p.1, p.2.1⟩ : U)) := by
  change φ.comp (map (ContinuousMap.subtypeVal (U : Set X))
    (⟨p.1, p.2.1⟩ : U)) = _
  rfl

/-- The inverse equivalence extends the supplied homomorphism along the inclusion
of the first open. -/
@[simp]
theorem homEquivOfIsOpenCoverCyclicIntersection_symm_comp
    (φU : {φU : FundamentalGroup U (⟨p.1, p.2.1⟩ : U) →* G //
      φU (map (X := ↥((U : Set X) ∩ (V : Set X))) (Y := U) (ContinuousMap.inclusion
        (s := (U : Set X) ∩ (V : Set X)) (t := (U : Set X))
        Set.inter_subset_left) p
        (ε.symm (Multiplicative.ofAdd (1 : ℤ)))) = 1}) :
    ((homEquivOfIsOpenCoverCyclicIntersection
      U V hcover hU hV hI p ε G).symm φU).comp
        (M := FundamentalGroup U (⟨p.1, p.2.1⟩ : U))
        (map (X := U) (Y := X) (ContinuousMap.subtypeVal (U : Set X))
          (⟨p.1, p.2.1⟩ : U)) = φU.val := by
  have h := congrArg Subtype.val
    ((homEquivOfIsOpenCoverCyclicIntersection
      U V hcover hU hV hI p ε G).apply_symm_apply φU)
  rw [homEquivOfIsOpenCoverCyclicIntersection_apply_val] at h
  exact h

end FundamentalGroup
