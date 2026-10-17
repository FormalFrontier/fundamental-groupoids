/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# Based equivalences of covering spaces

For two covering maps to a common base, equality of their induced fundamental-group images
at chosen points determines a homeomorphism over the base taking one chosen point to the
other. The images are compared in a single fundamental group, using equality transport for
the second projection. The homeomorphism is characterized among continuous maps by its
projection and chosen-point equations.

The total spaces are path connected, and local path connectedness is required only of the
source total space. There is no connectedness, local connectedness, or separation hypothesis
on the base, and the covering maps need not be surjective: they may have empty fibers away
from the images of their total spaces. This generalizes May's connected, locally
path-connected setting with surjective covers. The supporting surjectivity statement needs
only a nonempty source and a path-connected target total space.

## Limitations

The equivalences here are over a fixed base, not arbitrary homeomorphisms of total spaces.
This is the over-base interpretation of the covering classification in May, Chapter 3 §7;
bare homeomorphism of total spaces does not classify covers. Only the based equal-image
case is considered, not the unbased conjugacy classification.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3 §7, pp. 28–29.
* Mathlib's covering and lifting theory, especially Junyan Xu's formalization in
  `Mathlib.Topology.Homotopy.Lifting`, provides the continuous-map lifting criterion
  and uniqueness used for this construction.
-/

@[expose] public section

universe u v w

namespace IsCoveringMap

variable {E : Type u} {E' : Type v} {X : Type w}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X]
  {p : E → X} {q : E' → X}

/-- A continuous map over a common base between covering spaces is surjective if its source
is nonempty and its target total space is path connected. No local path connectedness or
connectedness assumption on the source is needed. This is the surjectivity part of the
cover-map discussion in May, Chapter 3 §7, p. 29. -/
theorem surjective_of_comp_eq (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    [Nonempty E] [PathConnectedSpace E'] (g : C(E, E')) (h : q ∘ g = p) :
    Function.Surjective g := by
  obtain ⟨a⟩ := ‹Nonempty E›
  intro y
  let γ := PathConnectedSpace.somePath (g a) y
  obtain ⟨Γ, hΓ, hΓ₀⟩ := covp.exists_path_lifts (γ.map covq.continuous) a
    (by simpa using congr_fun h a)
  have hlifts : q ∘ (g ∘ Γ) = q ∘ γ := by
    rw [← Function.comp_assoc, h]
    exact hΓ
  have heq : g ∘ Γ = γ :=
    covq.eq_of_comp_eq (g.continuous.comp Γ.continuous) γ.continuous hlifts 0
      (by simp [hΓ₀])
  exact ⟨Γ 1, (congr_fun heq 1).trans γ.target⟩

/-- The based homeomorphism over `X` associated to equal images of fundamental groups.
Both ranges in `hπ` are subgroups of `FundamentalGroup X (p e)`; the second uses transport
along `he.symm : q e' = p e`. Local path connectedness of `E'` is not an input.

This constructs the based equal-image case of May, Chapter 3 §7, p. 29, interpreted as an
isomorphism of covers over the fixed base, not merely a homeomorphism of total spaces. -/
noncomputable def homeomorphOfRangeEq (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] [PathConnectedSpace E']
    (e : E) (e' : E') (he : p e = q e')
    (hπ : (FundamentalGroup.map ⟨p, covp.continuous⟩ e).range =
      (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ he.symm).range) : E ≃ₜ E' := by
  let g := Classical.choose (covq.existsUnique_continuousMap_lifts_of_range_le he.symm hπ.le)
  have hg : g e = e' ∧ q ∘ g = p := (Classical.choose_spec
    (covq.existsUnique_continuousMap_lifts_of_range_le he.symm hπ.le)).1
  have hgSurj := covp.surjective_of_comp_eq covq g hg.2
  have hgLocal : IsLocalHomeomorph g :=
    IsLocalHomeomorph.of_comp (hg.2 ▸ covp.isLocalHomeomorph)
      covq.isLocalHomeomorph g.continuous
  letI : LocallyPathConnectedSpace E' :=
    (hgLocal.isOpenMap.isQuotientMap g.continuous hgSurj).locallyPathConnectedSpace
  -- Transport the image equality to `q e'`, cancelling the two endpoint casts.
  have hπ' : (FundamentalGroup.map ⟨q, covq.continuous⟩ e').range =
      (FundamentalGroup.mapOfEq ⟨p, covp.continuous⟩ he).range := by
    have cancel (γ : FundamentalGroup E e) (γ' : FundamentalGroup E' e')
        (h : FundamentalGroup.map ⟨p, covp.continuous⟩ e γ =
          FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ he.symm γ') :
        FundamentalGroup.mapOfEq ⟨p, covp.continuous⟩ he γ =
          FundamentalGroup.map ⟨q, covq.continuous⟩ e' γ' := by
      rw [FundamentalGroup.mapOfEq_apply] at h ⊢
      change Path.Homotopic.Quotient.cast
        (FundamentalGroup.map ⟨p, covp.continuous⟩ e γ) he.symm he.symm = _
      rw [h]
      simp only [Path.Homotopic.Quotient.cast_cast,
        Path.Homotopic.Quotient.cast_rfl_rfl, FundamentalGroup.map_apply]
    apply le_antisymm
    · rintro _ ⟨γ', rfl⟩
      obtain ⟨γ, hγ⟩ := hπ.symm.le ⟨γ', rfl⟩
      exact ⟨γ, cancel γ γ' hγ⟩
    · rintro _ ⟨γ, rfl⟩
      obtain ⟨γ', hγ'⟩ := hπ.le ⟨γ, rfl⟩
      exact ⟨γ', (cancel γ γ' hγ'.symm).symm⟩
  let r := Classical.choose (covp.existsUnique_continuousMap_lifts_of_range_le he hπ'.le)
  have hr : r e' = e ∧ p ∘ r = q := (Classical.choose_spec
    (covp.existsUnique_continuousMap_lifts_of_range_le he hπ'.le)).1
  have hrg : r ∘ g = id := covp.eq_of_comp_eq (r.continuous.comp g.continuous)
    continuous_id (by rw [← Function.comp_assoc, hr.2, hg.2]; rfl) e
    (by change r (g e) = e; rw [hg.1, hr.1])
  have hgr : g ∘ r = id := covq.eq_of_comp_eq (g.continuous.comp r.continuous)
    continuous_id (by rw [← Function.comp_assoc, hg.2, hr.2]; rfl) e'
    (by change g (r e') = e'; rw [hr.1, hg.1])
  exact
    { toFun := g
      invFun := r
      left_inv := congr_fun hrg
      right_inv := congr_fun hgr
      continuous_toFun := g.continuous
      continuous_invFun := r.continuous }

variable (covp : IsCoveringMap p) (covq : IsCoveringMap q)
  [PathConnectedSpace E] [LocallyPathConnectedSpace E] [PathConnectedSpace E']
  (e : E) (e' : E') (he : p e = q e')
  (hπ : (FundamentalGroup.map ⟨p, covp.continuous⟩ e).range =
    (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ he.symm).range)

private theorem homeomorphOfRangeEq_spec :
    covp.homeomorphOfRangeEq covq e e' he hπ e = e' ∧
      q ∘ covp.homeomorphOfRangeEq covq e e' he hπ = p := by
  exact (Classical.choose_spec
    (covq.existsUnique_continuousMap_lifts_of_range_le he.symm hπ.le)).1

/-- The based equivalence sends the selected source point to the selected target point. -/
@[simp] theorem homeomorphOfRangeEq_apply_basepoint :
    covp.homeomorphOfRangeEq covq e e' he hπ e = e' :=
  (homeomorphOfRangeEq_spec covp covq e e' he hπ).1

/-- The based equivalence commutes with the projections to the common base. -/
theorem homeomorphOfRangeEq_apply_proj (z : E) :
    q (covp.homeomorphOfRangeEq covq e e' he hπ z) = p z :=
  congr_fun (homeomorphOfRangeEq_spec covp covq e e' he hπ).2 z

/-- The inverse based equivalence sends the selected target point to the selected source
point. -/
@[simp] theorem homeomorphOfRangeEq_symm_apply_basepoint :
    (covp.homeomorphOfRangeEq covq e e' he hπ).symm e' = e := by
  apply (covp.homeomorphOfRangeEq covq e e' he hπ).injective
  rw [Homeomorph.apply_symm_apply, homeomorphOfRangeEq_apply_basepoint]

/-- The inverse based equivalence also commutes with the projections to the common base. -/
theorem homeomorphOfRangeEq_symm_apply_proj (z : E') :
    p ((covp.homeomorphOfRangeEq covq e e' he hπ).symm z) = q z := by
  rw [← homeomorphOfRangeEq_apply_proj covp covq e e' he hπ,
    Homeomorph.apply_symm_apply]

/-- A continuous map is the based equivalence exactly when it commutes with the projections
and sends the chosen point to the chosen point. Thus the construction is independent of any
choices of lifts. -/
theorem homeomorphOfRangeEq_eq_iff (g : C(E, E')) :
    (covp.homeomorphOfRangeEq covq e e' he hπ : C(E, E')) = g ↔
      q ∘ g = p ∧ g e = e' := by
  constructor
  · rintro rfl
    exact ⟨(homeomorphOfRangeEq_spec covp covq e e' he hπ).2,
      homeomorphOfRangeEq_apply_basepoint covp covq e e' he hπ⟩
  · rintro ⟨hg, hge⟩
    apply DFunLike.ext'
    exact covq.eq_of_comp_eq (covp.homeomorphOfRangeEq covq e e' he hπ).continuous
      g.continuous ((homeomorphOfRangeEq_spec covp covq e e' he hπ).2.trans hg.symm)
      e ((homeomorphOfRangeEq_apply_basepoint covp covq e e' he hπ).trans hge.symm)

end IsCoveringMap
