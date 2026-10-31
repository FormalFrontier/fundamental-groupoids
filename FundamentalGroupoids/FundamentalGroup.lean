/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Induced maps, homotopy retractions and change of basepoint

The homomorphism `FundamentalGroup.map` preserves identity maps and composition.
It commutes with `FundamentalGroup.fundamentalGroupMulEquivOfPath`, and a homotopy
compares its two induced maps by transport along the basepoint's track. Both
comparisons are available pointwise and as equalities of monoid homomorphisms.
No connectedness or basedness hypothesis is needed. Loop classes are the identity
exactly for nullhomotopic loops; trivial images of induced homomorphisms are
characterized by ambient nullhomotopies, also for arbitrary subspace inclusions.

A homotopy retraction gives an explicit splitting of the induced fundamental-group
homomorphism, using the moving basepoint track of the homotopy. The induced map
is therefore injective. Nontriviality of the source vertex group and triviality of the target
vertex group obstruct such a homotopy retraction.

The proofs restrict fundamental-groupoid functors to endomorphisms and use
Mathlib's functoriality of conjugation and naturality of the transformation
associated to a homotopy. Transport along `a : Path x x'` traverses `a.symm`,
then the loop, then `a`; group multiplication traverses the right factor first.

The loop-class and image characterizations use Mathlib's path-homotopy quotient
and subgroup-range APIs. Simple connectivity is characterized by path connectedness
and subsingletonness of the fundamental group at a given point.

## References

* Mathlib's `Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup`
  and `Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic` provide the induced
  homomorphisms and the functoriality of the fundamental groupoid.
* Mathlib's simple-connectivity API, by Praneeth Kolichala and contributors,
  supplies the canonical class and the all-point null-loop characterization.
* `Mathlib.Topology.Homotopy.Path` and `Mathlib.Algebra.Group.Subgroup.Ker`
  provide the loop quotient and the trivial-range criterion.
* `Mathlib.CategoryTheory.Endomorphism` and `Mathlib.CategoryTheory.EqToHom`
  provide restriction to endomorphisms and comparison of equal functors on morphisms.
* `Mathlib.CategoryTheory.Conj`, `Mathlib.CategoryTheory.NatIso` and
  `Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps` provide functorial
  conjugation and the natural transformation associated to a homotopy.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 1, §§3–4,
  pp. 6–8, for change of basepoint and the homotopy comparison convention; §6,
  p. 10, for the strict-retraction obstruction extended here to homotopy retractions;
  Chapter 2, §8, p. 20, for the fundamental-group characterization of simple connectivity.
-/

@[expose] public section

universe u v w

namespace FundamentalGroup

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A loop represents the identity in the fundamental group exactly when it is
nullhomotopic. -/
theorem mk_eq_one_iff {x : X} (γ : Path x x) :
    (Path.Homotopic.Quotient.mk γ : FundamentalGroup X x) = (1 : FundamentalGroup X x) ↔
      γ.Homotopic (Path.refl x) := by
  rw [one_def, ← Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.eq]

/-- A space is simply connected exactly when it is path connected and its fundamental
group at the given point is subsingleton. No separate nonemptiness assumption is needed.

This is the based fundamental-group characterization of simple connectivity in
J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §8, p. 20. -/
theorem simplyConnectedSpace_iff (p : X) :
    SimplyConnectedSpace X ↔ PathConnectedSpace X ∧ Subsingleton (FundamentalGroup X p) := by
  constructor
  · intro h
    let := h
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hpc, hπ⟩
    let := hpc
    let := hπ
    apply simply_connected_iff_loops_nullhomotopic.mpr
    refine ⟨hpc, ?_⟩
    intro x γ
    let : Subsingleton (FundamentalGroup X x) :=
      (fundamentalGroupMulEquivOfPathConnected p x).symm.toEquiv.subsingleton
    exact (mk_eq_one_iff γ).mp (Subsingleton.elim (α := FundamentalGroup X x) _ _)

/-- The image of the induced fundamental-group homomorphism is trivial exactly
when every based loop maps to a nullhomotopic loop. -/
theorem range_map_eq_bot_iff (f : C(X, Y)) (x : X) :
    (map f x).range = ⊥ ↔
      ∀ γ : Path x x, (γ.map f.continuous).Homotopic (Path.refl (f x)) := by
  rw [MonoidHom.range_eq_bot_iff]
  constructor
  · intro h γ
    have hγ :
        (Path.Homotopic.Quotient.mk (γ.map f.continuous) : FundamentalGroup Y (f x)) =
          (1 : FundamentalGroup Y (f x)) := by
      have hγ := congrArg
        (fun k : FundamentalGroup X x →* FundamentalGroup Y (f x) =>
          k (Path.Homotopic.Quotient.mk γ)) h
      simpa only [map_apply, ← Path.Homotopic.Quotient.mk_map,
        MonoidHom.one_apply] using hγ
    exact (mk_eq_one_iff (γ.map f.continuous)).mp hγ
  · intro h
    apply MonoidHom.ext
    intro q
    induction q using Path.Homotopic.Quotient.ind with
    | mk γ =>
      have hγ :
          (Path.Homotopic.Quotient.mk (γ.map f.continuous) : FundamentalGroup Y (f x)) =
            (1 : FundamentalGroup Y (f x)) :=
        (mk_eq_one_iff (γ.map f.continuous)).mpr (h γ)
      simpa only [map_apply, ← Path.Homotopic.Quotient.mk_map,
        MonoidHom.one_apply] using hγ

/-- The inclusion of a subspace has trivial image on the fundamental group
at `⟨x, hx⟩` exactly when all ambient loops at `x` with range in that subspace
are nullhomotopic in `X`. The subspace need not be connected or open. -/
theorem range_map_subtypeVal_eq_bot_iff {U : Set X} {x : X} (hx : x ∈ U) :
    (map (ContinuousMap.subtypeVal U) ⟨x, hx⟩).range = ⊥ ↔
      ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x) := by
  rw [range_map_eq_bot_iff]
  dsimp only [ContinuousMap.subtypeVal]
  constructor
  · intro h γ hγ
    let δ : Path (⟨x, hx⟩ : U) ⟨x, hx⟩ :=
      { toFun := fun t => ⟨γ t, hγ ⟨t, rfl⟩⟩
        continuous_toFun := γ.continuous.subtype_mk _
        source' := Subtype.ext γ.source
        target' := Subtype.ext γ.target }
    have hδ : δ.map continuous_subtype_val = γ := by
      ext t
      rfl
    rw [← hδ]
    exact h δ
  · intro h δ
    exact h (δ.map continuous_subtype_val) (by
      rintro y ⟨t, rfl⟩
      exact (δ t).property)

/-- The identity map induces the identity homomorphism on the fundamental group. -/
@[simp]
theorem map_id (p : X) :
    map (ContinuousMap.id X) p = MonoidHom.id (FundamentalGroup X p) :=
  MonoidHom.ext fun γ => eq_of_heq
    (CategoryTheory.Functor.hcongr_hom (FundamentalGroupoid.map_id (X := X)) γ)

/-- Composition of continuous maps induces composition of fundamental-group homomorphisms,
with the intermediate basepoint given by the image under the first map. -/
@[simp]
theorem map_comp (g : C(Y, Z)) (f : C(X, Y)) (p : X) :
    map (g.comp f) p = (map g (f p)).comp (map f p) :=
  MonoidHom.ext fun γ => eq_of_heq
    (CategoryTheory.Functor.hcongr_hom (FundamentalGroupoid.map_comp g f) γ)

open CategoryTheory

private theorem map_pathIso (f : C(X, Y)) {x x' : X} (a : Path x x') :
    (FundamentalGroupoid.map f).mapIso
        ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
          (FundamentalGroupoid.mk x')).symm (Path.Homotopic.Quotient.mk a)) =
      (Groupoid.isoEquivHom (FundamentalGroupoid.mk (f x))
        (FundamentalGroupoid.mk (f x'))).symm
          (Path.Homotopic.Quotient.mk (a.map f.continuous)) := by
  apply Iso.ext
  rfl

/-- Mapping a loop commutes with change of basepoint along a path. -/
theorem map_fundamentalGroupMulEquivOfPath (f : C(X, Y)) {x x' : X}
    (a : Path x x') (γ : FundamentalGroup X x) :
    map f x' (fundamentalGroupMulEquivOfPath a γ) =
      fundamentalGroupMulEquivOfPath (a.map f.continuous) (map f x γ) := by
  calc
    _ = ((FundamentalGroupoid.map f).mapIso
        ((Groupoid.isoEquivHom (FundamentalGroupoid.mk x)
          (FundamentalGroupoid.mk x')).symm
            (Path.Homotopic.Quotient.mk a))).conj (map f x γ) :=
      (FundamentalGroupoid.map f).map_conj _ γ
    _ = _ := by
      rw [map_pathIso, fundamentalGroupMulEquivOfPath]
      rfl

/-- The change-of-basepoint square for a continuous map, as an equality of homomorphisms. -/
theorem map_comp_fundamentalGroupMulEquivOfPath (f : C(X, Y)) {x x' : X}
    (a : Path x x') :
    (map f x').comp (fundamentalGroupMulEquivOfPath a).toMonoidHom =
      (fundamentalGroupMulEquivOfPath (a.map f.continuous)).toMonoidHom.comp (map f x) :=
  MonoidHom.ext fun γ => map_fundamentalGroupMulEquivOfPath f a γ

/-- A homotopy compares the induced maps by change of basepoint along its component path.
This is the homotopy comparison of May, Chapter 1, §4, with time in the first coordinate. -/
theorem fundamentalGroupMulEquivOfPath_map_of_homotopy {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) (γ : FundamentalGroup X x) :
    fundamentalGroupMulEquivOfPath (H.evalAt x) (map f x γ) = map g x γ := by
  change Groupoid.inv ((FundamentalGroupoidFunctor.homotopicMapsNatIso H).app
      (FundamentalGroupoid.mk x)) ≫ (FundamentalGroupoid.map f).map γ ≫
        (FundamentalGroupoidFunctor.homotopicMapsNatIso H).app (FundamentalGroupoid.mk x) =
      (FundamentalGroupoid.map g).map γ
  rw [Groupoid.inv_eq_inv]
  exact NatIso.naturality_1' (FundamentalGroupoidFunctor.homotopicMapsNatIso H) γ

/-- The homotopy comparison as an equality of fundamental-group homomorphisms. -/
theorem fundamentalGroupMulEquivOfPath_comp_map_of_homotopy {f g : C(X, Y)}
    (H : ContinuousMap.Homotopy f g) (x : X) :
    (fundamentalGroupMulEquivOfPath (H.evalAt x)).toMonoidHom.comp (map f x) = map g x :=
  MonoidHom.ext fun γ => fundamentalGroupMulEquivOfPath_map_of_homotopy H x γ

/-- The fundamental-group retraction induced by a homotopy `f ∘ g ∼ id`.
It first maps by `f`, then changes basepoint along the track `H.evalAt x`.
The track need not be constant. This is a moving-basepoint extension of May's
strict-retraction argument (Chapter 1, §6, p. 10). -/
noncomputable def retractionOfHomotopy (g : C(X, Y)) (f : C(Y, X))
    (H : ContinuousMap.Homotopy (f.comp g) (ContinuousMap.id X)) (x : X) :
    FundamentalGroup Y (g x) →* FundamentalGroup X x :=
  (fundamentalGroupMulEquivOfPath (H.evalAt x)).toMonoidHom.comp (map f (g x))

/-- The retraction maps a loop by `f` and transports along the supplied homotopy track. -/
@[simp]
theorem retractionOfHomotopy_apply (g : C(X, Y)) (f : C(Y, X))
    (H : ContinuousMap.Homotopy (f.comp g) (ContinuousMap.id X)) (x : X)
    (γ : FundamentalGroup Y (g x)) :
    retractionOfHomotopy g f H x γ =
      fundamentalGroupMulEquivOfPath (H.evalAt x) (map f (g x) γ) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The retraction splits the homomorphism induced by `g`. -/
@[simp]
theorem retractionOfHomotopy_comp_map (g : C(X, Y)) (f : C(Y, X))
    (H : ContinuousMap.Homotopy (f.comp g) (ContinuousMap.id X)) (x : X) :
    (retractionOfHomotopy g f H x).comp (map g x) =
      MonoidHom.id (FundamentalGroup X x) := by
  simpa only [ContinuousMap.id_apply, retractionOfHomotopy, map_comp, map_id,
    MonoidHom.comp_assoc] using
    fundamentalGroupMulEquivOfPath_comp_map_of_homotopy H x

/-- As a function, the same retraction is a left inverse of the induced map. -/
theorem leftInverse_retractionOfHomotopy (g : C(X, Y)) (f : C(Y, X))
    (H : ContinuousMap.Homotopy (f.comp g) (ContinuousMap.id X)) (x : X) :
    Function.LeftInverse (retractionOfHomotopy g f H x) (map g x) := by
  intro γ
  exact DFunLike.congr_fun (retractionOfHomotopy_comp_map g f H x) γ

/-- A map admitting a homotopy left inverse induces an injective fundamental-group map. -/
theorem map_injective_of_homotopy_retraction (g : C(X, Y)) (f : C(Y, X))
    (H : ContinuousMap.Homotopy (f.comp g) (ContinuousMap.id X)) (x : X) :
    Function.Injective (map g x) :=
  (leftInverse_retractionOfHomotopy g f H x).injective

set_option backward.isDefEq.respectTransparency false in
/-- For identity maps the retraction is the identity, even for a moving self-homotopy. -/
@[simp]
theorem retractionOfHomotopy_id
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.id X)) (x : X) :
    retractionOfHomotopy (ContinuousMap.id X) (ContinuousMap.id X) H x =
      MonoidHom.id (FundamentalGroup X x) := by
  apply MonoidHom.ext
  intro γ
  simpa only [ContinuousMap.id_apply, map_id, MonoidHom.id_apply] using
    leftInverse_retractionOfHomotopy (ContinuousMap.id X) (ContinuousMap.id X) H x γ

/-- A nontrivial source vertex group cannot be a homotopy retract of a trivial
vertex group at its image. Only these two local fundamental groups are constrained;
no connectedness hypothesis is needed. This extends the strict-retraction obstruction
of May, Chapter 1, §6, p. 10. -/
theorem not_homotopic_comp_id (g : C(X, Y)) (f : C(Y, X)) (x : X)
    [Nontrivial (FundamentalGroup X x)] [Subsingleton (FundamentalGroup Y (g x))] :
    ¬ ContinuousMap.Homotopic (f.comp g) (ContinuousMap.id X) := by
  rintro ⟨H⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne (FundamentalGroup X x)
  exact hab (map_injective_of_homotopy_retraction g f H x (Subsingleton.elim _ _))

end FundamentalGroup
