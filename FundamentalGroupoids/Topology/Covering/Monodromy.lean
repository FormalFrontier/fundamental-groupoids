/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Monodromy stabilizers, path components and maps of fibers

For a covering map, the loops fixing a point of a fiber are exactly the image of the
fundamental group of the total space based at that point. Two points of a fiber lie in the
same monodromy orbit exactly when they are joined by a path in the total space.

The stabilizer and orbit statements use Mathlib's covering maps, which need not be
surjective. Unlike the connected, locally path-connected setting of May's covering-space
theory, they need no global connectedness, local path-connectedness, or separation assumptions.

Path connectedness of the total space makes the canonical monodromy action pretransitive at
any basepoint. With a chosen point of a fiber, `IsCoveringMap.monodromyQuotientEquiv`
identifies that fiber with the left cosets of the image of the induced fundamental-group map.
The coset of `g` maps to monodromy by `g`, and this equivalence intertwines the canonical
left action on cosets with monodromy. The group and the fiber may live in independent universes;
no normality or connectedness of the base is required. The same orbit–stabilizer
identification describes path components of pullback coverings.

Over a path-connected base, the converse holds for nonempty total spaces,
without local path connectedness: every path component meets the chosen fiber. Thus path
connectedness of the total space is equivalent to its nonemptiness and monodromy
pretransitivity. Nonemptiness is necessary because an empty fiber has a pretransitive action.

The monodromy and path-lifting constructions are those of Mathlib's prior formalization by
Junyan Xu in `Mathlib.Topology.Homotopy.Lifting`. In particular, the point stabilizer below
is not the kernel of the permutation representation for a general covering map. For quotient
coverings, Mathlib's `IsQuotientCoveringMap.monodromy_eq_id_iff` identifies these conditions,
and `IsQuotientCoveringMap.ker_monodromyPerm` already computes that kernel.

Commuting squares of continuous maps intertwine monodromy, including when the base map
is not a covering. Equivariant squares of quotient coverings also intertwine the canonical
fundamental-group homomorphisms to the opposite acting groups, without simple connectivity.
The same-base API is the identity-base specialization. The proof generalizes the
lifted-path-class argument of Mathlib's `IsQuotientCoveringMap.monodromy_toPermFiber`;
`IsQuotientCoveringMap.monodromy_naturality_toPermFiber` recovers its quotient-action
formula. Restriction to a point fiber is the equivariant map `IsCoveringMap.fiberMap`
for the two covering maps' canonical fundamental-group actions, without connectivity
hypotheses. Restriction preserves identities and composition.

Over a path-connected base, continuous maps out of a covering space are determined by their
values on one whole fiber when the target projection is separated and locally injective.
This uniqueness requires no local path connectedness.

Monodromy on a represented path is the endpoint of any continuous lift with the specified
starting value. For a simply connected quotient covering, the fundamental-group equivalence
has the same characteristic equation as its underlying homomorphism, in both multiplicative
and additive notation.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §§2–4,
  especially the monodromy discussion on p. 25.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §7, p. 29,
  for restriction of maps of covering spaces to a fiber and uniqueness.
* Junyan Xu, `Mathlib.Topology.Homotopy.Lifting`, for covering-space monodromy and lifting.
* Kenny Lau and Antoine Chambert-Loir, `Mathlib.GroupTheory.GroupAction.Hom`, for
  equivariant maps.
* Chris Hughes and Yury Kudryashov, `Mathlib.Algebra.Group.Action.Pretransitive`, for
  pretransitive actions.
* Chris Hughes and Thomas Browning, `Mathlib.GroupTheory.GroupAction.Quotient`, for the
  orbit–stabilizer equivalence, and `GroupTheory.GroupAction.Quotient` for its equivariance.
-/

@[expose] public section

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

namespace IsCoveringMap

variable (cov : IsCoveringMap p) {x : X}

/-- Monodromy on a represented path is the endpoint of a continuous lift with the specified
starting value. No connectedness or surjectivity is required. -/
theorem monodromy_mk_apply_eq_of_lift {y : X} (γ : Path x y) (e : p ⁻¹' {x})
    (Γ : C(unitInterval, E)) (hΓ : p ∘ Γ = γ) (h0 : Γ 0 = e.1) :
    (cov.monodromy (Path.Homotopic.Quotient.mk γ) e : E) = Γ 1 := by
  have hlift : Γ = cov.liftPath γ e.1 (γ.source.trans e.2.symm) :=
    (cov.eq_liftPath_iff' _).mpr ⟨hΓ, h0⟩
  change cov.liftPath γ e.1 _ 1 = Γ 1
  exact congrArg (fun δ : C(unitInterval, E) ↦ δ 1) hlift.symm

/-- Changing only the endpoint indices of a path class does not change the total-space
value of monodromy. The starting fiber point is transported along the same equality. -/
theorem monodromy_cast {x' y y' : X} (γ : Path.Homotopic.Quotient x y)
    (hx : x' = x) (hy : y' = y) (e : p ⁻¹' {x'}) :
    (cov.monodromy (γ.cast hx hy) e : E) =
      cov.monodromy γ ⟨e.1, e.2.trans hx⟩ := by
  cases hx
  cases hy
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]

set_option backward.isDefEq.respectTransparency.types false in
/-- A loop fixes a point of the fiber under monodromy if and only if it belongs to the image
of the fundamental group of the total space based at that point. This is the point-stabilizer
formulation of the covering-space correspondence in May, Chapter 3, §§2–4, without global
connectedness or local path-connectedness assumptions. No regularity of the covering is assumed. -/
theorem monodromy_eq_self_iff_mem_range (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    cov.monodromy γ e = e ↔
      γ ∈ (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ e.2).range := by
  constructor
  · intro h
    refine ⟨(cov.liftPathQuotient γ e).cast rfl (congrArg Subtype.val h.symm), ?_⟩
    rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.map_cast,
      cov.map_liftPathQuotient]
    simp
  · rintro ⟨Γ, rfl⟩
    apply cov.monodromy_eq_of_map_eq Γ
    rw [FundamentalGroup.mapOfEq_apply]
    simp

/-- Two points of a fiber lie in the same monodromy orbit if and only if they are joined by a
path in the total space. This is the orbit formulation of the covering-space correspondence in
May, Chapter 3, §§2–4. If the total space is path-connected, this equivalence yields transitivity;
the equivalence itself needs no such assumption. -/
theorem exists_monodromy_eq_iff_joined (e e' : p ⁻¹' {x}) :
    (∃ γ : FundamentalGroup X x, cov.monodromy γ e = e') ↔ Joined e.1 e'.1 := by
  constructor
  · rintro ⟨γ, rfl⟩
    obtain ⟨Γ⟩ := cov.liftPathQuotient γ e
    exact ⟨Γ⟩
  · rintro ⟨Γ⟩
    let γ := (Path.Homotopic.Quotient.mk Γ).map ⟨p, cov.continuous⟩
    refine ⟨γ.cast e.2.symm e'.2.symm, cov.monodromy_eq_of_map_eq (.mk Γ) ?_⟩
    exact ((γ.cast_cast e.2.symm e'.2.symm e.2 e'.2).trans γ.cast_rfl_rfl).symm

/-- A path-connected total space makes canonical monodromy pretransitive on every fiber.
No connectedness assumption on the base is needed, and the fiber may be empty. This is the
pretransitivity consequence of the orbit correspondence in May, Chapter 3, §§2–4. -/
theorem monodromy_isPretransitive (b : X) [PathConnectedSpace E] :
    @MulAction.IsPretransitive (FundamentalGroup X b) (p ⁻¹' {b})
      (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul := by
  refine @MulAction.IsPretransitive.mk (FundamentalGroup X b) (p ⁻¹' {b})
    (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul ?_
  intro e e'
  exact (cov.exists_monodromy_eq_iff_joined e e').mpr (PathConnectedSpace.joined _ _)

/-- Over a path-connected base, pretransitive canonical monodromy makes a nonempty total
space path-connected. Each path component meets the chosen fiber, so no local path
connectedness assumption is needed. Nonemptiness excludes the empty covering, whose
monodromy action is vacuously pretransitive. -/
theorem pathConnectedSpace_of_monodromy_isPretransitive (b : X)
    [PathConnectedSpace X] [Nonempty E]
    (h : @MulAction.IsPretransitive (FundamentalGroup X b) (p ⁻¹' {b})
      (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul) : PathConnectedSpace E := by
  refine ⟨inferInstance, ?_⟩
  intro e e'
  obtain ⟨a, ha⟩ := cov.comp_subtypeVal_pathComponent_surjective e b
  obtain ⟨a', ha'⟩ := cov.comp_subtypeVal_pathComponent_surjective e' b
  have hjoined : Joined a.val a'.val :=
    (cov.exists_monodromy_eq_iff_joined ⟨a.val, ha⟩ ⟨a'.val, ha'⟩).mp
      (h.exists_smul_eq ⟨a.val, ha⟩ ⟨a'.val, ha'⟩)
  exact (mem_pathComponent_iff.mp a.property).trans
    (hjoined.trans (mem_pathComponent_iff.mp a'.property).symm)

/-- Over a path-connected base, the total space is path-connected exactly when it is
nonempty and its canonical monodromy action on the chosen fiber is pretransitive. The
nonemptiness condition is essential: monodromy on the empty covering is pretransitive. -/
theorem pathConnectedSpace_iff_nonempty_and_monodromy_isPretransitive (b : X)
    [PathConnectedSpace X] :
    PathConnectedSpace E ↔ Nonempty E ∧
      @MulAction.IsPretransitive (FundamentalGroup X b) (p ⁻¹' {b})
        (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul := by
  constructor
  · intro h
    have := h
    exact ⟨h.nonempty, cov.monodromy_isPretransitive b⟩
  · rintro ⟨hne, h⟩
    have := hne
    exact cov.pathConnectedSpace_of_monodromy_isPretransitive b h

end IsCoveringMap

section Cosets

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

namespace IsCoveringMap

variable (hp : IsCoveringMap p) (b : B) (a : p ⁻¹' {b}) [PathConnectedSpace E]

/-- For a covering with path-connected total space, the left cosets of the image of the
induced based fundamental-group map are equivalent to the ordinary fiber. The coset of `g`
maps to `hp.monodromy g a`. No normality, connectedness of the base, or surjectivity is needed.

This is the orbit–stabilizer construction with the stabilizer identified by
`monodromy_eq_self_iff_mem_range`. Its representative formula determines the equivalence
uniquely by quotient induction and `Equiv.ext`. -/
noncomputable def monodromyQuotientEquiv :
    (FundamentalGroup B b ⧸
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ a.property).range) ≃ p ⁻¹' {b} := by
  letI := hp.fundamentalGroupMulAction b
  haveI : MulAction.IsPretransitive (FundamentalGroup B b) (p ⁻¹' {b}) :=
    hp.monodromy_isPretransitive b
  have h : MulAction.stabilizer (FundamentalGroup B b) a =
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ a.property).range := by
    ext g
    exact hp.monodromy_eq_self_iff_mem_range a g
  exact (Subgroup.quotientEquivOfEq h.symm).trans
    (((MulAction.orbitEquivQuotientStabilizer (FundamentalGroup B b) a).symm.trans
      (Set.equivOfEq (MulAction.orbit_eq_univ (FundamentalGroup B b) a))).trans
        (Equiv.Set.univ (p ⁻¹' {b})))

/-- The coset of a loop maps to its monodromy endpoint at the chosen fiber point. -/
@[simp] theorem monodromyQuotientEquiv_apply_mk (g : FundamentalGroup B b) :
    hp.monodromyQuotientEquiv b a (QuotientGroup.mk g) = hp.monodromy g a := by
  let := hp.fundamentalGroupMulAction b
  unfold monodromyQuotientEquiv
  rw [Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk]
  rfl

/-- The inverse equivalence sends a monodromy endpoint to the coset of its loop. -/
@[simp] theorem monodromyQuotientEquiv_symm_apply_monodromy (g : FundamentalGroup B b) :
    (hp.monodromyQuotientEquiv b a).symm (hp.monodromy g a) = QuotientGroup.mk g := by
  rw [Equiv.symm_apply_eq]
  exact (hp.monodromyQuotientEquiv_apply_mk b a g).symm

/-- The equivalence intertwines the canonical left action on cosets with monodromy. -/
@[simp] theorem monodromyQuotientEquiv_smul (k : FundamentalGroup B b)
    (q : FundamentalGroup B b ⧸
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ a.property).range) :
    hp.monodromyQuotientEquiv b a (k • q) =
      hp.monodromy k (hp.monodromyQuotientEquiv b a q) := by
  let := hp.fundamentalGroupMulAction b
  have h : MulAction.stabilizer (FundamentalGroup B b) a =
      (FundamentalGroup.mapOfEq ⟨p, hp.continuous⟩ a.property).range := by
    ext g
    exact hp.monodromy_eq_self_iff_mem_range a g
  have hq : Subgroup.quotientEquivOfEq h.symm (k • q) =
      k • Subgroup.quotientEquivOfEq h.symm q := by
    refine Quotient.inductionOn' q ?_
    intro g
    simp only [MulAction.Quotient.smul_mk, Subgroup.quotientEquivOfEq_mk]
  change ((MulAction.orbitEquivQuotientStabilizer (FundamentalGroup B b) a).symm
      (Subgroup.quotientEquivOfEq h.symm (k • q))).val =
    k • ((MulAction.orbitEquivQuotientStabilizer (FundamentalGroup B b) a).symm
      (Subgroup.quotientEquivOfEq h.symm q)).val
  rw [hq]
  exact congrArg Subtype.val
    (MulAction.orbitEquivQuotientStabilizer_symm_smul a k _)

end IsCoveringMap

end Cosets

section ChangingBase

universe u v w z a b

variable {E : Type u} {E' : Type v} {B : Type w} {B' : Type z}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B] [TopologicalSpace B']
  {p : E → B} {q : E' → B'}

namespace IsCoveringMap

/-- A commuting square of continuous maps intertwines covering monodromy along a path class
and its image in the other base. The base map and total-space map need not be covering maps;
neither covering needs to be surjective, and no connectivity hypotheses are required. -/
theorem monodromy_naturality_map (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (F : C(E, E')) (f : C(B, B')) (hF : q ∘ F = f ∘ p) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    covq.monodromy (γ.map f) ⟨F e, (congr_fun hF e).trans (congrArg f e.2)⟩ =
      ⟨F (covp.monodromy γ e),
        (congr_fun hF (covp.monodromy γ e)).trans
          (congrArg f (covp.monodromy γ e).2)⟩ := by
  let Γ := covp.liftPathQuotient γ e
  let p' : C(E, B) := ⟨p, covp.continuous⟩
  let q' : C(E', B') := ⟨q, covq.continuous⟩
  have hcomp : q'.comp F = f.comp p' := ContinuousMap.ext fun z ↦ congr_fun hF z
  apply covq.monodromy_eq_of_map_eq (Γ.map F)
  rw [← Path.Homotopic.Quotient.map_comp]
  have h := congrArg (fun δ : Path.Homotopic.Quotient (p e.1)
      (p (covp.monodromy γ e)) ↦ δ.map f) (covp.map_liftPathQuotient γ e)
  have h' := h.trans (Path.Homotopic.Quotient.map_cast γ
    (hx := e.2) (hy := (covp.monodromy γ e).2) (f := f))
  convert h' using 2
  · exact congr_fun hF e
  · exact congr_fun hF (covp.monodromy γ e)
  · rw [← Path.Homotopic.Quotient.map_comp]
    have hmap (g₁ g₂ : C(E, B')) (hg : g₁ = g₂) : HEq (Γ.map g₁) (Γ.map g₂) := by
      subst g₂
      rfl
    exact hmap _ _ hcomp
  · exact (Path.Homotopic.Quotient.cast_heq _ _ (γ := γ.map f)).trans
      (Path.Homotopic.Quotient.cast_heq _ _ (γ := γ.map f)).symm

end IsCoveringMap

namespace IsQuotientCoveringMap

variable {G : Type a} {H : Type b} [Group G] [Group H]
  [MulAction G E] [MulAction H E']

/-- An equivariant continuous map in a commuting square of quotient coverings intertwines
the canonical fundamental-group homomorphisms to the opposite acting groups. This does not
require either total space to be simply connected. -/
theorem fundamentalGroupToMulOpposite_naturality
    (hp : IsQuotientCoveringMap p G) (hq : IsQuotientCoveringMap q H)
    (ρ : G →* H) (F : C(E, E')) (f : C(B, B')) (hF : q ∘ F = f ∘ p)
    (hρ : ∀ (g : G) (e : E), F (g • e) = ρ g • F e) {x : B} (e : p ⁻¹' {x}) :
    (hq.fundamentalGroupToMulOpposite
      ⟨F e, (congr_fun hF e).trans (congrArg f e.2)⟩).comp
        (FundamentalGroup.map f x) =
      (MonoidHom.op ρ).comp (hp.fundamentalGroupToMulOpposite e) := by
  ext γ
  apply hq.fundamentalGroupToMulOpposite_apply_eq_Iff.mpr
  change ρ (hp.fundamentalGroupToMulOpposite e γ).unop • F e = _
  rw [← hρ, hp.unop_fundamentalGroupToMulOpposite_smul]
  exact (congrArg Subtype.val
    (hp.isCoveringMap.monodromy_naturality_map hq.isCoveringMap F f hF γ e)).symm

end IsQuotientCoveringMap

namespace IsAddQuotientCoveringMap

variable {G : Type a} {H : Type b} [AddGroup G] [AddGroup H]
  [AddAction G E] [AddAction H E']

/-- Additive quotient-covering naturality, obtained from the multiplicative theorem through
`Multiplicative`. No simple connectivity or connectedness hypothesis is required. -/
theorem fundamentalGroupToMulOpposite_naturality
    (hp : IsAddQuotientCoveringMap p G) (hq : IsAddQuotientCoveringMap q H)
    (ρ : G →+ H) (F : C(E, E')) (f : C(B, B')) (hF : q ∘ F = f ∘ p)
    (hρ : ∀ (g : G) (e : E), F (g +ᵥ e) = ρ g +ᵥ F e) {x : B} (e : p ⁻¹' {x}) :
    (hq.fundamentalGroupToMulOpposite
      ⟨F e, (congr_fun hF e).trans (congrArg f e.2)⟩).comp
        (FundamentalGroup.map f x) =
      (MonoidHom.op ρ.toMultiplicative).comp (hp.fundamentalGroupToMulOpposite e) :=
  hp.toMultiplicative.fundamentalGroupToMulOpposite_naturality hq.toMultiplicative
    ρ.toMultiplicative F f hF hρ e

end IsAddQuotientCoveringMap

end ChangingBase

section Maps

universe u v w z

variable {E : Type u} {E' : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : E → B} {q : E' → B}

namespace IsCoveringMap

/-- Monodromy is natural for continuous maps between covering spaces over the same base.
This uses the lifted homotopy class of a path, without connectivity hypotheses. -/
theorem monodromy_naturality (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (f : C(E, E')) (hf : q ∘ f = p) {x y : B}
    (γ : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    covq.monodromy γ ⟨f e, (congr_fun hf e).trans e.2⟩ =
      ⟨f (covp.monodromy γ e),
        (congr_fun hf (covp.monodromy γ e)).trans (covp.monodromy γ e).2⟩ := by
  obtain ⟨γ⟩ := γ
  exact covp.monodromy_naturality_map covq f (ContinuousMap.id B) hf
    (Path.Homotopic.Quotient.mk γ) e

/-- Restriction of a continuous map over the base to an equivariant map of point fibers.
Both actions are the specified covering maps' canonical fundamental-group actions. No
connectedness, local path connectedness or surjectivity is required. -/
def fiberMap (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (b : B) (f : {f : C(E, E') // q ∘ f = p}) :
    @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul :=
  @MulActionHom.mk (FundamentalGroup B b) (FundamentalGroup B b)
    (@id (FundamentalGroup B b))
    (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
    (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul
    (fun e ↦ ⟨f.val e.val, (congr_fun f.property e.val).trans e.property⟩)
    (fun γ e ↦ (covp.monodromy_naturality covq f.val f.property γ e).symm)

/-- Restriction evaluates the original continuous map on the fiber. -/
theorem fiberMap_apply (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (b : B) (f : {f : C(E, E') // q ∘ f = p}) (e : p ⁻¹' {b}) :
    covp.fiberMap covq b f e =
      ⟨f.val e.val, (congr_fun f.property e.val).trans e.property⟩ := rfl

/-- The total-space coordinate of restriction is evaluation of the original map. -/
@[simp] theorem fiberMap_apply_coe (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (b : B) (f : {f : C(E, E') // q ∘ f = p}) (e : p ⁻¹' {b}) :
    (covp.fiberMap covq b f e).val = f.val e.val := rfl

/-- An equivariant map is the restriction of an over-map exactly when their underlying
values agree on the whole fiber. -/
theorem fiberMap_eq_iff (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (b : B) (f : {f : C(E, E') // q ∘ f = p})
    {h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul} :
    covp.fiberMap covq b f = h ↔ ∀ e : p ⁻¹' {b}, f.val e.val = (h e).val := by
  constructor
  · intro hf e
    exact congrArg Subtype.val (DFunLike.congr_fun hf e)
  · intro hf
    exact DFunLike.ext _ _ fun e ↦ Subtype.ext (hf e)

/-- Restriction of the identity over-map is the identity equivariant map. -/
@[simp] theorem fiberMap_id (covp : IsCoveringMap p) (b : B) :
    covp.fiberMap covp b ⟨ContinuousMap.id E, rfl⟩ =
      @MulActionHom.id (FundamentalGroup B b) (p ⁻¹' {b})
        (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul := by
  exact DFunLike.ext _ _ fun _ ↦ Subtype.ext rfl

section Composition

variable {E'' : Type z} [TopologicalSpace E''] {r : E'' → B}

/-- Restriction preserves composition of continuous maps over the base. The three total
spaces and the base have independent universes. -/
@[simp] theorem fiberMap_comp (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    (covr : IsCoveringMap r) (b : B)
    (g : {g : C(E', E'') // r ∘ g = q}) (f : {f : C(E, E') // q ∘ f = p}) :
    covp.fiberMap covr b
      ⟨g.val.comp f.val, funext fun e ↦
        (congr_fun g.property (f.val e)).trans (congr_fun f.property e)⟩ =
      @MulActionHom.comp (FundamentalGroup B b) (FundamentalGroup B b)
        (FundamentalGroup B b) (@id (FundamentalGroup B b)) (@id (FundamentalGroup B b))
        (@id (FundamentalGroup B b))
        (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
        (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul
        (r ⁻¹' {b}) (covr.fundamentalGroupMulAction b).toSemigroupAction.toSMul
        (covq.fiberMap covr b g) (covp.fiberMap covq b f) inferInstance := by
  exact DFunLike.ext _ _ fun _ ↦ Subtype.ext rfl

end Composition

/-- Continuous maps over a path-connected base from a covering space to a separated,
locally injective map agree everywhere if they agree on one whole fiber. Every path component
of the source meets that fiber, and uniqueness of lifts applies on each component. No local
path connectedness, total-space connectedness, nonemptiness, or surjectivity is required. -/
theorem eq_of_comp_eq_of_eqOn_fiber (covp : IsCoveringMap p) (hsep : IsSeparatedMap q)
    (hinj : IsLocallyInjective q) [PathConnectedSpace B] (f g : C(E, E'))
    (hf : q ∘ f = p) (hg : q ∘ g = p) (b : B)
    (h : ∀ e : p ⁻¹' {b}, f e = g e) : f = g := by
  ext e
  obtain ⟨a, ha⟩ := covp.comp_subtypeVal_pathComponent_surjective e b
  exact hsep.eqOn_of_comp_eqOn hinj isPathConnected_pathComponent.isConnected.isPreconnected
    f.continuous.continuousOn g.continuous.continuousOn
    (fun z _ ↦ congr_fun (hf.trans hg.symm) z) a.property (h ⟨a, ha⟩)
    (mem_pathComponent_self e)

/-- Restriction to a whole fiber is injective over a path-connected base. The total spaces
need not be connected, locally path connected or nonempty. -/
theorem fiberMap_injective (covp : IsCoveringMap p) (covq : IsCoveringMap q)
    [PathConnectedSpace B] (b : B) : Function.Injective (covp.fiberMap covq b) := by
  intro f g h
  apply Subtype.ext
  exact covp.eq_of_comp_eq_of_eqOn_fiber covq.isSeparatedMap
    covq.isLocalHomeomorph.isLocallyInjective f.val g.val f.property g.property b
    ((covp.fiberMap_eq_iff covq b f).mp h)

end IsCoveringMap

end Maps

namespace IsQuotientCoveringMap

variable {G : Type*} [Group G] [MulAction G E] (hp : IsQuotientCoveringMap p G) {x : X}

/-- Naturality for the continuous action defining a quotient covering recovers the
`IsQuotientCoveringMap.monodromy_toPermFiber` formula. Thus the naturality statement for
arbitrary covering maps specializes to the quotient-covering commutation law. -/
theorem monodromy_naturality_toPermFiber {y : X} (γ : Path.Homotopic.Quotient x y)
    (g : G) (e : p ⁻¹' {x}) :
    hp.isCoveringMap.monodromy γ (hp.toPermFiber x g e) =
      hp.toPermFiber y g (hp.isCoveringMap.monodromy γ e) := by
  exact hp.isCoveringMap.monodromy_naturality hp.isCoveringMap
    ⟨fun z ↦ g • z, hp.toContinuousConstSMul.continuous_const_smul g⟩
    (funext fun _ ↦ hp.map_smul g) γ e

/-- For a quotient covering, fixing one point of a fiber under monodromy is equivalent to
acting trivially on the whole fiber. Thus the kernel of the monodromy representation is the
preimage of any point stabilizer. Combined with
`IsCoveringMap.monodromy_eq_self_iff_mem_range`, this recovers
`IsQuotientCoveringMap.ker_monodromyPerm`. -/
theorem ker_monodromyPerm_eq_comap_stabilizer (e : p ⁻¹' {x}) :
    (hp.isCoveringMap.monodromyPerm x).ker =
      (MulAction.stabilizer (Equiv.Perm (p ⁻¹' {x})) e).comap
        (hp.isCoveringMap.monodromyPerm x) := by
  ext γ
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  simpa only [DFunLike.ext'_iff, IsCoveringMap.coe_monodromyPerm, Equiv.Perm.coe_one,
    Equiv.Perm.smul_def] using hp.monodromy_eq_id_iff e (γ := γ)

/-- The quotient-covering equivalence acts by its underlying fundamental-group homomorphism. -/
@[simp]
theorem fundamentalGroupEquiv_apply [SimplyConnectedSpace E] (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) :
    hp.fundamentalGroupEquiv e γ = hp.fundamentalGroupToMulOpposite e γ := rfl

/-- The value of the quotient-covering equivalence is characterized by translation of the
chosen fiber point to its monodromy image. -/
theorem fundamentalGroupEquiv_apply_eq_iff [SimplyConnectedSpace E] (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) (g : Gᵐᵒᵖ) :
    hp.fundamentalGroupEquiv e γ = g ↔
      g.unop • e.1 = hp.isCoveringMap.monodromy γ e := by
  simpa only [fundamentalGroupEquiv_apply] using
    (hp.fundamentalGroupToMulOpposite_apply_eq_Iff (e := e) (γ := γ) (g := g))

end IsQuotientCoveringMap

namespace IsAddQuotientCoveringMap

variable {G : Type*} [AddGroup G] [AddAction G E]
    (hp : IsAddQuotientCoveringMap p G) {x : X}

/-- The additive quotient-covering equivalence acts by its underlying fundamental-group
homomorphism. -/
@[simp]
theorem fundamentalGroupEquiv_apply [SimplyConnectedSpace E] (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) :
    hp.fundamentalGroupEquiv e γ = hp.fundamentalGroupToMulOpposite e γ :=
  hp.toMultiplicative.fundamentalGroupEquiv_apply e γ

/-- The value of the additive quotient-covering equivalence is characterized by translation
of the chosen fiber point to its monodromy image. -/
theorem fundamentalGroupEquiv_apply_eq_iff [SimplyConnectedSpace E] (e : p ⁻¹' {x})
    (γ : FundamentalGroup X x) (g : (Multiplicative G)ᵐᵒᵖ) :
    hp.fundamentalGroupEquiv e γ = g ↔
      g.unop • e.1 = hp.isCoveringMap.monodromy γ e :=
  hp.toMultiplicative.fundamentalGroupEquiv_apply_eq_iff e γ g

end IsAddQuotientCoveringMap
