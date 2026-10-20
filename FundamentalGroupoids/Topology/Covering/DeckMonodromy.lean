/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.GroupTheory.Subgroup.Centralizer
import FundamentalGroupoids.Topology.Covering.Equivalence
public import FundamentalGroupoids.Topology.Covering.Monodromy
public import FundamentalGroupoids.Topology.Covering.DeckGroup

/-!
# Maps of covering spaces and monodromy

Restriction to a fiber identifies continuous maps over a common base with equivariant maps
for the covers' canonical fundamental-group actions. The target is Mathlib's `MulActionHom`,
not a space of bijections: an individual map of fibers need not be invertible.
`IsCoveringMap.fiberMapEquivOfPathConnected` requires only a path-connected, locally
path-connected source and a supplied source point. `IsCoveringMap.fiberMapEquiv` instead
requires a path-connected base and a locally path-connected source, which may be empty or
disconnected. Neither comparison requires connectivity or local path connectedness of the
target. Their forward map is the unconditional `IsCoveringMap.fiberMap`.

The inverse uses Mathlib's based lifting criterion. Equivariance gives inclusion of the
fundamental-group images via `IsCoveringMap.monodromy_eq_self_iff_mem_range`. In the full
comparison the based lifts are glued on the source's open path components, without selecting
a global point of either total space. These constructions generalize the covering-space
extension argument of May, Chapter 3, §7.

For deck transformations, restriction to a point fiber gives a homomorphism from the deck
group to the centralizer of monodromy in the permutation group of that fiber. No connectivity
hypotheses are needed for this homomorphism. If the base is path connected, restriction to
the whole fiber is faithful, even when the total space is disconnected or empty. Local path
connectedness is not needed for faithfulness.

If the total space is locally path connected and the base is path connected, restriction
is a multiplicative equivalence `IsCoveringMap.deckMonodromyEquiv`. A commuting permutation
extends by based lifting on each open path component, and whole-fiber uniqueness makes the
extensions for a permutation and its inverse into inverse maps. The total space may be
empty; no point of it or surjectivity of the covering is assumed.

For path-connected, locally path-connected total space,
`IsCoveringMap.deckMonodromyEquivOfPathConnected` uses the fiber over the image of a supplied
point, with no connectedness assumption on the base. Both equivalences have the same
canonical restriction homomorphism as their forward map. These formulations generalize
the connected, locally path-connected setting of May, Chapter 3, §7.

The target is a subgroup of the permutation group of the point fiber, not a group structure
on that fiber. This centralizer is distinct from a point stabilizer or the kernel of the
monodromy representation, both of which are subgroups of the fundamental group.

The fiber action is the existing `deck.instMulActionFiber`; both deck transformations and
permutations multiply by composition, so restriction involves no inversion.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §7, p. 29,
  for restriction of maps of covering spaces to a fiber and its inverse.
* Mathlib's based lifting criterion and the open-path-component gluing argument.
* Mathlib's deck group (Kim Morrison), covering-space monodromy and lifting (Junyan Xu),
  and restriction of group actions to invariant subsets.
* Mathlib's equivariant maps (`MulActionHom`), formalized by Kenny Lau and
  Antoine Chambert-Loir.
* Covering-space fiber actions, monodromy naturality, and extension of deck transformations
  from equivariant fiber permutations.
-/

@[expose] public section

universe u v w z

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B} (cov : IsCoveringMap p)

/-- Deck transformations intertwine monodromy along every homotopy class of paths.
This is naturality for their continuous maps over the base. -/
theorem monodromy_deck_smul {x y : B} (γ : Path.Homotopic.Quotient x y)
    (g : deck p) (e : p ⁻¹' {x}) :
    cov.monodromy γ (g • e) = g • cov.monodromy γ e := by
  apply Subtype.ext
  exact congrArg Subtype.val (cov.monodromy_naturality cov
    ⟨fun z ↦ g • z, (g : E ≃ₜ E).continuous⟩ (deck.comp_eq g) γ e)

/-- The permutation induced by a deck transformation commutes with every monodromy
permutation on the fiber. -/
theorem commute_monodromyPerm_deck (b : B) (γ : FundamentalGroup B b) (g : deck p) :
    Commute (cov.monodromyPerm b γ)
      (MulAction.toPermHom (deck p) (p ⁻¹' {b}) g) := by
  ext e
  exact congrArg Subtype.val (cov.monodromy_deck_smul γ g e)

/-- Restriction of deck transformations to a fiber, with codomain the centralizer of
monodromy. This is the forward map in the covering-space comparison of May, Chapter 3,
§7, p. 29, without connectedness, local path connectedness, or surjectivity assumptions. -/
noncomputable def deckMonodromyHom (b : B) :
    deck p →* Subgroup.centralizer (Set.range (cov.monodromyPerm b)) :=
  (MulAction.toPermHom (deck p) (p ⁻¹' {b})).codRestrict _ fun g ↦ by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨γ, rfl⟩
    exact (cov.commute_monodromyPerm_deck b γ g).eq

/-- Restriction acts by the original deck transformation on the underlying total-space
coordinate. -/
@[simp] theorem deckMonodromyHom_apply_coe (b : B) (g : deck p) (e : p ⁻¹' {b}) :
    ((cov.deckMonodromyHom b g).val e).val = g • e.val :=
  rfl

include cov

/-- Deck transformations of a cover over a path-connected base are equal if their actions
agree on a whole fiber. This is the uniqueness part of restriction to a fiber in May,
Chapter 3, §7, p. 29; the total space need not be connected, locally path connected, or
nonempty. -/
theorem deck_ext [PathConnectedSpace B] (b : B) {g h : deck p}
    (he : ∀ e : p ⁻¹' {b}, g • e.val = h • e.val) : g = h := by
  have heq := cov.eq_of_comp_eq_of_eqOn_fiber cov.isSeparatedMap
    cov.isLocalHomeomorph.isLocallyInjective
    (⟨fun z ↦ g • z, (g : E ≃ₜ E).continuous⟩ : C(E, E))
    ⟨fun z ↦ h • z, (h : E ≃ₜ E).continuous⟩ (deck.comp_eq g) (deck.comp_eq h) b he
  apply eq_of_smul_eq_smul (α := E)
  intro e
  exact congrArg (fun f : C(E, E) ↦ f e) heq

/-- Restriction to the monodromy centralizer is injective over a path-connected base.
No local path connectedness of either space is required. -/
theorem deckMonodromyHom_injective [PathConnectedSpace B] (b : B) :
    Function.Injective (cov.deckMonodromyHom b) := by
  intro g h heq
  apply cov.deck_ext b
  intro e
  simpa only [deckMonodromyHom_apply_coe] using
    congrArg (fun α : Subgroup.centralizer (Set.range (cov.monodromyPerm b)) ↦
      (α.val e).val) heq

end IsCoveringMap

namespace IsCoveringMap

section Extension

variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  {p : E → B} {q : F → B} (covp : IsCoveringMap p) (covq : IsCoveringMap q)
  {b : B}

private theorem centralizer_range_le
    (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul) (e : p ⁻¹' {b}) :
    (FundamentalGroup.mapOfEq ⟨p, covp.continuous⟩ e.property).range ≤
      (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ (h e).property).range := by
  intro γ hγ
  apply (covq.monodromy_eq_self_iff_mem_range (h e) γ).mp
  calc
    covq.monodromy γ (h e) = h (covp.monodromy γ e) :=
      (@MulActionHom.map_smul' (FundamentalGroup B b) (FundamentalGroup B b)
        (@id (FundamentalGroup B b))
        (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
        (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul h γ e).symm
    _ = h e := congrArg h ((covp.monodromy_eq_self_iff_mem_range e γ).mpr hγ)

private theorem exists_based_monodromy_lift
    {A : Type z} [TopologicalSpace A] [PathConnectedSpace A]
    [LocallyPathConnectedSpace A] (i : C(A, E)) (a₀ : A) (ha : p (i a₀) = b)
    (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul) :
    ∃ g : C(A, F), g a₀ = (h ⟨i a₀, ha⟩).val ∧ q ∘ g = p ∘ i := by
  subst b
  let e : p ⁻¹' {p (i a₀)} := ⟨i a₀, rfl⟩
  have hπ : (FundamentalGroup.map ((⟨p, covp.continuous⟩ : C(E, B)).comp i) a₀).range ≤
      (FundamentalGroup.mapOfEq ⟨q, covq.continuous⟩ (h e).property).range := by
    apply le_trans _ (covp.centralizer_range_le covq h e)
    rintro _ ⟨γ, rfl⟩
    refine ⟨FundamentalGroup.map i a₀ γ, ?_⟩
    change FundamentalGroup.mapOfEq ⟨p, covp.continuous⟩ rfl
      (FundamentalGroup.map i a₀ γ) = _
    simp only [FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
      Path.Homotopic.Quotient.cast_rfl_rfl, Path.Homotopic.Quotient.map_comp]
  exact (covq.existsUnique_continuousMap_lifts_of_range_le
    (f := (⟨p, covp.continuous⟩ : C(E, B)).comp i) (a₀ := a₀) (e₀ := (h e).val)
    (show q (h e).val = p (i a₀) from (h e).property) hπ).exists

private theorem based_monodromy_lift_fiber
    {A : Type z} [TopologicalSpace A] [PathConnectedSpace A]
    (i : C(A, E)) (g : C(A, F)) (hg : q ∘ g = p ∘ i) (a₀ : A) (ha₀ : p (i a₀) = b)
    (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul)
    (h₀ : g a₀ = (h ⟨i a₀, ha₀⟩).val) (a : A) (ha : p (i a) = b) :
    g a = (h ⟨i a, ha⟩).val := by
  let δ := PathConnectedSpace.somePath a₀ a
  let γ : FundamentalGroup B b :=
    (((Path.Homotopic.Quotient.mk δ).map i).map ⟨p, covp.continuous⟩).cast ha₀.symm ha.symm
  have hi : covp.monodromy γ ⟨i a₀, ha₀⟩ = ⟨i a, ha⟩ :=
    covp.monodromy_eq_of_map_eq ((Path.Homotopic.Quotient.mk δ).map i) (by
      change ((Path.Homotopic.Quotient.mk δ).map i).map ⟨p, covp.continuous⟩ =
        Path.Homotopic.Quotient.cast γ ha₀ ha
      simp only [γ, Path.Homotopic.Quotient.cast_cast,
        Path.Homotopic.Quotient.cast_rfl_rfl])
  have hcomp : (⟨q, covq.continuous⟩ : C(F, B)).comp g =
      (⟨p, covp.continuous⟩ : C(E, B)).comp i := ContinuousMap.ext (congr_fun hg)
  have hga₀ : q (g a₀) = b := (congr_fun hg a₀).trans ha₀
  have hga : q (g a) = b := (congr_fun hg a).trans ha
  have map_loop_eq (f f' : C(A, B)) (hff' : f = f')
      (hx : f a₀ = b) (hy : f a = b) (hx' : f' a₀ = b) (hy' : f' a = b) :
      ((Path.Homotopic.Quotient.mk δ).map f).cast hx.symm hy.symm =
        ((Path.Homotopic.Quotient.mk δ).map f').cast hx'.symm hy'.symm := by
    subst f'
    rfl
  have hloop : (((Path.Homotopic.Quotient.mk δ).map g).map
      ⟨q, covq.continuous⟩).cast hga₀.symm hga.symm = γ := by
    simp only [γ, ← Path.Homotopic.Quotient.map_comp]
    exact map_loop_eq _ _ hcomp hga₀ hga ha₀ ha
  have hgg : covq.monodromy γ ⟨g a₀, hga₀⟩ = ⟨g a, hga⟩ := by
    rw [← hloop]
    apply covq.monodromy_eq_of_map_eq ((Path.Homotopic.Quotient.mk δ).map g)
    change ((Path.Homotopic.Quotient.mk δ).map g).map ⟨q, covq.continuous⟩ =
      ((((Path.Homotopic.Quotient.mk δ).map g).map ⟨q, covq.continuous⟩).cast
        hga₀.symm hga.symm).cast hga₀ hga
    simp only [Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]
  have hbase : (⟨g a₀, hga₀⟩ : q ⁻¹' {b}) = h ⟨i a₀, ha₀⟩ := Subtype.ext h₀
  have hh : covq.monodromy γ (h ⟨i a₀, ha₀⟩) =
      h (covp.monodromy γ ⟨i a₀, ha₀⟩) :=
    (@MulActionHom.map_smul' (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      h γ ⟨i a₀, ha₀⟩).symm
  rw [hbase, hh, hi] at hgg
  exact (congrArg Subtype.val hgg).symm

private theorem exists_continuousMap_monodromy_extension_of_pathConnected
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (h : @MulActionHom (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul) :
    ∃ g : C(E, F), q ∘ g = p ∧ ∀ e : p ⁻¹' {p e₀}, g e.val = (h e).val := by
  obtain ⟨g, h₀, hg⟩ := covp.exists_based_monodromy_lift covq (ContinuousMap.id E) e₀ rfl h
  refine ⟨g, ?_, fun e ↦ ?_⟩
  · exact funext fun e ↦ congr_fun hg e
  · exact covp.based_monodromy_lift_fiber covq (ContinuousMap.id E) g hg e₀ rfl h h₀
      e.val e.property

private theorem exists_pathComponent_monodromy_lift [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul) (x : E) :
    ∃ g : C(pathComponent x, F), q ∘ g = p ∘ Subtype.val ∧
      ∀ (e : p ⁻¹' {b}) (he : e.val ∈ pathComponent x), g ⟨e.val, he⟩ = (h e).val := by
  let : PathConnectedSpace (pathComponent x) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent
  let : LocallyPathConnectedSpace (pathComponent x) :=
    (IsOpen.pathComponent x).locallyPathConnectedSpace
  obtain ⟨a₀, ha₀⟩ := covp.comp_subtypeVal_pathComponent_surjective x b
  let i : C(pathComponent x, E) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨g, h₀, hg⟩ := covp.exists_based_monodromy_lift covq i a₀ ha₀ h
  refine ⟨g, hg, fun e he ↦ ?_⟩
  exact covp.based_monodromy_lift_fiber covq i g hg a₀ ha₀ h h₀ ⟨e.val, he⟩ e.property

/-- Extend an equivariant fiber map by gluing based lifts on the open path components of
its source. No point of the source or target is selected globally. -/
private theorem exists_continuousMap_monodromy_extension [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul) :
    ∃ g : C(E, F), q ∘ g = p ∧ ∀ e : p ⁻¹' {b}, g e.val = (h e).val := by
  classical
  let Components := {s : Set E // ∃ x : E, s = pathComponent x}
  let component (x : E) : Components := ⟨pathComponent x, x, rfl⟩
  have hlifts (s : Components) :
      ∃ g : C(s.val, F), q ∘ g = p ∘ Subtype.val ∧
        ∀ (e : p ⁻¹' {b}) (he : e.val ∈ s.val), g ⟨e.val, he⟩ = (h e).val := by
    rcases s with ⟨s, x, rfl⟩
    exact covp.exists_pathComponent_monodromy_lift covq h x
  choose lifts hlifts_proj hlifts_fiber using hlifts
  let g (x : E) : F := lifts (component x) ⟨x, mem_pathComponent_self x⟩
  have hcomponent (s : Components) (y : s.val) : component y.val = s := by
    apply Subtype.ext
    obtain ⟨x, hx⟩ := s.property
    change pathComponent y.val = s.val
    exact (pathComponent_congr (hx ▸ y.property)).trans hx.symm
  have hrestrict (s : Components) (y : s.val) : g y.val = lifts s y := by
    have htransport (t : Components) (ht : t = s) (hy : y.val ∈ t.val) :
        lifts t ⟨y.val, hy⟩ = lifts s y := by
      subst t
      rfl
    exact htransport _ (hcomponent s y) (mem_pathComponent_self y.val)
  have hcont : Continuous g := by
    apply continuous_of_continuousOn_iUnion_of_isOpen (s := fun s : Components ↦ s.val)
    · intro s
      rw [continuousOn_iff_continuous_domRestrict]
      convert (lifts s).continuous using 1
      funext y
      exact hrestrict s y
    · rintro ⟨s, x, rfl⟩
      exact IsOpen.pathComponent x
    · apply Set.eq_univ_of_forall
      intro x
      exact Set.mem_iUnion.mpr ⟨component x, mem_pathComponent_self x⟩
  refine ⟨⟨g, hcont⟩, funext fun x ↦ ?_, fun e ↦ ?_⟩
  · change q (g x) = p x
    rw [hrestrict (component x) ⟨x, mem_pathComponent_self x⟩]
    exact congr_fun (hlifts_proj (component x)) ⟨x, mem_pathComponent_self x⟩
  · change g e.val = (h e).val
    rw [hrestrict (component e.val) ⟨e.val, mem_pathComponent_self e.val⟩]
    exact hlifts_fiber (component e.val) e (mem_pathComponent_self e.val)

/-- Over-maps from a path-connected source are determined by restriction to an occupied
fiber. Only the source is path connected; no local path connectedness is needed. -/
theorem fiberMap_injective_of_pathConnected [PathConnectedSpace E] (e₀ : E) :
    Function.Injective (covp.fiberMap covq (p e₀)) := by
  intro f g hfg
  apply Subtype.ext
  apply DFunLike.ext'
  have he := (covp.fiberMap_eq_iff covq (p e₀) f).mp hfg
  exact covq.eq_of_comp_eq f.val.continuous g.val.continuous
    (f.property.trans g.property.symm) e₀ (he ⟨e₀, rfl⟩)

/-- Restriction to the fiber containing a supplied source point identifies continuous
maps over the base with equivariant maps of fibers. Only the source total space must be
path connected and locally path connected. This is the occupied-fiber form of the map
comparison in May, Chapter 3 §7; the base and target have no connectivity hypotheses. -/
noncomputable def fiberMapEquivOfPathConnected [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    {f : C(E, F) // q ∘ f = p} ≃
      @MulActionHom (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul :=
  Equiv.ofBijective (covp.fiberMap covq (p e₀))
    ⟨covp.fiberMap_injective_of_pathConnected covq e₀, by
      intro h
      obtain ⟨g, hg, hgf⟩ :=
        covp.exists_continuousMap_monodromy_extension_of_pathConnected covq e₀ h
      exact ⟨⟨g, hg⟩, (covp.fiberMap_eq_iff covq (p e₀) ⟨g, hg⟩).mpr hgf⟩⟩

/-- Restriction to one whole fiber identifies maps of covers with equivariant maps of
fibers over a path-connected base. The source need only be locally path connected and may
be empty or disconnected; no connectivity or local path connectedness of the target is
required. The inverse glues the occupied construction over the source's open components. -/
noncomputable def fiberMapEquiv [PathConnectedSpace B] [LocallyPathConnectedSpace E]
    (b : B) : {f : C(E, F) // q ∘ f = p} ≃
      @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul :=
  Equiv.ofBijective (covp.fiberMap covq b) ⟨covp.fiberMap_injective covq b, by
    intro h
    obtain ⟨g, hg, hgf⟩ := covp.exists_continuousMap_monodromy_extension covq h
    exact ⟨⟨g, hg⟩, (covp.fiberMap_eq_iff covq b ⟨g, hg⟩).mpr hgf⟩⟩

/-- The forward map of the comparison is canonical restriction to the fiber. -/
@[simp] theorem fiberMapEquivOfPathConnected_toFun
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E) :
    ⇑(covp.fiberMapEquivOfPathConnected covq e₀) = covp.fiberMap covq (p e₀) :=
  rfl

/-- The comparison evaluates the original continuous map on each fiber coordinate. -/
@[simp] theorem fiberMapEquivOfPathConnected_apply_coe
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : {f : C(E, F) // q ∘ f = p}) (e : p ⁻¹' {p e₀}) :
    (covp.fiberMapEquivOfPathConnected covq e₀ f e).val = f.val e.val :=
  rfl

/-- The inverse comparison extends the given equivariant map on the whole fiber. -/
@[simp] theorem fiberMapEquivOfPathConnected_symm_apply_coe
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (h : @MulActionHom (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul)
    (e : p ⁻¹' {p e₀}) :
    ((covp.fiberMapEquivOfPathConnected covq e₀).symm h).val e.val = (h e).val :=
  congrArg Subtype.val
    (DFunLike.congr_fun ((covp.fiberMapEquivOfPathConnected covq e₀).apply_symm_apply h) e)

/-- The comparison is characterized by its values on the source fiber. -/
theorem fiberMapEquivOfPathConnected_apply_eq_iff
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : {f : C(E, F) // q ∘ f = p})
    (h : @MulActionHom (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul) :
    covp.fiberMapEquivOfPathConnected covq e₀ f = h ↔
      ∀ e : p ⁻¹' {p e₀}, f.val e.val = (h e).val :=
  covp.fiberMap_eq_iff covq (p e₀) f

/-- Restricting an extension recovers the supplied equivariant map. -/
theorem fiberMapEquivOfPathConnected_apply_symm_apply
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (h : @MulActionHom (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul) :
    covp.fiberMapEquivOfPathConnected covq e₀
      ((covp.fiberMapEquivOfPathConnected covq e₀).symm h) = h :=
  (covp.fiberMapEquivOfPathConnected covq e₀).apply_symm_apply h

/-- Extending a restriction recovers the original continuous map over the base. -/
theorem fiberMapEquivOfPathConnected_symm_apply_apply
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : {f : C(E, F) // q ∘ f = p}) :
    (covp.fiberMapEquivOfPathConnected covq e₀).symm
      (covp.fiberMapEquivOfPathConnected covq e₀ f) = f :=
  (covp.fiberMapEquivOfPathConnected covq e₀).symm_apply_apply f

/-- Two equivariant maps agree if their extensions agree on all source points. -/
theorem fiberMapEquivOfPathConnected_symm_ext
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    {h k : @MulActionHom (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul}
    (hhk : ∀ e : E, ((covp.fiberMapEquivOfPathConnected covq e₀).symm h).val e =
      ((covp.fiberMapEquivOfPathConnected covq e₀).symm k).val e) : h = k := by
  apply (covp.fiberMapEquivOfPathConnected covq e₀).symm.injective
  exact Subtype.ext (ContinuousMap.ext hhk)

/-- In the occupied case, the extension is recognized by a single chosen-point equation
among continuous maps over the base. -/
theorem fiberMapEquivOfPathConnected_symm_eq_iff
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (h : @MulActionHom (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul)
    (f : {f : C(E, F) // q ∘ f = p}) :
    (covp.fiberMapEquivOfPathConnected covq e₀).symm h = f ↔ f.val e₀ = (h ⟨e₀, rfl⟩).val := by
  constructor
  · rintro rfl
    exact covp.fiberMapEquivOfPathConnected_symm_apply_coe covq e₀ h ⟨e₀, rfl⟩
  · intro hf
    apply Subtype.ext
    apply DFunLike.ext'
    exact covq.eq_of_comp_eq ((covp.fiberMapEquivOfPathConnected covq e₀).symm h).val.continuous
      f.val.continuous
      (((covp.fiberMapEquivOfPathConnected covq e₀).symm h).property.trans f.property.symm) e₀
      ((covp.fiberMapEquivOfPathConnected_symm_apply_coe covq e₀ h ⟨e₀, rfl⟩).trans hf.symm)

/-- The forward map of the comparison is canonical restriction to the fiber. -/
@[simp] theorem fiberMapEquiv_toFun [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B) :
    ⇑(covp.fiberMapEquiv covq b) = covp.fiberMap covq b :=
  rfl

/-- The comparison evaluates the original continuous map on each fiber coordinate. -/
@[simp] theorem fiberMapEquiv_apply_coe [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B)
    (f : {f : C(E, F) // q ∘ f = p}) (e : p ⁻¹' {b}) :
    (covp.fiberMapEquiv covq b f e).val = f.val e.val :=
  rfl

/-- The inverse comparison extends the given equivariant map on the whole fiber. -/
@[simp] theorem fiberMapEquiv_symm_apply_coe
    [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B)
    (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul) (e : p ⁻¹' {b}) :
    ((covp.fiberMapEquiv covq b).symm h).val e.val = (h e).val :=
  congrArg Subtype.val (DFunLike.congr_fun ((covp.fiberMapEquiv covq b).apply_symm_apply h) e)

/-- The comparison is characterized by its values on the source fiber. -/
theorem fiberMapEquiv_apply_eq_iff [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B)
    (f : {f : C(E, F) // q ∘ f = p})
    (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul) :
    covp.fiberMapEquiv covq b f = h ↔ ∀ e : p ⁻¹' {b}, f.val e.val = (h e).val :=
  covp.fiberMap_eq_iff covq b f

/-- Restricting an extension recovers the supplied equivariant map. -/
theorem fiberMapEquiv_apply_symm_apply
    [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B)
    (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul) :
    covp.fiberMapEquiv covq b ((covp.fiberMapEquiv covq b).symm h) = h :=
  (covp.fiberMapEquiv covq b).apply_symm_apply h

/-- Extending a restriction recovers the original continuous map over the base. -/
theorem fiberMapEquiv_symm_apply_apply
    [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B)
    (f : {f : C(E, F) // q ∘ f = p}) :
    (covp.fiberMapEquiv covq b).symm (covp.fiberMapEquiv covq b f) = f :=
  (covp.fiberMapEquiv covq b).symm_apply_apply f

/-- Two equivariant maps agree if their extensions agree on all source points. -/
theorem fiberMapEquiv_symm_ext [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B)
    {h k : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul}
    (hhk : ∀ e : E, ((covp.fiberMapEquiv covq b).symm h).val e =
      ((covp.fiberMapEquiv covq b).symm k).val e) : h = k := by
  apply (covp.fiberMapEquiv covq b).symm.injective
  exact Subtype.ext (ContinuousMap.ext hhk)

/-- The extension is the unique continuous over-map with the prescribed fiber values. -/
theorem fiberMapEquiv_symm_eq_iff [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B)
    (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul)
    (f : {f : C(E, F) // q ∘ f = p}) :
    (covp.fiberMapEquiv covq b).symm h = f ↔ ∀ e : p ⁻¹' {b}, f.val e.val = (h e).val := by
  rw [Equiv.symm_apply_eq, eq_comm, covp.fiberMapEquiv_apply_eq_iff covq b]

/-- Where both comparisons apply, they agree as equivalence data because their forward
maps are the same canonical restriction. -/
theorem fiberMapEquiv_eq_of_pathConnected [PathConnectedSpace B] [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    covp.fiberMapEquiv covq (p e₀) = covp.fiberMapEquivOfPathConnected covq e₀ := by
  apply Equiv.ext
  intro f
  rfl

/-- Restriction under the comparison preserves the identity over-map. -/
@[simp] theorem fiberMapEquivOfPathConnected_id
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E) :
    covp.fiberMapEquivOfPathConnected covp e₀ ⟨ContinuousMap.id E, rfl⟩ =
      @MulActionHom.id (FundamentalGroup B (p e₀)) (p ⁻¹' {p e₀})
      (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul :=
  covp.fiberMap_id (p e₀)

/-- Extending the identity equivariant map gives the identity over-map. -/
@[simp] theorem fiberMapEquivOfPathConnected_symm_id
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E) :
    (covp.fiberMapEquivOfPathConnected covp e₀).symm
      (@MulActionHom.id (FundamentalGroup B (p e₀)) (p ⁻¹' {p e₀})
        (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul) =
      ⟨ContinuousMap.id E, rfl⟩ := by
  apply (covp.fiberMapEquivOfPathConnected covp e₀).symm_apply_eq.mpr
  exact (covp.fiberMapEquivOfPathConnected_id e₀).symm

/-- Restriction under the comparison preserves the identity over-map. -/
@[simp] theorem fiberMapEquiv_id [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B) :
    covp.fiberMapEquiv covp b ⟨ContinuousMap.id E, rfl⟩ =
      @MulActionHom.id (FundamentalGroup B b) (p ⁻¹' {b})
      (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul :=
  covp.fiberMap_id b

/-- Extending the identity equivariant map gives the identity over-map. -/
@[simp] theorem fiberMapEquiv_symm_id [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B) :
    (covp.fiberMapEquiv covp b).symm (@MulActionHom.id (FundamentalGroup B b) (p ⁻¹' {b})
      (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul) = ⟨ContinuousMap.id E, rfl⟩ := by
  apply (covp.fiberMapEquiv covp b).symm_apply_eq.mpr
  exact (covp.fiberMapEquiv_id b).symm

variable {G : Type z} [TopologicalSpace G] {r : G → B} (covr : IsCoveringMap r)

/-- The comparison respects postcomposition by any continuous map over the base. No
local path connectedness of the intermediate or final target is required. -/
theorem fiberMapEquivOfPathConnected_comp
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (f : {f : C(E, F) // q ∘ f = p}) (g : {g : C(F, G) // r ∘ g = q}) :
    covp.fiberMapEquivOfPathConnected covr e₀ ⟨g.val.comp f.val, funext fun e ↦
      (congr_fun g.property (f.val e)).trans (congr_fun f.property e)⟩ =
      @MulActionHom.comp (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (FundamentalGroup B (p e₀)) (@id (FundamentalGroup B (p e₀)))
      (@id (FundamentalGroup B (p e₀))) (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (r ⁻¹' {p e₀}) (covr.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (covq.fiberMap covr (p e₀) g) (covp.fiberMapEquivOfPathConnected covq e₀ f) inferInstance :=
  covp.fiberMap_comp covq covr (p e₀) g f

/-- Extension commutes with postcomposition by a given continuous map over the base.
The intermediate target need not be locally path connected, since no extension out of it
is used. -/
theorem fiberMapEquivOfPathConnected_symm_postcomp
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (g : {g : C(F, G) // r ∘ g = q})
    (h : @MulActionHom (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul) :
    (covp.fiberMapEquivOfPathConnected covr e₀).symm
      (@MulActionHom.comp (FundamentalGroup B (p e₀)) (FundamentalGroup B (p e₀))
      (FundamentalGroup B (p e₀)) (@id (FundamentalGroup B (p e₀)))
      (@id (FundamentalGroup B (p e₀))) (@id (FundamentalGroup B (p e₀)))
      (p ⁻¹' {p e₀}) (covp.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (q ⁻¹' {p e₀}) (covq.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (r ⁻¹' {p e₀}) (covr.fundamentalGroupMulAction (p e₀)).toSemigroupAction.toSMul
      (covq.fiberMap covr (p e₀) g) (h) inferInstance) =
      ⟨g.val.comp ((covp.fiberMapEquivOfPathConnected covq e₀).symm h).val, funext fun e ↦
        (congr_fun g.property (((covp.fiberMapEquivOfPathConnected covq e₀).symm h).val e)).trans
          (congr_fun ((covp.fiberMapEquivOfPathConnected covq e₀).symm h).property e)⟩ := by
  apply (covp.fiberMapEquivOfPathConnected_symm_eq_iff covr e₀ _ _).mpr
  change g.val (((covp.fiberMapEquivOfPathConnected covq e₀).symm h).val e₀) =
    g.val (h ⟨e₀, rfl⟩).val
  rw [covp.fiberMapEquivOfPathConnected_symm_apply_coe covq e₀ h ⟨e₀, rfl⟩]

/-- The comparison respects postcomposition by any continuous map over the base. No
local path connectedness of the intermediate or final target is required. -/
theorem fiberMapEquiv_comp [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B)
    (f : {f : C(E, F) // q ∘ f = p}) (g : {g : C(F, G) // r ∘ g = q}) :
    covp.fiberMapEquiv covr b ⟨g.val.comp f.val, funext fun e ↦
      (congr_fun g.property (f.val e)).trans (congr_fun f.property e)⟩ =
      @MulActionHom.comp (FundamentalGroup B b) (FundamentalGroup B b)
      (FundamentalGroup B b) (@id (FundamentalGroup B b))
      (@id (FundamentalGroup B b)) (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (r ⁻¹' {b}) (covr.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (covq.fiberMap covr b g) (covp.fiberMapEquiv covq b f) inferInstance :=
  covp.fiberMap_comp covq covr b g f

/-- Extension commutes with postcomposition by a given continuous map over the base.
The intermediate target need not be locally path connected, since no extension out of it
is used. -/
theorem fiberMapEquiv_symm_postcomp [PathConnectedSpace B] [LocallyPathConnectedSpace E] (b : B)
    (g : {g : C(F, G) // r ∘ g = q})
    (h : @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul) :
    (covp.fiberMapEquiv covr b).symm
      (@MulActionHom.comp (FundamentalGroup B b) (FundamentalGroup B b)
      (FundamentalGroup B b) (@id (FundamentalGroup B b))
      (@id (FundamentalGroup B b)) (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (covp.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (q ⁻¹' {b}) (covq.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (r ⁻¹' {b}) (covr.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (covq.fiberMap covr b g) (h) inferInstance) =
      ⟨g.val.comp ((covp.fiberMapEquiv covq b).symm h).val, funext fun e ↦
        (congr_fun g.property (((covp.fiberMapEquiv covq b).symm h).val e)).trans
          (congr_fun ((covp.fiberMapEquiv covq b).symm h).property e)⟩ := by
  apply (covp.fiberMapEquiv_symm_eq_iff covr b _ _).mpr
  intro e
  change g.val (((covp.fiberMapEquiv covq b).symm h).val e.val) = g.val (h e).val
  rw [covp.fiberMapEquiv_symm_apply_coe covq b h e]

end Extension

end IsCoveringMap

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B} (cov : IsCoveringMap p)

section DeckExtension

variable {b : B}

private theorem centralizer_monodromy_apply
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b)))
    (γ : FundamentalGroup B b) (e : p ⁻¹' {b}) :
    cov.monodromy γ (α.val e) = α.val (cov.monodromy γ e) :=
  congrArg (fun σ : Equiv.Perm (p ⁻¹' {b}) ↦ σ e)
    ((Subgroup.mem_centralizer_iff.mp α.property) _ ⟨γ, rfl⟩)

private def centralizerFiberHom
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) :
    @MulActionHom (FundamentalGroup B b) (FundamentalGroup B b)
      (@id (FundamentalGroup B b))
      (p ⁻¹' {b}) (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul
      (p ⁻¹' {b}) (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul :=
  @MulActionHom.mk (FundamentalGroup B b) (FundamentalGroup B b)
    (@id (FundamentalGroup B b))
    (p ⁻¹' {b}) (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul
    (p ⁻¹' {b}) (cov.fundamentalGroupMulAction b).toSemigroupAction.toSMul
    α.val (fun γ e ↦ (cov.centralizer_monodromy_apply α γ e).symm)

private theorem centralizerFiberHom_apply
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) (e : p ⁻¹' {b}) :
    cov.centralizerFiberHom α e = α.val e :=
  rfl

/-- A commuting permutation extends by the general over-map extension, applied to the
permutation and its inverse. Whole-fiber uniqueness supplies the inverse laws. -/
private theorem exists_deck_monodromy_extension [PathConnectedSpace B] [LocallyPathConnectedSpace E]
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) :
    ∃ g : deck p, ∀ e : p ⁻¹' {b}, g • e.val = (α.val e).val := by
  obtain ⟨f, hfp, hf⟩ := cov.exists_continuousMap_monodromy_extension cov
    (cov.centralizerFiberHom α)
  obtain ⟨g, hgp, hg⟩ := cov.exists_continuousMap_monodromy_extension cov
    (cov.centralizerFiberHom (α⁻¹))
  simp only [centralizerFiberHom_apply] at hf hg
  have hgf : g.comp f = ContinuousMap.id E := by
    refine cov.eq_of_comp_eq_of_eqOn_fiber cov.isSeparatedMap
      cov.isLocalHomeomorph.isLocallyInjective (g.comp f) (ContinuousMap.id E) ?_ rfl b ?_
    · change p ∘ (g ∘ f) = p
      rw [← Function.comp_assoc, hgp, hfp]
    · intro e
      change g (f e.val) = e.val
      rw [hf e, hg (α.val e)]
      exact congrArg Subtype.val (α.val.symm_apply_apply e)
  have hfg : f.comp g = ContinuousMap.id E := by
    refine cov.eq_of_comp_eq_of_eqOn_fiber cov.isSeparatedMap
      cov.isLocalHomeomorph.isLocallyInjective (f.comp g) (ContinuousMap.id E) ?_ rfl b ?_
    · change p ∘ (f ∘ g) = p
      rw [← Function.comp_assoc, hfp, hgp]
    · intro e
      change f (g e.val) = e.val
      rw [hg e, hf ((α⁻¹).val e)]
      exact congrArg Subtype.val (α.val.apply_symm_apply e)
  let H : E ≃ₜ E :=
    { toFun := f
      invFun := g
      left_inv := fun x ↦ DFunLike.congr_fun hgf x
      right_inv := fun x ↦ DFunLike.congr_fun hfg x
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  exact ⟨⟨H, hfp⟩, hf⟩

/-- The occupied-source deck extension is the general occupied extension applied to a
commuting permutation and its inverse; no connectedness assumption on the base is used. -/
private theorem exists_deck_smul_eq_of_pathConnected
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (e₀ : E)
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm (p e₀)))) :
    ∃ g : deck p, ∀ e : p ⁻¹' {p e₀}, g • e.val = (α.val e).val := by
  obtain ⟨f, hfp, hf⟩ := cov.exists_continuousMap_monodromy_extension_of_pathConnected cov e₀
    (cov.centralizerFiberHom α)
  obtain ⟨g, hgp, hg⟩ := cov.exists_continuousMap_monodromy_extension_of_pathConnected cov e₀
    (cov.centralizerFiberHom (α⁻¹))
  simp only [centralizerFiberHom_apply] at hf hg
  let ebase : p ⁻¹' {p e₀} := ⟨e₀, rfl⟩
  have hgf : g ∘ f = id := by
    refine cov.eq_of_comp_eq (g.continuous.comp f.continuous) continuous_id ?_ e₀ ?_
    · rw [← Function.comp_assoc, hgp, hfp]
      rfl
    · change g (f ebase.val) = ebase.val
      rw [hf ebase, hg (α.val ebase)]
      exact congrArg Subtype.val (α.val.symm_apply_apply ebase)
  have hfg : f ∘ g = id := by
    refine cov.eq_of_comp_eq (f.continuous.comp g.continuous) continuous_id ?_ e₀ ?_
    · rw [← Function.comp_assoc, hfp, hgp]
      rfl
    · change f (g ebase.val) = ebase.val
      rw [hg ebase, hf ((α⁻¹).val ebase)]
      exact congrArg Subtype.val (α.val.apply_symm_apply ebase)
  let H : E ≃ₜ E :=
    { toFun := f
      invFun := g
      left_inv := congr_fun hgf
      right_inv := congr_fun hfg
      continuous_toFun := f.continuous
      continuous_invFun := g.continuous }
  exact ⟨⟨H, hfp⟩, hf⟩

end DeckExtension

/-- Restriction identifies the deck group with the centralizer of monodromy on a fiber
when the base is path connected and the total space is locally path connected. This is the
restriction comparison of May, Chapter 3, §7, p. 29, generalized to disconnected or empty
total spaces. No surjectivity or nonemptiness is assumed. -/
noncomputable def deckMonodromyEquiv [PathConnectedSpace B] [LocallyPathConnectedSpace E]
    (b : B) : deck p ≃* Subgroup.centralizer (Set.range (cov.monodromyPerm b)) :=
  MulEquiv.ofBijective (cov.deckMonodromyHom b) ⟨cov.deckMonodromyHom_injective b, by
    intro α
    obtain ⟨g, hg⟩ := cov.exists_deck_monodromy_extension α
    exact ⟨g, Subtype.ext (Equiv.ext fun e ↦ Subtype.ext (hg e))⟩⟩

/-- The forward homomorphism of the comparison is restriction to the fiber. -/
@[simp] theorem deckMonodromyEquiv_toMonoidHom [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] (b : B) :
    (cov.deckMonodromyEquiv b : deck p →*
      Subgroup.centralizer (Set.range (cov.monodromyPerm b))) = cov.deckMonodromyHom b :=
  rfl

/-- The comparison applies the original deck transformation to each fiber coordinate. -/
@[simp] theorem deckMonodromyEquiv_apply_coe [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] (b : B) (g : deck p) (e : p ⁻¹' {b}) :
    ((cov.deckMonodromyEquiv b g).val e).val = g • e.val :=
  rfl

/-- The inverse comparison extends the given permutation on every point of the fiber. -/
@[simp] theorem deckMonodromyEquiv_symm_smul [PathConnectedSpace B]
    [LocallyPathConnectedSpace E] (b : B)
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm b))) (e : p ⁻¹' {b}) :
    (cov.deckMonodromyEquiv b).symm α • e.val = (α.val e).val := by
  rw [← cov.deckMonodromyEquiv_apply_coe b, MulEquiv.apply_symm_apply]

/-- For path-connected, locally path-connected total space, restriction identifies the
deck group with the monodromy centralizer on the fiber containing a specified point.
This is the occupied-fiber form of May, Chapter 3, §7, p. 29. The base need not be path
connected or locally path connected, and the covering need not be surjective. -/
noncomputable def deckMonodromyEquivOfPathConnected [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    deck p ≃* Subgroup.centralizer (Set.range (cov.monodromyPerm (p e₀))) :=
  MulEquiv.ofBijective (cov.deckMonodromyHom (p e₀)) ⟨by
    intro g h hgh
    apply (deck.evalEmbedding cov.isSeparatedMap
      cov.isLocalHomeomorph.isLocallyInjective e₀).injective
    apply Subtype.ext
    exact congrArg (fun α ↦ (α.val ⟨e₀, rfl⟩).val) hgh, by
    intro α
    obtain ⟨g, hg⟩ := cov.exists_deck_smul_eq_of_pathConnected e₀ α
    exact ⟨g, Subtype.ext (Equiv.ext fun e ↦ Subtype.ext (hg e))⟩⟩

/-- The occupied-fiber comparison has the same restriction homomorphism. -/
@[simp] theorem deckMonodromyEquivOfPathConnected_toMonoidHom [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    (cov.deckMonodromyEquivOfPathConnected e₀ : deck p →*
      Subgroup.centralizer (Set.range (cov.monodromyPerm (p e₀)))) =
      cov.deckMonodromyHom (p e₀) :=
  rfl

/-- The occupied-fiber comparison applies the deck transformation to each coordinate. -/
@[simp] theorem deckMonodromyEquivOfPathConnected_apply_coe [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) (g : deck p) (e : p ⁻¹' {p e₀}) :
    ((cov.deckMonodromyEquivOfPathConnected e₀ g).val e).val = g • e.val :=
  rfl

/-- The inverse occupied-fiber comparison extends the permutation on the whole fiber. -/
@[simp] theorem deckMonodromyEquivOfPathConnected_symm_smul [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E)
    (α : Subgroup.centralizer (Set.range (cov.monodromyPerm (p e₀))))
    (e : p ⁻¹' {p e₀}) :
    (cov.deckMonodromyEquivOfPathConnected e₀).symm α • e.val = (α.val e).val := by
  rw [← cov.deckMonodromyEquivOfPathConnected_apply_coe e₀, MulEquiv.apply_symm_apply]

/-- Where both constructions apply, they are equal as multiplicative equivalence data:
their forward maps are the same canonical restriction. -/
theorem deckMonodromyEquiv_eq_of_pathConnected [PathConnectedSpace B] [PathConnectedSpace E]
    [LocallyPathConnectedSpace E] (e₀ : E) :
    cov.deckMonodromyEquiv (p e₀) = cov.deckMonodromyEquivOfPathConnected e₀ := by
  apply MulEquiv.ext
  intro g
  rfl

end IsCoveringMap
