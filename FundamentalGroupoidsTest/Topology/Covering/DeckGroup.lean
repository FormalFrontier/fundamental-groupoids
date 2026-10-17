/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Covering.Components
import FundamentalGroupoids.Topology.Covering.DeckGroup
import FundamentalGroupoids.Topology.Covering.DeckMonodromy

import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Covering.Deck
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Separation.Connected

/-!
# Deck transformations of the circle covering and a disconnected covering

Translation by one is a nonidentity deck transformation of the covering
`ℝ → AddCircle (1 : ℝ)`. Its value at zero is one, in the same fiber as zero.
The total space of this covering is preconnected.

For the discrete covering `Fin 3 → Unit`, transposing zero and one gives a
nonidentity deck transformation fixing two. Thus a fixed point does not force
a deck transformation to be the identity when the total space is disconnected.

The monodromy comparison restricts the same circle translation to its fiber and
recovers it from its nontrivial centralizer permutation. On the three-sheet cover,
the transposition of one and two fixes zero but remains nonidentity; the comparison
recovers this permutation without requiring connected total space. An empty cover
and a disconnected-base cover record the nonemptiness and faithfulness boundaries.
On `Bool × Bool → Bool`, the component-fiber embedding distinguishes the two points
over `false`, without a path-connected base. Constant and empty-total covers also
instantiate the embedding when the chosen raw fiber is empty.

## References

The constructions use Mathlib's `deck`, `Homeomorph.addRight`,
`Equiv.toHomeomorphOfDiscrete`, and `AddCircle.isCoveringMap_coe`.
-/

@[expose] public section

namespace SphereTopologyTest

private def realCircleProjection : ℝ → AddCircle (1 : ℝ) := (↑)

private theorem realCircleProjection_covering : IsCoveringMap realCircleProjection :=
  AddCircle.isCoveringMap_coe (1 : ℝ)

private theorem real_preconnected : PreconnectedSpace ℝ := inferInstance

/-- Translation by one, as a deck transformation of the circle covering. -/
private def realCircleTranslation : deck realCircleProjection :=
  ⟨Homeomorph.addRight (1 : ℝ), by
    funext x
    exact AddCircle.coe_add_period (1 : ℝ) x⟩

private theorem realCircleTranslation_smul (x : ℝ) :
    realCircleTranslation • x = x + 1 := rfl

private theorem realCircleTranslation_zero : realCircleTranslation • (0 : ℝ) = 1 := by
  rw [realCircleTranslation_smul, zero_add]

private theorem realCircleTranslation_ne_one : realCircleTranslation ≠ 1 := by
  intro h
  have hzero := realCircleTranslation_zero
  rw [h, one_smul] at hzero
  exact zero_ne_one hzero

private theorem realCircleTranslation_projection (x : ℝ) :
    realCircleProjection (realCircleTranslation • x) = realCircleProjection x :=
  deck.proj_smul realCircleTranslation x

/-- The origin in the point fiber of the circle covering over zero. -/
private def realCircleFiberOrigin : realCircleProjection ⁻¹' {0} :=
  ⟨0, AddCircle.coe_zero (1 : ℝ)⟩

/-- The translate of the origin, in the same point fiber. -/
private def realCircleFiberTranslatedOrigin : realCircleProjection ⁻¹' {0} :=
  ⟨realCircleTranslation • (0 : ℝ),
    (realCircleTranslation_projection 0).trans realCircleFiberOrigin.property⟩

private theorem realCircleFiberTranslatedOrigin_val :
    realCircleFiberTranslatedOrigin.val = 1 :=
  realCircleTranslation_zero

private theorem realCircleFiberTranslatedOrigin_ne_origin :
    realCircleFiberTranslatedOrigin ≠ realCircleFiberOrigin := by
  intro h
  have hval := congrArg Subtype.val h
  rw [realCircleFiberTranslatedOrigin_val] at hval
  exact one_ne_zero hval

private def threeSheetProjection (_ : Fin 3) : Unit := ()

private theorem threeSheetProjection_covering : IsCoveringMap threeSheetProjection :=
  IsCoveringMap.of_discreteTopology _

/-- The transposition of the first two sheets of the three-sheet covering. -/
private def threeSheetTransposition : deck threeSheetProjection :=
  ⟨(Equiv.swap (0 : Fin 3) 1).toHomeomorphOfDiscrete, by funext x; rfl⟩

private theorem threeSheetTransposition_fixes_two :
    threeSheetTransposition • (2 : Fin 3) = 2 := by
  change Equiv.swap (0 : Fin 3) 1 2 = 2
  decide

private theorem threeSheetTransposition_moves_zero :
    threeSheetTransposition • (0 : Fin 3) = 1 := by
  change Equiv.swap (0 : Fin 3) 1 0 = 1
  decide

private theorem threeSheetTransposition_ne_one : threeSheetTransposition ≠ 1 := by
  intro h
  have hzero := threeSheetTransposition_moves_zero
  rw [h, one_smul] at hzero
  exact (by decide : (0 : Fin 3) ≠ 1) hzero

private theorem threeSheet_not_preconnected : ¬ PreconnectedSpace (Fin 3) := by
  intro h
  let := h
  have hsub := PreconnectedSpace.trivial_of_discrete (X := Fin 3)
  exact (by decide : (0 : Fin 3) ≠ 1) (hsub.elim 0 1)

/-- The fiber action sends the origin to its translated point. -/
private theorem realCircleTranslation_smul_fiberOrigin :
    realCircleTranslation • realCircleFiberOrigin = realCircleFiberTranslatedOrigin := by
  apply Subtype.ext
  exact (deck.coe_fiber_smul realCircleTranslation realCircleFiberOrigin).trans rfl

/-- Evaluation at zero records the nonidentity translation at the point with value one. -/
private theorem realCircleTranslation_eval_origin :
    (deck.evalEmbedding realCircleProjection_covering.isSeparatedMap
      realCircleProjection_covering.isLocalHomeomorph.isLocallyInjective (0 : ℝ)
      realCircleTranslation : ℝ) = 1 := by
  simpa only [deck.coe_evalEmbedding_apply] using realCircleTranslation_zero

/-- A nonidentity translation of the circle covering has no fixed point. -/
private theorem realCircleTranslation_no_fixed_point (x : ℝ) :
    realCircleTranslation • x ≠ x := by
  intro hx
  exact realCircleTranslation_ne_one
    (deck.eq_one_of_smul_eq realCircleProjection_covering.isSeparatedMap
      realCircleProjection_covering.isLocalHomeomorph.isLocallyInjective hx)

/-- A deck transformation of the circle covering fixing the origin is the identity. -/
private theorem realCircleDeck_eq_one_of_fixed_origin (g : deck realCircleProjection)
    (hg : g • (0 : ℝ) = 0) : g = 1 :=
  realCircleProjection_covering.eq_one_of_deck_smul_eq hg

section Monodromy

private instance realCircle_pathConnected : PathConnectedSpace (AddCircle (1 : ℝ)) :=
  QuotientAddGroup.mk_surjective.pathConnectedSpace realCircleProjection_covering.continuous

/-- The translation permutation on the occupied fiber, using the existing fiber action. -/
private noncomputable def realCircleCentralizerTranslation : Subgroup.centralizer
    (Set.range (realCircleProjection_covering.monodromyPerm (realCircleProjection 0))) :=
  realCircleProjection_covering.deckMonodromyHom (realCircleProjection 0) realCircleTranslation

private theorem realCircleCentralizerTranslation_moves_origin :
    (realCircleCentralizerTranslation.val ⟨0, rfl⟩).val = 1 := by
  simpa only [realCircleCentralizerTranslation,
    IsCoveringMap.deckMonodromyHom_apply_coe] using realCircleTranslation_zero

private theorem realCircleCentralizerTranslation_ne_one :
    realCircleCentralizerTranslation ≠ 1 := by
  intro h
  have he := realCircleCentralizerTranslation_moves_origin
  rw [h] at he
  exact zero_ne_one he

/-- Both comparison constructors act on the same nonidentity translation. -/
example :
    ((realCircleProjection_covering.deckMonodromyEquiv (realCircleProjection 0)
      realCircleTranslation).val ⟨0, rfl⟩).val = 1 ∧
    ((realCircleProjection_covering.deckMonodromyEquivOfPathConnected 0
      realCircleTranslation).val ⟨0, rfl⟩).val = 1 := by
  constructor <;> simpa only [IsCoveringMap.deckMonodromyEquiv_apply_coe,
    IsCoveringMap.deckMonodromyEquivOfPathConnected_apply_coe] using realCircleTranslation_zero

private theorem realCircleComparisons_agree :
    realCircleProjection_covering.deckMonodromyEquiv (realCircleProjection 0) =
      realCircleProjection_covering.deckMonodromyEquivOfPathConnected 0 :=
  realCircleProjection_covering.deckMonodromyEquiv_eq_of_pathConnected 0

/-- The inverse comparison recovers the translation from its nontrivial fiber permutation. -/
example :
    (realCircleProjection_covering.deckMonodromyEquiv (realCircleProjection 0)).symm
      realCircleCentralizerTranslation = realCircleTranslation ∧
    (realCircleProjection_covering.deckMonodromyEquivOfPathConnected 0).symm
      realCircleCentralizerTranslation = realCircleTranslation := by
  have h : (realCircleProjection_covering.deckMonodromyEquiv (realCircleProjection 0)).symm
      realCircleCentralizerTranslation = realCircleTranslation := by
    apply realCircleProjection_covering.deck_ext (realCircleProjection 0)
    intro e
    rw [IsCoveringMap.deckMonodromyEquiv_symm_smul]
    exact realCircleProjection_covering.deckMonodromyHom_apply_coe
      (realCircleProjection 0) realCircleTranslation e
  exact ⟨h, by rw [← realCircleComparisons_agree]; exact h⟩

/-- Inverse coordinates give one rather than zero for this centralizer element. -/
example :
    (realCircleProjection_covering.deckMonodromyEquiv (realCircleProjection 0)).symm
      realCircleCentralizerTranslation • (0 : ℝ) = 1 ∧
    (realCircleProjection_covering.deckMonodromyEquivOfPathConnected 0).symm
      realCircleCentralizerTranslation • (0 : ℝ) = 1 := by
  constructor
  · exact (realCircleProjection_covering.deckMonodromyEquiv_symm_smul (realCircleProjection 0)
      realCircleCentralizerTranslation ⟨0, rfl⟩).trans realCircleCentralizerTranslation_moves_origin
  · exact (realCircleProjection_covering.deckMonodromyEquivOfPathConnected_symm_smul 0
      realCircleCentralizerTranslation ⟨0, rfl⟩).trans realCircleCentralizerTranslation_moves_origin

/-- The comparison inherits multiplicativity and inverse compatibility from `MulEquiv`. -/
example : realCircleProjection_covering.deckMonodromyEquiv (realCircleProjection 0)
    (realCircleTranslation * realCircleTranslation⁻¹) = 1 := by
  rw [map_mul, map_inv, mul_inv_cancel]

/-- Unlike the first transposition above, this one fixes zero and exchanges one and two. -/
private def threeSheetLastTransposition : deck threeSheetProjection :=
  ⟨(Equiv.swap (1 : Fin 3) 2).toHomeomorphOfDiscrete, by funext x; rfl⟩

private def threeSheetLastFiberPermutation : Equiv.Perm (threeSheetProjection ⁻¹' {()}) :=
  threeSheetLastTransposition.val.toEquiv.subtypeEquiv (fun _ ↦ Iff.rfl)

private def threeSheetCentralizerTransposition : Subgroup.centralizer
    (Set.range (threeSheetProjection_covering.monodromyPerm ())) :=
  ⟨threeSheetLastFiberPermutation, by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨γ, rfl⟩
    rw [Subsingleton.elim γ 1, map_one, one_mul, mul_one]⟩

private theorem threeSheetCentralizerTransposition_apply (e : threeSheetProjection ⁻¹' {()}) :
    (threeSheetCentralizerTransposition.val e).val = threeSheetLastTransposition • e.val :=
  rfl

example : threeSheetLastTransposition • (0 : Fin 3) = 0 ∧
    threeSheetLastTransposition ≠ 1 := by
  constructor
  · change Equiv.swap (1 : Fin 3) 2 0 = 0
    decide
  · intro h
    have he := congrArg (fun g : deck threeSheetProjection ↦ g • (1 : Fin 3)) h
    exact (by decide : (2 : Fin 3) ≠ 1) he

/-- The arbitrary-total comparison is usable on a non-path-connected total space. -/
example : ((threeSheetProjection_covering.deckMonodromyEquiv ()
    threeSheetLastTransposition).val ⟨1, rfl⟩).val = 2 := by
  rw [IsCoveringMap.deckMonodromyEquiv_apply_coe]
  exact Equiv.swap_apply_left (1 : Fin 3) 2

/-- The inverse acts on the independently specified fiber permutation, without unfolding lifts. -/
example : (threeSheetProjection_covering.deckMonodromyEquiv ()).symm
    threeSheetCentralizerTransposition = threeSheetLastTransposition := by
  apply threeSheetProjection_covering.deck_ext ()
  intro e
  rw [IsCoveringMap.deckMonodromyEquiv_symm_smul,
    threeSheetCentralizerTransposition_apply]

example : (threeSheetProjection_covering.deckMonodromyEquiv ()).symm
    threeSheetCentralizerTransposition • (1 : Fin 3) = 2 := by
  exact (threeSheetProjection_covering.deckMonodromyEquiv_symm_smul ()
    threeSheetCentralizerTransposition ⟨1, rfl⟩).trans (Equiv.swap_apply_left _ _)

/-- The empty cover comparison requires neither a total-space point nor an inhabited fiber. -/
example : ((IsCoveringMap.of_isEmpty (Empty.elim : Empty → Unit)).deckMonodromyEquiv ()).symm
    1 = 1 :=
  map_one _

private def twoFiberProjection : Bool × Bool → Bool := Prod.fst

private theorem twoFiberProjection_covering : IsCoveringMap twoFiberProjection :=
  IsCoveringMap.of_discreteTopology _

/-- Orbit classes over `false` map into the component-map fiber, not all total components. -/
private noncomputable def falseFiberComponentEmbedding :=
  twoFiberProjection_covering.monodromyOrbitEmbeddingZerothHomotopyFiber false

private theorem falseFiberComponentEmbedding_apply (s : Bool) :
    (falseFiberComponentEmbedding
      (Quotient.mk _ ⟨(false, s), rfl⟩)).val = ZerothHomotopy.mk (false, s) :=
  twoFiberProjection_covering.monodromyOrbitEmbeddingZerothHomotopyFiber_val_apply false
    ⟨(false, s), rfl⟩

/-- The two points over `false` have distinct component-fiber images. -/
private theorem falseFiberComponentEmbedding_distinct :
    falseFiberComponentEmbedding (Quotient.mk _ ⟨(false, false), rfl⟩) ≠
      falseFiberComponentEmbedding (Quotient.mk _ ⟨(false, true), rfl⟩) := by
  intro h
  have hc := congrArg Subtype.val h
  rw [falseFiberComponentEmbedding_apply, falseFiberComponentEmbedding_apply] at hc
  obtain ⟨γ⟩ := Quotient.exact hc
  have he : γ 0 = γ 1 := PreconnectedSpace.constant inferInstance γ.continuous
  have hbad : (false, false) = (false, true) := γ.source.symm.trans (he.trans γ.target)
  cases congrArg Prod.snd hbad

/-- Every component over the component of `false` comes from a fiber-point orbit. -/
private theorem falseFiberComponentEmbedding_surjective :
    Function.Surjective falseFiberComponentEmbedding :=
  twoFiberProjection_covering.monodromyOrbitEmbeddingZerothHomotopyFiber_surjective false

/-- The canonical cover maps the path component of a point onto its image component. -/
private theorem twoFiberProjection_image_pathComponent :
    twoFiberProjection '' pathComponent (false, false) =
      pathComponent (twoFiberProjection (false, false)) :=
  twoFiberProjection_covering.image_pathComponent (false, false)

/-- The total space is nonempty, but the point fiber over `true` is empty. -/
private noncomputable def emptyImageComponentEmbedding :=
  IsCoveringMap.monodromyOrbitEmbeddingZerothHomotopyFiber
    (IsCoveringMap.of_discreteTopology (fun _ : Bool ↦ false)) true

/-- An empty total space still has its canonical orbit-to-component-fiber embedding. -/
private noncomputable def emptyTotalComponentEmbedding :=
  IsCoveringMap.monodromyOrbitEmbeddingZerothHomotopyFiber
    (IsCoveringMap.of_isEmpty (Empty.elim : Empty → Bool)) false

/-- Swap only the points over true, leaving the entire false fiber fixed. -/
private def trueFiberTransposition : deck twoFiberProjection :=
  ⟨(Equiv.swap (true, false) (true, true)).toHomeomorphOfDiscrete, by
    funext x
    change (Equiv.swap (true, false) (true, true) x).1 = x.1
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;> decide⟩

private theorem trueFiberTransposition_fixes_false (e : twoFiberProjection ⁻¹' {false}) :
    trueFiberTransposition • e.val = e.val := by
  obtain ⟨⟨a, b⟩, he⟩ := e
  change a = false at he
  subst a
  cases b <;> decide

/-- Restriction to one fiber can miss a different base component, so it need not be
faithful without base path connectedness. Only the all-cover homomorphism, not an
equivalence, is used here. -/
example : twoFiberProjection_covering.deckMonodromyHom false trueFiberTransposition = 1 ∧
    trueFiberTransposition ≠ 1 := by
  constructor
  · apply Subtype.ext
    apply Equiv.ext
    intro e
    apply Subtype.ext
    exact trueFiberTransposition_fixes_false e
  · intro h
    have he := congrArg (fun g : deck twoFiberProjection ↦ g • (true, false)) h
    exact (by decide : (true, true) ≠ (true, false)) he

end Monodromy

end SphereTopologyTest
