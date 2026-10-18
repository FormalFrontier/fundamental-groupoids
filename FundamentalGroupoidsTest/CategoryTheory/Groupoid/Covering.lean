/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.CategoryTheory.Groupoid.Covering
import FundamentalGroupoids.CategoryTheory.Groupoid.Elements
import Mathlib.Algebra.Group.Action.End
import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.Combinatorics.Quiver.Covering

/-!
# The permutation action groupoid as a covering

The projection from the action groupoid of permutations of `Bool` to its single-object
groupoid is a covering of quivers. Its fiber contains the distinct points corresponding
to `false` and `true`, and the transposition labels an arrow between them. Uniqueness
of lifts identifies its canonical monodromy with the permutation action. The groupoid
structure and connectedness are supplied by Mathlib's action-category instances.

The projection from the permutation action groupoid of the empty type also gives a
covering, with empty fiber.

## References

These examples use Mathlib's formalizations in `Mathlib.CategoryTheory.Action`,
`Mathlib.CategoryTheory.FiberedCategory.Fiber`, and `Mathlib.Combinatorics.Quiver.Covering`.
-/

namespace CategoryTheory.ActionCategory

/-- The label of an outgoing arrow determines its target and the whole arrow. Reversal
then gives the corresponding bijection on incoming arrows. -/
private theorem projection_isCovering.{uG, uX} (G : Type uG) (X : Type uX)
    [Group G] [MulAction G X] : (π G X).toPrefunctor.IsCovering := by
  exact Functor.Elements.π_isCovering (actionAsFunctor G X)

private abbrev boolProjection :
    ActionCategory (Equiv.Perm Bool) Bool ⥤ SingleObj (Equiv.Perm Bool) :=
  π (Equiv.Perm Bool) Bool

private theorem boolProjection_isCovering : boolProjection.toPrefunctor.IsCovering :=
  projection_isCovering (Equiv.Perm Bool) Bool

/-- Connectedness here is an input supplied by the permutation action, independently
of any action constructed from the covering. -/
private theorem boolActionCategory_isConnected :
    IsConnected (ActionCategory (Equiv.Perm Bool) Bool) :=
  inferInstance

private def falseFiber : boolProjection.Fiber (SingleObj.star (Equiv.Perm Bool)) :=
  ⟨objEquiv (Equiv.Perm Bool) Bool false, π_obj _ _ _⟩

private def trueFiber : boolProjection.Fiber (SingleObj.star (Equiv.Perm Bool)) :=
  ⟨objEquiv (Equiv.Perm Bool) Bool true, π_obj _ _ _⟩

private theorem falseFiber_ne_trueFiber : falseFiber ≠ trueFiber := by
  intro h
  have hbool : false = true :=
    congrArg (fun e : boolProjection.Fiber (SingleObj.star (Equiv.Perm Bool)) => e.1.back) h
  cases hbool

private def swapLoop : Aut (SingleObj.star (Equiv.Perm Bool)) :=
  (Groupoid.isoEquivHom _ _).symm
    (SingleObj.toEnd (Equiv.Perm Bool) (Equiv.swap false true))

private def swapArrow : falseFiber.1 ⟶ trueFiber.1 :=
  Functor.Elements.homMk (Equiv.swap false true) (by
    change (Equiv.swap false true) false = true
    exact Equiv.swap_apply_left false true)

private theorem swapArrow_label : swapArrow.hom = Equiv.swap false true := rfl

private theorem swapArrow_projection : boolProjection.map swapArrow = swapLoop.hom := rfl

private theorem swapArrow_endpoint :
    (show Equiv.Perm Bool from swapArrow.hom) • falseFiber.1.back = trueFiber.1.back :=
  swapArrow.map_val

/-- Canonical monodromy along the transposition sends the false fiber point to the true one. -/
private theorem boolMonodromy_swap :
    (boolProjection.monodromyMulAction boolProjection_isCovering
      (SingleObj.star (Equiv.Perm Bool))).toSemigroupAction.toSMul.smul
        swapLoop falseFiber = trueFiber := by
  have hswap : Quiver.Star.mk swapArrow =
      boolProjection.coveringLift boolProjection_isCovering swapLoop.hom falseFiber := by
    apply boolProjection.coveringLift_unique boolProjection_isCovering swapLoop.hom falseFiber
    change (⟨SingleObj.star (Equiv.Perm Bool), boolProjection.map swapArrow⟩ :
        Quiver.Star (SingleObj.star (Equiv.Perm Bool))) =
      ⟨SingleObj.star (Equiv.Perm Bool), eqToHom falseFiber.property ≫ swapLoop.hom⟩
    rw [swapArrow_projection, eqToHom_refl, Category.id_comp]
  rw [boolProjection.monodromyMulAction_smul boolProjection_isCovering]
  apply Subtype.ext
  exact (boolProjection.coveringLiftTarget_val boolProjection_isCovering
    swapLoop.hom falseFiber).trans (congrArg Sigma.fst hswap).symm

/-- The pretransitivity statement specializes to the connected permutation action groupoid. -/
private theorem boolMonodromy_isPretransitive :
    @MulAction.IsPretransitive (Aut (SingleObj.star (Equiv.Perm Bool)))
      (boolProjection.Fiber (SingleObj.star (Equiv.Perm Bool)))
      (boolProjection.monodromyMulAction boolProjection_isCovering
        (SingleObj.star (Equiv.Perm Bool))).toSemigroupAction.toSMul := by
  have : @IsPreconnected (ActionCategory (Equiv.Perm Bool) Bool)
      (inferInstance : Groupoid.{0} (ActionCategory (Equiv.Perm Bool) Bool)).toCategory :=
    @IsConnected.toIsPreconnected (ActionCategory (Equiv.Perm Bool) Bool)
      (inferInstance : Groupoid.{0} (ActionCategory (Equiv.Perm Bool) Bool)).toCategory
      boolActionCategory_isConnected
  exact boolProjection.monodromyMulAction_isPretransitive boolProjection_isCovering
    (SingleObj.star (Equiv.Perm Bool))

/-- The covering condition does not require a nonempty fiber. -/
private theorem emptyProjection_covering_empty_fiber :
    (π (Equiv.Perm Empty) Empty).toPrefunctor.IsCovering ∧
      IsEmpty ((π (Equiv.Perm Empty) Empty).Fiber (SingleObj.star (Equiv.Perm Empty))) := by
  refine ⟨projection_isCovering (Equiv.Perm Empty) Empty, ⟨?_⟩⟩
  intro e
  exact Empty.elim e.1.back

private theorem boolFiber_eq_false_or_true
    (x : boolProjection.Fiber (SingleObj.star (Equiv.Perm Bool))) :
    x = falseFiber ∨ x = trueFiber := by
  cases h : x.1.back with
  | false =>
    left
    apply Subtype.ext
    apply (objEquiv (Equiv.Perm Bool) Bool).symm.injective
    change x.1.back = false
    exact h
  | true =>
    right
    apply Subtype.ext
    apply (objEquiv (Equiv.Perm Bool) Bool).symm.injective
    change x.1.back = true
    exact h

/-- The canonical monodromy on the strict Bool fiber is pretransitive: every point is
either the false point or its image under the transposition. The orbit criterion
`MulAction.IsPretransitive.of_orbit` is from Chris Hughes and Yury Kudryashov's
`Mathlib.Algebra.Group.Action.Pretransitive`. -/
private theorem boolProjection_monodromy_isPretransitive
    (hP : (π (Equiv.Perm Bool) Bool).toPrefunctor.IsCovering) :
    @MulAction.IsPretransitive (Aut (SingleObj.star (Equiv.Perm Bool)))
      ((π (Equiv.Perm Bool) Bool).Fiber (SingleObj.star (Equiv.Perm Bool)))
      (((π (Equiv.Perm Bool) Bool).monodromyMulAction hP
        (SingleObj.star (Equiv.Perm Bool))).toSemigroupAction.toSMul) := by
  let : MulAction (Aut (SingleObj.star (Equiv.Perm Bool)))
      (boolProjection.Fiber (SingleObj.star (Equiv.Perm Bool))) :=
    boolProjection.monodromyMulAction hP (SingleObj.star (Equiv.Perm Bool))
  apply MulAction.IsPretransitive.of_orbit (x₀ := falseFiber)
  intro x
  rcases boolFiber_eq_false_or_true x with rfl | rfl
  · exact ⟨1, by simp only [one_smul]⟩
  · exact ⟨swapLoop, boolMonodromy_swap⟩

/-- The canonical monodromy on the strict fiber of the permutation action on `Empty`
is pretransitive, since that fiber has no points. -/
private theorem emptyProjection_monodromy_isPretransitive
    (hP : (π (Equiv.Perm Empty) Empty).toPrefunctor.IsCovering) :
    @MulAction.IsPretransitive (Aut (SingleObj.star (Equiv.Perm Empty)))
      ((π (Equiv.Perm Empty) Empty).Fiber (SingleObj.star (Equiv.Perm Empty)))
      (((π (Equiv.Perm Empty) Empty).monodromyMulAction hP
        (SingleObj.star (Equiv.Perm Empty))).toSemigroupAction.toSMul) := by
  rw [MulAction.isPretransitive_iff]
  intro x y
  exact Empty.elim x.1.back

/-- Pretransitive monodromy on the two-point fiber gives preconnectedness of the
permutation action category. -/
private theorem boolActionCategory_isPreconnected :
    IsPreconnected (ActionCategory (Equiv.Perm Bool) Bool) := by
  have hP : (π (Equiv.Perm Bool) Bool).toPrefunctor.IsCovering :=
    projection_isCovering (Equiv.Perm Bool) Bool
  exact CategoryTheory.Functor.isPreconnected_of_monodromyMulAction_isPretransitive
    (π (Equiv.Perm Bool) Bool) hP (SingleObj.star (Equiv.Perm Bool))
    (boolProjection_monodromy_isPretransitive hP)

/-- Pretransitive monodromy on the empty fiber gives preconnectedness of the empty
permutation action category, without a nonemptiness assumption. -/
private theorem emptyActionCategory_isPreconnected :
    IsPreconnected (ActionCategory (Equiv.Perm Empty) Empty) := by
  have hP : (π (Equiv.Perm Empty) Empty).toPrefunctor.IsCovering :=
    projection_isCovering (Equiv.Perm Empty) Empty
  exact CategoryTheory.Functor.isPreconnected_of_monodromyMulAction_isPretransitive
    (π (Equiv.Perm Empty) Empty) hP (SingleObj.star (Equiv.Perm Empty))
    (emptyProjection_monodromy_isPretransitive hP)

end CategoryTheory.ActionCategory

/-!
## Recovering values in the original fibers

The characteristic API of `fiberEquiv` recovers the two Boolean values. The lift
and monodromy comparisons send the false fiber point along the transposition to
the true value and also specialize to the empty permutation action. Neither
connectedness nor pretransitivity is a premise of these comparisons.
-/

namespace CategoryTheory.ActionCategory

/-- Recovering the value of the original false fiber point. -/
private theorem falseFiber_fiberEquiv :
    Functor.Elements.fiberEquiv (actionAsFunctor (Equiv.Perm Bool) Bool)
      (SingleObj.star (Equiv.Perm Bool)) falseFiber = false := by
  erw [Functor.Elements.fiberEquiv_apply]
  exact (objEquiv (Equiv.Perm Bool) Bool).symm_apply_apply false

/-- Recovering the value of the original true fiber point. -/
private theorem trueFiber_fiberEquiv :
    Functor.Elements.fiberEquiv (actionAsFunctor (Equiv.Perm Bool) Bool)
      (SingleObj.star (Equiv.Perm Bool)) trueFiber = true := by
  erw [Functor.Elements.fiberEquiv_apply]
  exact (objEquiv (Equiv.Perm Bool) Bool).symm_apply_apply true

/-- Both comparisons send the original false fiber
point along the original transposition to the value `true`. The scalar map is
computed from the original arrow label, not assumed as a recovery law. -/
private theorem boolFiberEquiv_swap :
    Functor.Elements.fiberEquiv (actionAsFunctor (Equiv.Perm Bool) Bool)
        (SingleObj.star (Equiv.Perm Bool))
        (boolProjection.coveringLiftTarget boolProjection_isCovering
          swapLoop.hom falseFiber) = true ∧
      Functor.Elements.fiberEquiv (actionAsFunctor (Equiv.Perm Bool) Bool)
        (SingleObj.star (Equiv.Perm Bool))
        (@SMul.smul (Aut (SingleObj.star (Equiv.Perm Bool)))
          (boolProjection.Fiber (SingleObj.star (Equiv.Perm Bool)))
          (boolProjection.monodromyMulAction boolProjection_isCovering
            (SingleObj.star (Equiv.Perm Bool))).toSemigroupAction.toSMul
          swapLoop falseFiber) = true := by
  have hmap :
      (actionAsFunctor (Equiv.Perm Bool) Bool).map swapLoop.hom
        (Functor.Elements.fiberEquiv (actionAsFunctor (Equiv.Perm Bool) Bool)
          (SingleObj.star (Equiv.Perm Bool)) falseFiber) = true := by
    rw [falseFiber_fiberEquiv, ← swapArrow_projection]
    change (show Equiv.Perm Bool from swapArrow.hom) false = true
    rw [swapArrow_label]
    exact Equiv.swap_apply_left false true
  constructor
  · exact (Functor.Elements.fiberEquiv_coveringLiftTarget
      (actionAsFunctor (Equiv.Perm Bool) Bool) boolProjection_isCovering
      swapLoop.hom falseFiber).trans hmap
  · exact (Functor.Elements.fiberEquiv_monodromyMulAction_smul
      (actionAsFunctor (Equiv.Perm Bool) Bool) boolProjection_isCovering
      (SingleObj.star (Equiv.Perm Bool)) swapLoop falseFiber).trans hmap

/-- Both comparisons specialize universally to the
original empty permutation model, using its canonical covering supplier. No point
of the empty fiber, or nonemptiness hypothesis, is supplied. -/
private theorem emptyFiberEquiv_lift_monodromy
    (f : SingleObj.star (Equiv.Perm Empty) ⟶ SingleObj.star (Equiv.Perm Empty))
    (a : Aut (SingleObj.star (Equiv.Perm Empty)))
    (x : (π (Equiv.Perm Empty) Empty).Fiber (SingleObj.star (Equiv.Perm Empty))) :
    Functor.Elements.fiberEquiv (actionAsFunctor (Equiv.Perm Empty) Empty)
        (SingleObj.star (Equiv.Perm Empty))
        ((π (Equiv.Perm Empty) Empty).coveringLiftTarget
          (Functor.Elements.π_isCovering (actionAsFunctor (Equiv.Perm Empty) Empty))
          f x) =
      (actionAsFunctor (Equiv.Perm Empty) Empty).map f
        (Functor.Elements.fiberEquiv (actionAsFunctor (Equiv.Perm Empty) Empty)
          (SingleObj.star (Equiv.Perm Empty)) x) ∧
      Functor.Elements.fiberEquiv (actionAsFunctor (Equiv.Perm Empty) Empty)
        (SingleObj.star (Equiv.Perm Empty))
        (@SMul.smul (Aut (SingleObj.star (Equiv.Perm Empty)))
          ((π (Equiv.Perm Empty) Empty).Fiber (SingleObj.star (Equiv.Perm Empty)))
          ((π (Equiv.Perm Empty) Empty).monodromyMulAction
            (Functor.Elements.π_isCovering (actionAsFunctor (Equiv.Perm Empty) Empty))
            (SingleObj.star (Equiv.Perm Empty))).toSemigroupAction.toSMul a x) =
      (actionAsFunctor (Equiv.Perm Empty) Empty).map a.hom
        (Functor.Elements.fiberEquiv (actionAsFunctor (Equiv.Perm Empty) Empty)
          (SingleObj.star (Equiv.Perm Empty)) x) := by
  constructor
  · exact Functor.Elements.fiberEquiv_coveringLiftTarget
      (actionAsFunctor (Equiv.Perm Empty) Empty)
      (Functor.Elements.π_isCovering (actionAsFunctor (Equiv.Perm Empty) Empty)) f x
  · exact Functor.Elements.fiberEquiv_monodromyMulAction_smul
      (actionAsFunctor (Equiv.Perm Empty) Empty)
      (Functor.Elements.π_isCovering (actionAsFunctor (Equiv.Perm Empty) Empty))
      (SingleObj.star (Equiv.Perm Empty)) a x

end CategoryTheory.ActionCategory
