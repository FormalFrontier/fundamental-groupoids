/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.CategoryTheory.Groupoid.Covering
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
  let baseGroupoid : Groupoid.{uG} (SingleObj G) := SingleObj.groupoid G
  let actionGroupoid : Groupoid.{uG} (ActionCategory G X) :=
    @Functor.Elements.groupoid (SingleObj G) baseGroupoid (actionAsFunctor G X)
  refine @Prefunctor.isCovering_of_bijective_star
    (ActionCategory G X) actionGroupoid.toCategory.toCategoryStruct.toQuiver
    (SingleObj G) baseGroupoid.toCategory.toCategoryStruct.toQuiver
    (π G X).toPrefunctor
    (@groupoidHasInvolutiveReverse (ActionCategory G X) actionGroupoid)
    (@groupoidHasInvolutiveReverse (SingleObj G) baseGroupoid)
    (@functorMapReverse (ActionCategory G X) actionGroupoid
      (SingleObj G) baseGroupoid (π G X)) ?_
  intro x
  constructor
  · rintro ⟨y, f⟩ ⟨z, g⟩ h
    have hfg : f.hom = g.hom :=
      congrArg (fun s : Quiver.Star ((π G X).obj x) => (show G from s.2)) h
    have hyz : y = z := by
      apply (objEquiv G X).symm.injective
      change y.back = z.back
      calc
        y.back = f.hom • x.back := f.map_val.symm
        _ = g.hom • x.back := congrArg (fun a : G => a • x.back) hfg
        _ = z.back := g.map_val
    subst z
    have hhom : f = g := Functor.Elements.hom_ext hfg
    cases hhom
    rfl
  · rintro ⟨b, g⟩
    cases b
    refine ⟨⟨(g • x.back : X), Functor.Elements.homMk g rfl⟩, ?_⟩
    rfl

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

end CategoryTheory.ActionCategory
