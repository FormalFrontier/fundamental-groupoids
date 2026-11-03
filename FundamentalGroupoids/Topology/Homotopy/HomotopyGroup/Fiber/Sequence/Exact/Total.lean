/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence.Exact.Transport
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Exactness at the total-space terms of the homotopy-fiber sequence

In every degree `3n + 1`, including `n = 0`, the incoming differential has
range equal to the fiber of the outgoing differential over the distinguished
point. The proof transports pointed-set exactness of homotopy-fiber projection
through the public term isomorphisms and differential application laws.
-/

@[expose] public section

open CategoryTheory

namespace HomotopyGroup

/-- The homotopy-fiber sequence is exact at every total-space term.
This includes the term of path components and requires no group structure
on that term. The auxiliary lift universe is the first universe parameter. -/
theorem homotopyFiberSequence_exact_total.{v, uE, uB}
    {E : Type uE} {B : Type uB} [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (n : ℕ) :
    Set.range ((homotopyFiberSequence.{v} f b e₀ h).d (3 * n + 2) (3 * n + 1)).toFun =
      ((homotopyFiberSequence.{v} f b e₀ h).d (3 * n + 1) (3 * n)).toFun ⁻¹'
        {((homotopyFiberSequence.{v} f b e₀ h).X (3 * n)).point} := by
  let S := homotopyFiberSequence.{v} f b e₀ h
  let iF := homotopyFiberSequenceFiberIso.{v} f b e₀ h n
  let iE := homotopyFiberSequenceTotalIso.{v} f b e₀ h n
  let iB := homotopyFiberSequenceBaseIso.{v} f b e₀ h n
  let cF := (((forget Pointed).mapIso iF).toEquiv).trans Equiv.ulift
  let cE := (((forget Pointed).mapIso iE).toEquiv).trans Equiv.ulift
  let cB := (((forget Pointed).mapIso iB).toEquiv).trans Equiv.ulift
  have hf (x : S.X (3 * n + 2)) :
      cE (S.d (3 * n + 2) (3 * n + 1) x) =
        mapFun (Fin n) (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
          (ContinuousMap.HomotopyFiber.point_const e₀ h) (cF x) := by
    have hx : iF.inv.toFun (iF.hom.toFun x) = x :=
      (((forget Pointed).mapIso iF).toEquiv).symm_apply_apply x
    have hd := homotopyFiberSequence_d_total_apply.{v} f b e₀ h n (iF.hom.toFun x)
    rw [hx] at hd
    exact congrArg ULift.down hd
  have hg (y : S.X (3 * n + 1)) :
      cB (S.d (3 * n + 1) (3 * n) y) = mapFun (Fin n) f h (cE y) := by
    have hy : iE.inv.toFun (iE.hom.toFun y) = y :=
      (((forget Pointed).mapIso iE).toEquiv).symm_apply_apply y
    have hd := homotopyFiberSequence_d_base_apply.{v} f b e₀ h n (iE.hom.toFun y)
    rw [hy] at hd
    exact congrArg ULift.down hd
  have hp : cB (S.X (3 * n)).point =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) B b) := by
    change (iB.hom.toFun (S.X (3 * n)).point).down = _
    rw [iB.hom.map_point]
  apply Function.range_eq_preimage_singleton_of_coordinates
    cF cE cB cF.surjective cE.injective cB.injective hf hg (S.X (3 * n)).point
  rw [hp]
  exact range_mapFun_homotopyFiber_point (Fin n) f b e₀ h

end HomotopyGroup
