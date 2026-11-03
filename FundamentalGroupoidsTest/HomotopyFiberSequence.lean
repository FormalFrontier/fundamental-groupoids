/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The degree-zero boundary of a pointed homotopy-fiber sequence

For the pointed constant map `PUnit → Bool`, with discrete `Bool`, two distinct
classes survive in degree zero. The incoming differential has exactly the
chosen class as its range, so the differential into degree zero is not surjective.
-/

noncomputable section

open CategoryTheory
open scoped Topology

namespace HomotopyGroup

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := discreteTopology_bot Bool

private def boolSequence : ChainComplex Pointed.{0} ℕ :=
  homotopyFiberSequence.{0, 0, 0} (ContinuousMap.const PUnit false) false PUnit.unit rfl

private def boolTrueClass : HomotopyGroup (Fin 0) Bool false :=
  ⟦(genLoopHomeoOfIsEmpty (Fin 0) (false : Bool)).symm true⟧

private theorem boolTrueClass_ne_const :
    boolTrueClass ≠ (⟦GenLoop.const⟧ : HomotopyGroup (Fin 0) Bool false) := by
  intro h
  have hc := congrArg
    (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) (false : Bool)) h
  change ZerothHomotopy.mk true = ZerothHomotopy.mk false at hc
  have hj : Joined (true : Bool) false := Quotient.exact hc
  have he : (false : Bool) = true := by
    simpa only [connectedComponent_eq_singleton, Set.mem_singleton_iff] using
      (pathComponent_subset_component (true : Bool) hj)
  cases he

private theorem pointedIso_inv_hom {X Y : Pointed.{0}} (e : X ≅ Y) (a : X) :
    e.inv.toFun (e.hom.toFun a) = a :=
  congrFun (congrArg Pointed.Hom.toFun e.hom_inv_id) a

private theorem pointedIso_hom_inv {X Y : Pointed.{0}} (e : X ≅ Y) (a : Y) :
    e.hom.toFun (e.inv.toFun a) = a :=
  congrFun (congrArg Pointed.Hom.toFun e.inv_hom_id) a

/-- For the pointed constant `PUnit → Bool`, the chosen class and a distinct
class both survive in degree zero. The incoming differential has exactly the
chosen singleton as its range and is not surjective. -/
private theorem boolSequence_degree_zero_boundary :
    ∃ x : boolSequence.X 0, x ≠ (boolSequence.X 0).point ∧
      Set.range (boolSequence.d 1 0).toFun = {(boolSequence.X 0).point} ∧
      ¬Function.Surjective (boolSequence.d 1 0).toFun := by
  let I := homotopyFiberSequenceBaseIso.{0, 0, 0}
    (ContinuousMap.const PUnit false) false PUnit.unit rfl 0
  let J := homotopyFiberSequenceTotalIso.{0, 0, 0}
    (ContinuousMap.const PUnit false) false PUnit.unit rfl 0
  let x : boolSequence.X 0 := I.inv.toFun (ULift.up boolTrueClass)
  have hx : x ≠ (boolSequence.X 0).point := by
    intro heq
    have hh := congrArg I.hom.toFun heq
    have hraw : ULift.up boolTrueClass =
        (ULift.up (⟦GenLoop.const⟧ : HomotopyGroup (Fin 0) Bool false) :
          ULift.{0} (HomotopyGroup (Fin 0) Bool false)) :=
      (pointedIso_hom_inv I (ULift.up boolTrueClass)).symm.trans
        (hh.trans I.hom.map_point)
    exact boolTrueClass_ne_const (congrArg ULift.down hraw)
  have hd (a : boolSequence.X 1) :
      (boolSequence.d 1 0).toFun a = (boolSequence.X 0).point := by
    -- The total-space term has only one class, independently of the differential.
    let : Subsingleton (ZerothHomotopy PUnit.{1}) :=
      inferInstanceAs (Subsingleton (Quotient (pathSetoid PUnit.{1})))
    have hJ : J.hom.toFun a = J.hom.toFun (boolSequence.X 1).point := by
      apply ULift.ext
      apply (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) PUnit.unit).injective
      exact Subsingleton.elim _ _
    have ha : a = (boolSequence.X 1).point :=
      Function.LeftInverse.injective (pointedIso_inv_hom J) hJ
    exact (congrArg (boolSequence.d 1 0).toFun ha).trans
      (boolSequence.d 1 0).map_point
  have hr : Set.range (boolSequence.d 1 0).toFun = {(boolSequence.X 0).point} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact hd a
    · intro hz
      change z = (boolSequence.X 0).point at hz
      subst z
      exact ⟨(boolSequence.X 1).point, (boolSequence.d 1 0).map_point⟩
  refine ⟨x, hx, hr, ?_⟩
  intro hs
  obtain ⟨a, ha⟩ := hs x
  exact hx (ha.symm.trans (hd a))

end HomotopyGroup
