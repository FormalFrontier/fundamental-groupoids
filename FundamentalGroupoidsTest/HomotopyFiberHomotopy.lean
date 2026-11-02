/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Homotopy.Fiber.Homotopy
import Mathlib.Tactic.NormNum

/-!
# A nonconstant path in a homotopy fiber

The constant maps from `Unit` to `ℝ` with values zero and one have different
strict fibers over zero. A path from zero to one gives a point of the second
homotopy fiber. Appending this path to a supplied nonconstant loop preserves
that loop as the whole first segment: quarter-time in the concatenated path
is midpoint-time in the loop, where the value is one rather than zero.
-/

@[expose] public section

noncomputable section

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

private def zeroUnitMap : C(Unit, ℝ) := ContinuousMap.const Unit 0

private def oneUnitMap : C(Unit, ℝ) := ContinuousMap.const Unit 1

private def unitIntervalHomotopy :
    ContinuousMap.Homotopy zeroUnitMap oneUnitMap where
  toFun p := (p.1 : ℝ)
  continuous_toFun := continuous_subtype_val.comp continuous_fst
  map_zero_left _ := rfl
  map_one_left _ := rfl

private def intervalPath : Path (0 : ℝ) 1 := unitIntervalHomotopy.evalAt ()

private def suppliedLoop : Path (0 : ℝ) 0 := intervalPath.trans intervalPath.symm

private def loopFiberPoint : HomotopyFiber zeroUnitMap 0 :=
  mk (f := zeroUnitMap) (b := 0) () suppliedLoop.toContinuousMap
    suppliedLoop.source suppliedLoop.target

private noncomputable def midpoint : I :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

private noncomputable def quarter : I :=
  ⟨(1 : ℝ) / 4, by constructor <;> norm_num⟩

/-- Strict fibers of the two unit maps at zero differ, while the homotopy-fiber map
accepts a nonconstant supplied loop and retains its whole first segment. The output
quarter-time is the original loop's midpoint, where its value is one. -/
example :
    Nonempty {e : Unit // zeroUnitMap e = (0 : ℝ)} ∧
      IsEmpty {e : Unit // oneUnitMap e = (0 : ℝ)} ∧
      Nonempty (HomotopyFiber oneUnitMap 0) ∧
      point (f := oneUnitMap) (b := 0)
          (homotopyMap (f := zeroUnitMap) (g := oneUnitMap)
            unitIntervalHomotopy 0 loopFiberPoint) = () ∧
      path (f := oneUnitMap) (b := 0)
          (homotopyMap (f := zeroUnitMap) (g := oneUnitMap)
            unitIntervalHomotopy 0 loopFiberPoint) =
        (suppliedLoop.trans intervalPath).toContinuousMap ∧
      eval (f := oneUnitMap) (b := 0) quarter
          (homotopyMap (f := zeroUnitMap) (g := oneUnitMap)
            unitIntervalHomotopy 0 loopFiberPoint) =
        eval (f := zeroUnitMap) (b := 0) midpoint loopFiberPoint ∧
      eval (f := zeroUnitMap) (b := 0) midpoint loopFiberPoint = (1 : ℝ) ∧
      path (f := zeroUnitMap) (b := 0) loopFiberPoint midpoint ≠
        path (f := zeroUnitMap) (b := 0) loopFiberPoint 0 := by
  have hpath :
      path (f := oneUnitMap) (b := 0)
          (homotopyMap (f := zeroUnitMap) (g := oneUnitMap)
            unitIntervalHomotopy 0 loopFiberPoint) =
        (suppliedLoop.trans intervalPath).toContinuousMap :=
    path_homotopyMap unitIntervalHomotopy 0 loopFiberPoint
  have hquarter :
      eval (f := oneUnitMap) (b := 0) quarter
          (homotopyMap (f := zeroUnitMap) (g := oneUnitMap)
            unitIntervalHomotopy 0 loopFiberPoint) =
        eval (f := zeroUnitMap) (b := 0) midpoint loopFiberPoint := by
    rw [eval_apply, hpath]
    change (suppliedLoop.trans intervalPath) quarter = suppliedLoop midpoint
    rw [Path.trans_apply,
      dite_eq_left (show (quarter : ℝ) ≤ 1 / 2 by norm_num [quarter])]
    apply congrArg suppliedLoop
    apply Subtype.ext
    norm_num [quarter, midpoint]
  have hmidpoint :
      eval (f := zeroUnitMap) (b := 0) midpoint loopFiberPoint = (1 : ℝ) := by
    change suppliedLoop midpoint = (1 : ℝ)
    rw [suppliedLoop, Path.trans_apply,
      dite_eq_left (show (midpoint : ℝ) ≤ 1 / 2 by norm_num [midpoint])]
    refine Eq.trans ?_ intervalPath.target
    apply congrArg intervalPath
    apply Subtype.ext
    norm_num [midpoint]
  refine ⟨⟨⟨(), rfl⟩⟩, ?_,
    ⟨homotopyMap unitIntervalHomotopy 0 loopFiberPoint⟩, ?_,
    hpath, hquarter, hmidpoint, ?_⟩
  · refine ⟨fun e => ?_⟩
    have h : (1 : ℝ) = 0 := e.property
    norm_num at h
  · exact point_homotopyMap unitIntervalHomotopy 0 loopFiberPoint
  · change eval (f := zeroUnitMap) (b := 0) midpoint loopFiberPoint ≠
      path (f := zeroUnitMap) (b := 0) loopFiberPoint 0
    rw [hmidpoint, path_zero]
    norm_num

end ContinuousMap.HomotopyFiber
