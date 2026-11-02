/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids
import Mathlib.Tactic.NormNum

/-!
# Nonconstant paths in a product homotopy fiber

Two zero maps on the real line retain independent source points and the full
loops `t ↦ t * (1 - t)` and `t ↦ 2 * t * (1 - t)`. The product comparison keeps
both loops at the same time, and distinguishes points with identical paths but
different source coordinates. The free-source comparison also keeps the same
nonconstant loop while either source coordinate varies independently. These use
the public root and product-fiber API.
-/

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

private def zeroMap : C(ℝ, ℝ) := ContinuousMap.const ℝ 0

private def quadraticLoop : C(I, ℝ) where
  toFun t := (t : ℝ) * (1 - (t : ℝ))
  continuous_toFun := continuous_subtype_val.mul (continuous_const.sub continuous_subtype_val)

private def doubleQuadraticLoop : C(I, ℝ) where
  toFun t := (2 : ℝ) * (t : ℝ) * (1 - (t : ℝ))
  continuous_toFun :=
    (continuous_const.mul continuous_subtype_val).mul
      (continuous_const.sub continuous_subtype_val)

private theorem quadraticLoop_zero : quadraticLoop 0 = 0 := by
  simp [quadraticLoop]

private theorem quadraticLoop_one : quadraticLoop 1 = 0 := by
  simp [quadraticLoop]

private theorem doubleQuadraticLoop_zero : doubleQuadraticLoop 0 = 0 := by
  simp [doubleQuadraticLoop]

private theorem doubleQuadraticLoop_one : doubleQuadraticLoop 1 = 0 := by
  simp [doubleQuadraticLoop]

private def zeroFiberPair : HomotopyFiber zeroMap 0 × HomotopyFiber zeroMap 0 :=
  (mk 2 quadraticLoop quadraticLoop_zero quadraticLoop_one,
    mk 3 doubleQuadraticLoop doubleQuadraticLoop_zero doubleQuadraticLoop_one)

private def zeroProductPoint (a b : ℝ) :
    HomotopyFiber (zeroMap.prodMap zeroMap) ((0, 0) : ℝ × ℝ) :=
  mk (a, b) (quadraticLoop.prodMk doubleQuadraticLoop)
    (Prod.ext quadraticLoop_zero doubleQuadraticLoop_zero)
    (Prod.ext quadraticLoop_one doubleQuadraticLoop_one)

private noncomputable def midpoint : I :=
  ⟨(1 : ℝ) / 2, by constructor <;> norm_num⟩

/-- Two zero-map factors keep independent nonconstant whole paths and independent
source points. Changing a retained point while keeping both paths changes the
fiber datum and its comparison image; both path values use the same midpoint. -/
example :
    let H := prodHomeomorph zeroMap zeroMap 0 0
    let p := zeroProductPoint 2 3
    ¬ Function.Injective zeroMap ∧
      H p = zeroFiberPair ∧
      (eval midpoint (H p).1, eval midpoint (H p).2) = ((1 / 4 : ℝ), (1 / 2 : ℝ)) ∧
      p ≠ zeroProductPoint 5 3 ∧ H p ≠ H (zeroProductPoint 5 3) := by
  dsimp only
  have hpoints : zeroProductPoint 2 3 ≠ zeroProductPoint 5 3 := by
    intro h
    have h25 : (2 : ℝ) = 5 := congrArg (fun q => (point q).1) h
    norm_num at h25
  refine ⟨?_, ?_, ?_, hpoints, ?_⟩
  · intro h
    have h01 : (0 : ℝ) = 1 := h rfl
    norm_num at h01
  · apply Prod.ext
    · apply ext
      · exact point_prodHomeomorph_fst zeroMap zeroMap 0 0 (zeroProductPoint 2 3)
      · apply ContinuousMap.ext
        intro t
        exact eval_prodHomeomorph_fst zeroMap zeroMap 0 0 (zeroProductPoint 2 3) t
    · apply ext
      · exact point_prodHomeomorph_snd zeroMap zeroMap 0 0 (zeroProductPoint 2 3)
      · apply ContinuousMap.ext
        intro t
        exact eval_prodHomeomorph_snd zeroMap zeroMap 0 0 (zeroProductPoint 2 3) t
  · refine (eval_prodHomeomorph zeroMap zeroMap 0 0 (zeroProductPoint 2 3) midpoint).trans ?_
    norm_num [eval_apply, zeroProductPoint, midpoint, quadraticLoop, doubleQuadraticLoop]
  · intro h
    have hfst := congrArg
      (fun q : HomotopyFiber zeroMap 0 × HomotopyFiber zeroMap 0 => point q.1) h
    have h25 : (2 : ℝ) = 5 :=
      (point_prodHomeomorph_fst zeroMap zeroMap 0 0 (zeroProductPoint 2 3)).symm.trans
        (hfst.trans (point_prodHomeomorph_fst zeroMap zeroMap 0 0 (zeroProductPoint 5 3)))
    norm_num at h25

private def freeSourceInput (x z : ℝ) :
    HomotopyFiber (zeroMap.comp (ContinuousMap.fst : C(ℝ × ℝ, ℝ))) 0 :=
  mk (x, z) quadraticLoop quadraticLoop_zero quadraticLoop_one

private def freeSourceFiber (x : ℝ) : HomotopyFiber zeroMap 0 :=
  mk x quadraticLoop quadraticLoop_zero quadraticLoop_one

/-- A noninjective zero map keeps both source coordinates and the same nonconstant
whole path. Each coordinate varies independently, while the original midpoint
and its quarter-value are unchanged. -/
example :
    let e := compFstHomeomorph (Z := ℝ) zeroMap 0
    ¬ Function.Injective zeroMap ∧
      e (freeSourceInput 2 3) = (freeSourceFiber 2, 3) ∧
      e (freeSourceInput 5 3) = (freeSourceFiber 5, 3) ∧
      e (freeSourceInput 2 7) = (freeSourceFiber 2, 7) ∧
      path (e (freeSourceInput 2 3)).1 = quadraticLoop ∧
      path (e (freeSourceInput 5 3)).1 = quadraticLoop ∧
      path (e (freeSourceInput 2 7)).1 = quadraticLoop ∧
      eval midpoint (e (freeSourceInput 2 3)).1 = eval midpoint (freeSourceInput 2 3) ∧
      eval midpoint (e (freeSourceInput 2 3)).1 = (1 / 4 : ℝ) ∧
      quadraticLoop midpoint ≠ quadraticLoop 0 ∧
      freeSourceInput 2 3 ≠ freeSourceInput 5 3 ∧
      freeSourceInput 2 3 ≠ freeSourceInput 2 7 ∧
      e (freeSourceInput 2 3) ≠ e (freeSourceInput 5 3) ∧
      e (freeSourceInput 2 3) ≠ e (freeSourceInput 2 7) := by
  dsimp only
  have himage (x z : ℝ) :
      compFstHomeomorph (Z := ℝ) zeroMap 0 (freeSourceInput x z) =
        (freeSourceFiber x, z) :=
    compFstHomeomorph_mk zeroMap 0 x z quadraticLoop quadraticLoop_zero quadraticLoop_one
  have hx : freeSourceInput 2 3 ≠ freeSourceInput 5 3 := by
    intro h
    have h25 : (2 : ℝ) = 5 := congrArg (fun q => (point q).1) h
    norm_num at h25
  have hz : freeSourceInput 2 3 ≠ freeSourceInput 2 7 := by
    intro h
    have h37 : (3 : ℝ) = 7 := congrArg (fun q => (point q).2) h
    norm_num at h37
  refine ⟨?_, himage 2 3, himage 5 3, himage 2 7, ?_, ?_, ?_, ?_, ?_, ?_, hx, hz, ?_, ?_⟩
  · intro h
    have h01 : (0 : ℝ) = 1 := h rfl
    norm_num at h01
  · rw [himage]
    exact path_mk 2 quadraticLoop quadraticLoop_zero quadraticLoop_one
  · rw [himage]
    exact path_mk 5 quadraticLoop quadraticLoop_zero quadraticLoop_one
  · rw [himage]
    exact path_mk 2 quadraticLoop quadraticLoop_zero quadraticLoop_one
  · exact eval_compFstHomeomorph_fst zeroMap 0 (freeSourceInput 2 3) midpoint
  · calc
      eval midpoint (compFstHomeomorph (Z := ℝ) zeroMap 0 (freeSourceInput 2 3)).1 =
          eval midpoint (freeSourceInput 2 3) :=
        eval_compFstHomeomorph_fst zeroMap 0 (freeSourceInput 2 3) midpoint
      _ = (1 / 4 : ℝ) := by
        norm_num [eval_apply, freeSourceInput, quadraticLoop, midpoint]
  · norm_num [quadraticLoop, midpoint]
  · intro h
    exact hx ((compFstHomeomorph (Z := ℝ) zeroMap 0).injective h)
  · intro h
    exact hz ((compFstHomeomorph (Z := ℝ) zeroMap 0).injective h)

end ContinuousMap.HomotopyFiber
