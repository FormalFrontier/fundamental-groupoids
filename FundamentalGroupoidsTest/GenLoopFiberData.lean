/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Homotopy.Fiber.GenLoop

/-!
# Empty-index retained-data control

For an empty cube index, generalized loops recover their target space. The
existing empty-index homeomorphism evaluates the homotopy-fiber comparison in the
original fiber. The input retains point `1`, rather than base point `0`, and the
nonconstant whole path `t ↦ t`. The raw empty-index boundary imposes no point
constraint.
-/

open unitInterval
open scoped Topology

namespace GenLoopFiberData

private def intervalCoordinate : C(I, ℝ) :=
  ⟨fun t => (t : ℝ), continuous_subtype_val⟩

private theorem intervalCoordinate_zero : intervalCoordinate (0 : I) = (0 : ℝ) :=
  rfl

private theorem intervalCoordinate_one :
    intervalCoordinate (1 : I) = (ContinuousMap.id ℝ) (1 : ℝ) :=
  rfl

private def emptyPoint : GenLoop Empty ℝ 0 :=
  (genLoopHomeoOfIsEmpty Empty (0 : ℝ)).symm 1

private def emptyPath : C(I, GenLoop Empty ℝ 0) :=
  ((genLoopHomeoOfIsEmpty Empty (0 : ℝ)).symm :
    C(ℝ, GenLoop Empty ℝ 0)).comp intervalCoordinate

private def emptyInput :
    ContinuousMap.HomotopyFiber
      (⟨GenLoop.map (ContinuousMap.id ℝ) (ContinuousMap.id_apply (0 : ℝ)),
        GenLoop.continuous_map (ContinuousMap.id ℝ)
          (ContinuousMap.id_apply (0 : ℝ))⟩ :
          C(GenLoop Empty ℝ 0, GenLoop Empty ℝ 0)) GenLoop.const :=
  ContinuousMap.HomotopyFiber.mk emptyPoint emptyPath rfl (by
    apply GenLoop.ext
    intro s
    rfl)

-- Evaluation by the existing empty-index provider gives the original retained
-- point and the whole supplied path, not merely an equivalent point coordinate.
example :
    genLoopHomeoOfIsEmpty Empty
        (ContinuousMap.HomotopyFiber.const (f := ContinuousMap.id ℝ)
          (b := (0 : ℝ)) 0 (ContinuousMap.id_apply (0 : ℝ)))
        (ContinuousMap.HomotopyFiber.genLoopHomeomorph (N := Empty) (e₀ := (0 : ℝ)) (b := (0 : ℝ))
          (ContinuousMap.id ℝ) (ContinuousMap.id_apply (0 : ℝ)) emptyInput) =
      ContinuousMap.HomotopyFiber.mk (f := ContinuousMap.id ℝ) (b := 0)
        1 intervalCoordinate intervalCoordinate_zero intervalCoordinate_one := by
  change ContinuousMap.HomotopyFiber.genLoopHomeomorph (N := Empty) (e₀ := (0 : ℝ)) (b := (0 : ℝ))
    (ContinuousMap.id ℝ) (ContinuousMap.id_apply (0 : ℝ)) emptyInput (0 : Empty → I) = _
  rw [ContinuousMap.HomotopyFiber.genLoopHomeomorph_apply]
  apply ContinuousMap.HomotopyFiber.ext
  · rw [ContinuousMap.HomotopyFiber.point_genLoopForward]
    rfl
  · rw [ContinuousMap.HomotopyFiber.path_genLoopForward]
    apply ContinuousMap.ext
    intro t
    rw [ContinuousMap.HomotopyFiber.genLoopForwardPath_apply]
    rfl

-- Neither the retained point nor the retained path collapses to the canonical
-- constant datum, even though there are no boundary faces.
example :
    ContinuousMap.HomotopyFiber.point
        (ContinuousMap.HomotopyFiber.genLoopHomeomorph (N := Empty) (e₀ := (0 : ℝ)) (b := (0 : ℝ))
          (ContinuousMap.id ℝ) (ContinuousMap.id_apply (0 : ℝ)) emptyInput (0 : Empty → I)) ≠ 0 ∧
      ContinuousMap.HomotopyFiber.path
          (ContinuousMap.HomotopyFiber.genLoopHomeomorph (N := Empty) (e₀ := (0 : ℝ)) (b := (0 : ℝ))
            (ContinuousMap.id ℝ) (ContinuousMap.id_apply (0 : ℝ)) emptyInput (0 : Empty → I)) 0 ≠
        ContinuousMap.HomotopyFiber.path
          (ContinuousMap.HomotopyFiber.genLoopHomeomorph (N := Empty) (e₀ := (0 : ℝ)) (b := (0 : ℝ))
            (ContinuousMap.id ℝ) (ContinuousMap.id_apply (0 : ℝ))
            emptyInput (0 : Empty → I)) 1 := by
  simp only [ContinuousMap.HomotopyFiber.genLoopHomeomorph_apply,
    ContinuousMap.HomotopyFiber.point_genLoopForward,
    ContinuousMap.HomotopyFiber.path_genLoopForward_apply]
  constructor
  · change (1 : ℝ) ≠ 0
    exact one_ne_zero
  · change (0 : ℝ) ≠ 1
    exact zero_ne_one

end GenLoopFiberData
