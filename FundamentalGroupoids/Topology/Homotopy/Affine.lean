/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Homotopy.Affine

/-!
# Affine homotopies relative to a subset

Affine interpolation between two continuous maps into a real topological vector
space fixes every point where the maps agree. `ContinuousMap.HomotopyRel.affine`
retains this fixed-subset property together with Mathlib's affine homotopy data.

The construction requires continuous addition and scalar multiplication.
Continuous negation follows from scalar multiplication by `-1`; no separation,
norm or completeness assumption is imposed.

## References

This construction uses Mathlib's affine homotopies by Yury G. Kudryashov,
straight segment paths by Patrick Massot and Yury Kudryashov, and relative
homotopies by Shing Tak Lam and contributors. Its underlying homotopy is
`ContinuousMap.Homotopy.affine`, not a separate interpolation construction.
-/

@[expose] public section

noncomputable section

universe u v

namespace ContinuousMap.HomotopyRel

variable {A : Type u} {E : Type v} [TopologicalSpace A]
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousSMul ℝ E]

/-- Affine interpolation between maps that agree on `S`, fixed throughout on `S`. -/
def affine [ContinuousAdd E] (f g : C(A, E)) {S : Set A} (hfg : Set.EqOn f g S) :
    ContinuousMap.HomotopyRel f g S := by
  letI : ContinuousNeg E := ContinuousNeg.of_continuousConstSMul ℝ E
  letI : IsTopologicalAddGroup E :=
    { toContinuousAdd := inferInstance
      toContinuousNeg := inferInstance }
  refine { toHomotopy := ContinuousMap.Homotopy.affine f g, prop' := ?_ }
  intro t a ha
  change Path.segment (f a) (g a) t = f a
  rw [← hfg ha, Path.segment_same]
  rfl

/-- The underlying homotopy of relative affine interpolation is Mathlib's affine homotopy. -/
@[simp]
theorem affine_toHomotopy [IsTopologicalAddGroup E] (f g : C(A, E))
    {S : Set A} (hfg : Set.EqOn f g S) :
    (affine f g hfg).toHomotopy = ContinuousMap.Homotopy.affine f g :=
  rfl

/-- Relative affine interpolation evaluates along the straight line between the map values. -/
@[simp]
theorem affine_apply [ContinuousAdd E] (f g : C(A, E)) {S : Set A}
    (hfg : Set.EqOn f g S) (p : unitInterval × A) :
    affine f g hfg p = AffineMap.lineMap (f p.2) (g p.2) (p.1 : ℝ) :=
  rfl

end ContinuousMap.HomotopyRel
