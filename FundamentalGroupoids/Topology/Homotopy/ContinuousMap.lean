/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Precomposition along homotopies

A homotopy between maps from `X` to `Y` induces a homotopy between the corresponding
precomposition maps `C(Y, Z) → C(X, Z)`. The construction uses
`ContinuousMap.Homotopy.curry` and `ContinuousMap.continuous_comp'`; joint continuity of
composition is supplied by `LocallyCompactPair Y Z`.
-/

@[expose] public section

open scoped unitInterval

universe u v w

namespace ContinuousMap.Homotopy

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [LocallyCompactPair Y Z] {f₀ f₁ : C(X, Y)}

/-- A homotopy induces a homotopy between the corresponding precomposition maps. -/
def compRightContinuousMap (H : Homotopy f₀ f₁) :
    Homotopy (ContinuousMap.compRightContinuousMap Z f₀)
      (ContinuousMap.compRightContinuousMap Z f₁) where
  toFun p := p.2.comp (H.curry p.1)
  continuous_toFun := ContinuousMap.continuous_comp'.comp
    ((H.curry.continuous.comp continuous_fst).prodMk continuous_snd)
  map_zero_left p := by
    ext x
    exact congrArg p (H.apply_zero x)
  map_one_left p := by
    ext x
    exact congrArg p (H.apply_one x)

/-- Evaluation of the precomposition homotopy is evaluation along the original homotopy. -/
@[simp]
theorem compRightContinuousMap_apply (H : Homotopy f₀ f₁) (t : I) (p : C(Y, Z)) (x : X) :
    H.compRightContinuousMap (t, p) x = p (H (t, x)) := by
  rfl

end ContinuousMap.Homotopy

namespace ContinuousMap.Homotopic

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [LocallyCompactPair Y Z] {f₀ f₁ : C(X, Y)}

/-- Homotopic maps induce homotopic precomposition maps between mapping spaces. -/
theorem compRightContinuousMap (h : Homotopic f₀ f₁) :
    Homotopic (ContinuousMap.compRightContinuousMap Z f₀)
      (ContinuousMap.compRightContinuousMap Z f₁) := by
  rcases h with ⟨H⟩
  exact ⟨H.compRightContinuousMap⟩

end ContinuousMap.Homotopic
