/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import FundamentalGroupoids.Topology.CompactOpen

/-!
# Precomposition along homotopies

A homotopy between maps from `X` to `Y` induces a homotopy between the corresponding
precomposition maps `C(Y, Z) → C(X, Z)`, with no local compactness or separation
assumptions on `X`, `Y`, or `Z`. The construction uses
`ContinuousMap.Homotopy.curry` and joint partial evaluation with the compact
interval as parameter. Under `LocallyCompactPair Y Z`, it agrees with the
construction using joint continuity of composition.
-/

@[expose] public section

open scoped unitInterval

universe u v w

namespace ContinuousMap.Homotopy

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f₀ f₁ : C(X, Y)}

/-- A homotopy induces a homotopy between the corresponding precomposition maps. -/
def compRightContinuousMap (H : Homotopy f₀ f₁) :
    Homotopy (ContinuousMap.compRightContinuousMap Z f₀)
      (ContinuousMap.compRightContinuousMap Z f₁) where
  toFun p := p.2.comp (H.curry p.1)
  continuous_toFun := continuous_comp_curry H.toContinuousMap
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

/-- The whole precomposition family is given by composition with the corresponding
slice of the original homotopy. -/
theorem coe_compRightContinuousMap (H : Homotopy f₀ f₁) :
    (H.compRightContinuousMap : I × C(Y, Z) → C(X, Z)) =
      fun q => q.2.comp (H.curry q.1) := by
  rfl

/-- When joint composition is continuous, the precomposition homotopy agrees with
the construction using `ContinuousMap.continuous_comp'`. -/
theorem compRightContinuousMap_eq_of_locallyCompactPair [LocallyCompactPair Y Z]
    (H : Homotopy f₀ f₁) :
    H.compRightContinuousMap (Z := Z) =
      { toFun := fun p => p.2.comp (H.curry p.1)
        continuous_toFun := ContinuousMap.continuous_comp'.comp
          ((H.curry.continuous.comp continuous_fst).prodMk continuous_snd)
        map_zero_left := fun p => by
          ext x
          exact congrArg p (H.apply_zero x)
        map_one_left := fun p => by
          ext x
          exact congrArg p (H.apply_one x) } := by
  rfl

end ContinuousMap.Homotopy

namespace ContinuousMap.Homotopic

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f₀ f₁ : C(X, Y)}

/-- Homotopic maps induce homotopic precomposition maps between mapping spaces. -/
theorem compRightContinuousMap (h : Homotopic f₀ f₁) :
    Homotopic (ContinuousMap.compRightContinuousMap Z f₀)
      (ContinuousMap.compRightContinuousMap Z f₁) := by
  rcases h with ⟨H⟩
  exact ⟨H.compRightContinuousMap⟩

end ContinuousMap.Homotopic
