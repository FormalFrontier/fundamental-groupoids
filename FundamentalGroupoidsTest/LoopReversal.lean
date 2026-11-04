/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Category.TopCat.Based.Loop

/-!
# Evaluation of a reversed loop-map composite

Strict naturality moves reversal past an induced loop map. The component and
loop-map evaluation APIs then give `f (γ (1 − t))` at every time, on the original
loop spaces and without unfolding the natural isomorphism.
-/

universe u

open CategoryTheory BasedTopCat

example {X Y : BasedTopCat.{u}} (f : X ⟶ Y)
    (γ : Path (point X) (point X)) (t : unitInterval) :
    Path.toContinuousMap (x := point Y) (y := point Y)
        (((loopReversal.hom.app X) ≫ loopFunctor.map f).right.hom γ) t =
      f.right.hom (γ (unitInterval.symm t)) := by
  calc
    _ = Path.toContinuousMap (x := point Y) (y := point Y)
        ((loopFunctor.map f ≫ loopReversal.hom.app Y).right.hom γ) t :=
      congrArg
        (fun k : loopFunctor.obj X ⟶ loopFunctor.obj Y ↦
          Path.toContinuousMap (x := point Y) (y := point Y) (k.right.hom γ) t)
        (loopReversal.hom.naturality f).symm
    _ = Path.toContinuousMap (x := point Y) (y := point Y)
        ((loopReversal.hom.app Y).right.hom ((loopFunctor.map f).right.hom γ)) t := rfl
    _ = Path.toContinuousMap (x := point Y) (y := point Y)
        ((loopFunctor.map f).right.hom γ) (unitInterval.symm t) :=
      loopReversal_hom_app_apply_apply Y ((loopFunctor.map f).right.hom γ) t
    _ = _ := loopFunctor_map_apply_apply f γ (unitInterval.symm t)
