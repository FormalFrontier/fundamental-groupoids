/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.Topology.Homotopy.Relative
import Mathlib.Topology.Homotopy.Path

/-!
# Coordinate relative homotopies of rebased loops

This checks the whole composite of the relative-homotopy coordinate equivalence
with the stock endpoint-transport equivalences. Its forward characteristic keeps
both endpoint casts; its inverse characteristic also restores both original
coordinate paths after undoing the endpoint casts. The type ascriptions check
the Path specialization and the stock `Equiv.refl` normalizations.
-/

open unitInterval

universe uι uX

example {ι : Type uι} {X : ι → Type uX} [∀ i, TopologicalSpace (X i)]
    (a b : ∀ i, X i) (p q : Path a a) (h : ∀ i, a i = b i) :
    let Ex := (ContinuousMap.HomotopyRel.piEquiv
      p.toContinuousMap q.toContinuousMap {0, 1} :
      p.Homotopy q ≃
        (∀ i, (p.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).Homotopy
          (q.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous)))
    let L : p.Homotopy q ≃
        (∀ i,
          ((p.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).cast
            (h i).symm (h i).symm).Homotopy
          ((q.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).cast
            (h i).symm (h i).symm)) :=
      Ex.trans (Equiv.piCongrRight (fun i =>
        (Equiv.refl
            ((p.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).Homotopy
              (q.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous)) :
          (p.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).Homotopy
              (q.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous) ≃
            ((p.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).cast
              (h i).symm (h i).symm).Homotopy
            ((q.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).cast
              (h i).symm (h i).symm))))
    let uₚ : ∀ i,
        (((p.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).cast
          (h i).symm (h i).symm).cast (h i) (h i)) =
          p.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous :=
      fun _ => DFunLike.ext _ _ (fun _ => rfl)
    let u_q : ∀ i,
        (((q.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).cast
          (h i).symm (h i).symm).cast (h i) (h i)) =
          q.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous :=
      fun _ => DFunLike.ext _ _ (fun _ => rfl)
    (∀ H i, L H i =
      Path.Homotopy.pathCast
        (p := p.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous)
        (q := q.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous)
        (Ex H i) (h i).symm (h i).symm) ∧
      (∀ K, L.symm K =
        Ex.symm (fun i => Path.Homotopy.cast
          (Path.Homotopy.pathCast
            (p := (p.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).cast
              (h i).symm (h i).symm)
            (q := (q.map (ContinuousMap.eval i : C(∀ j, X j, X i)).continuous).cast
              (h i).symm (h i).symm)
            (K i) (h i) (h i)) (uₚ i) (u_q i))) := by
  dsimp only
  constructor
  · intro H i
    rfl
  · intro K
    apply congrArg (ContinuousMap.HomotopyRel.piEquiv
      p.toContinuousMap q.toContinuousMap {0, 1}).symm
    funext i
    exact ContinuousMap.HomotopyWith.ext (fun _ => rfl)
