/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Precomposition of relative homotopies

Precomposing a homotopy relative to `S` along a continuous map gives a homotopy
relative to any set mapped into `S`.

## References

* Mathlib's `Mathlib.Topology.Homotopy.Basic` supplies relative homotopies and
  precomposition of their underlying homotopies.
-/

@[expose] public section

noncomputable section

universe u v w

open unitInterval

namespace ContinuousMap

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace HomotopyRel

variable {f g : C(X, Y)} {S : Set X} {T : Set Z}

/-- Precompose a homotopy relative to `S` by a continuous map sending `T` into `S`. -/
def precomp (H : HomotopyRel f g S) (k : C(Z, X)) (hk : Set.MapsTo k T S) :
    HomotopyRel (f.comp k) (g.comp k) T where
  toHomotopy := H.toHomotopy.compContinuousMap k
  prop' t _ hz := H.eq_fst t (hk hz)

@[simp]
theorem precomp_toHomotopy (H : HomotopyRel f g S) (k : C(Z, X))
    (hk : Set.MapsTo k T S) :
    (H.precomp k hk).toHomotopy = H.toHomotopy.compContinuousMap k :=
  rfl

@[simp]
theorem precomp_apply (H : HomotopyRel f g S) (k : C(Z, X))
    (hk : Set.MapsTo k T S) (p : I × Z) :
    H.precomp k hk p = H (p.1, k p.2) :=
  rfl

end HomotopyRel

namespace HomotopicRel

/-- Precomposition preserves relative homotopy on every set mapped into the fixed set. -/
theorem precomp_continuousMap {f₀ f₁ : C(Y, Z)} {S : Set Y} {T : Set X}
    (H : f₀.HomotopicRel f₁ S) (g : C(X, Y)) (hg : Set.MapsTo g T S) :
    (f₀.comp g).HomotopicRel (f₁.comp g) T :=
  H.map (fun F ↦ F.precomp g hg)

end HomotopicRel

end ContinuousMap
