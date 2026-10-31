/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Basic

/-!
# Relative homotopies and constrained mapping spaces

A homotopy whose intermediate maps satisfy a predicate gives a path in the
corresponding subtype of the compact-open mapping space. When the source is
locally compact, uncurrying gives the converse. No local compactness or separation
assumption is needed on the target.

Precomposing a homotopy relative to `S` along a continuous map gives a homotopy
relative to any set mapped into `S`.

## References

* Mathlib's `Mathlib.Topology.Homotopy.Basic` supplies relative homotopies,
  currying and precomposition of their underlying homotopies;
  `Mathlib.Topology.CompactOpen` supplies uncurrying, and
  `Mathlib.Topology.Connected.PathConnected` supplies paths in subtypes.
-/

@[expose] public section

noncomputable section

universe u v w

open unitInterval

namespace ContinuousMap

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace HomotopyWith

variable {f g : C(X, Y)} {P : C(X, Y) → Prop}

/-- A homotopy satisfying a predicate joins its endpoints in the corresponding
subtype of the compact-open mapping space. Currying requires no local compactness. -/
theorem joined (H : HomotopyWith f g P) (hf : P f) (hg : P g) :
    Joined (⟨f, hf⟩ : Subtype P) ⟨g, hg⟩ := by
  apply (joinedIn_iff_joined (F := {k : C(X, Y) | P k}) hf hg).mp
  exact ⟨⟨H.toHomotopy.curry, H.toHomotopy.curry_zero, H.toHomotopy.curry_one⟩,
    H.prop⟩

/-- For a locally compact source, homotopies satisfying a predicate are equivalent
to paths between the endpoints in the corresponding compact-open mapping subtype. -/
theorem nonempty_iff_joined [LocallyCompactSpace X] (hf : P f) (hg : P g) :
    Nonempty (HomotopyWith f g P) ↔ Joined (⟨f, hf⟩ : Subtype P) ⟨g, hg⟩ := by
  constructor
  · rintro ⟨H⟩
    exact H.joined hf hg
  · rintro ⟨γ⟩
    let γ' : Path f g := γ.map continuous_subtype_val
    refine ⟨{ toContinuousMap := γ'.toContinuousMap.uncurry
              map_zero_left := fun a ↦ congrArg (fun k : C(X, Y) ↦ k a) γ'.source
              map_one_left := fun a ↦ congrArg (fun k : C(X, Y) ↦ k a) γ'.target
              prop' := ?_ }⟩
    intro t
    change P (γ t).val
    exact (γ t).property

end HomotopyWith

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
