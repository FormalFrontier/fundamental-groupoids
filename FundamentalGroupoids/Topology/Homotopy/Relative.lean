/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.Inseparable

/-!
# Constrained homotopies and mapping spaces

Pointwise specialization gives a homotopy whose time slices are its endpoints,
preserving any predicate satisfied by both endpoints. A point specializing to
every point of a space also yields contractibility of that space.

A homotopy whose intermediate maps satisfy a predicate gives a path in the
corresponding subtype of the compact-open mapping space. For a locally compact
source, uncurrying gives the converse. No local compactness or separation
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

namespace HomotopyWith

variable {A : Type u} {B : Type v} [TopologicalSpace A] [TopologicalSpace B]
  {f₀ f₁ : C(A, B)} {P : C(A, B) → Prop}

/-- Pointwise specialization from `f₀` to `f₁` gives a homotopy in the same direction,
with value `f₀` until the final time and value `f₁` at time `1`. Since every time slice
is an endpoint, any predicate holding at both endpoints is preserved. -/
noncomputable def ofSpecializes (h : ∀ a, f₀ a ⤳ f₁ a) (h₀ : P f₀) (h₁ : P f₁) :
    HomotopyWith f₀ f₁ P := by
  classical
  refine
    { toFun := fun p ↦ if p.1 = 1 then f₁ p.2 else f₀ p.2
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · have hs : IsClosed {p : I × A | p.1 = 1} :=
      isClosed_singleton.preimage continuous_fst
    exact hs.continuous_piecewise_of_specializes
      (f₁.continuous.comp continuous_snd) (f₀.continuous.comp continuous_snd)
      (fun p ↦ h p.2)
  · intro a
    simp
  · intro a
    simp
  · intro t
    by_cases ht : t = 1
    · convert h₁ using 1
      ext a
      simp [ht]
    · convert h₀ using 1
      ext a
      simp [ht]

@[simp]
theorem ofSpecializes_apply (h : ∀ a, f₀ a ⤳ f₁ a) (h₀ : P f₀) (h₁ : P f₁)
    (p : I × A) :
    ofSpecializes h h₀ h₁ p = if p.1 = 1 then f₁ p.2 else f₀ p.2 := by
  classical
  rfl

end HomotopyWith

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

/-- A space with a point specializing to every point is contractible. -/
theorem contractibleSpace_of_specializes {Y : Type w} [TopologicalSpace Y]
    (p : Y) (h : ∀ y : Y, p ⤳ y) : ContractibleSpace Y := by
  apply (contractible_iff_id_nullhomotopic Y).mpr
  refine ⟨p, ?_⟩
  exact ⟨(ContinuousMap.HomotopyWith.ofSpecializes
    (f₀ := ContinuousMap.const Y p) (f₁ := ContinuousMap.id Y)
    (P := fun _ ↦ True) h trivial trivial).toHomotopy.symm⟩
