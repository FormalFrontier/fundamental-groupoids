/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Semilocally simply connected spaces

A space is semilocally simply connected at `x` if `x` has an open neighborhood
whose loops based at the chosen center `x` are nullhomotopic in the ambient space.
The nullhomotopies need not remain in the neighborhood. Without local path
connectedness, this does not assert the same condition at every basepoint in
one neighborhood, nor does it assert that the neighborhood is simply connected.

The global property asks for this chosen-center condition separately at every
point; in particular it holds vacuously on an empty space.

## References

Mathlib's fundamental-group and path-homotopy APIs supply the loop classes and
ambient homotopies. Its `SimplyConnectedSpace.paths_homotopic` supplies the
simply-connected case; the inclusion-range criterion is in
`FundamentalGroupoids.FundamentalGroup`.
-/

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The point `x` has an open neighborhood such that every loop based at `x`
with range in that neighborhood is nullhomotopic in the ambient space `X`.
Only loops at the chosen center are quantified, and the nullhomotopies need
not remain in the neighborhood. -/
def IsSemilocallySimplyConnectedAt (x : X) : Prop :=
  ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x)

/-- Every point has an open neighborhood whose loops at that chosen point are
nullhomotopic in the ambient space. No local path connectedness is assumed. -/
class SemilocallySimplyConnectedSpace (X : Type u) [TopologicalSpace X] : Prop where
  isSemilocallySimplyConnectedAt : ∀ x : X, IsSemilocallySimplyConnectedAt x

/-- The characteristic open-neighborhood condition, with nullhomotopies in `X`. -/
theorem isSemilocallySimplyConnectedAt_iff_exists_isOpen (x : X) :
    IsSemilocallySimplyConnectedAt x ↔
      ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
        ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x) :=
  Iff.rfl

namespace IsSemilocallySimplyConnectedAt

/-- Construct the pointwise property from an open neighborhood and ambient
nullhomotopies of its loops at the chosen center. -/
theorem of_isOpen {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U)
    (hloops : ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x)) :
    IsSemilocallySimplyConnectedAt x :=
  ⟨U, hU, hx, hloops⟩

/-- Extract an open neighborhood and the ambient nullhomotopies of its loops
at the chosen center. -/
theorem exists_isOpen {x : X} (h : IsSemilocallySimplyConnectedAt x) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x) :=
  h

end IsSemilocallySimplyConnectedAt

/-- Global semilocal simple connectivity is exactly the chosen-center condition
at every point, including vacuously when the space is empty. -/
theorem semilocallySimplyConnectedSpace_iff :
    SemilocallySimplyConnectedSpace X ↔ ∀ x : X, IsSemilocallySimplyConnectedAt x :=
  ⟨fun h => h.isSemilocallySimplyConnectedAt, fun h => ⟨h⟩⟩

namespace SemilocallySimplyConnectedSpace

/-- Construct the global property from the pointwise condition at every point. -/
theorem of_forall (h : ∀ x : X, IsSemilocallySimplyConnectedAt x) :
    SemilocallySimplyConnectedSpace X :=
  ⟨h⟩

end SemilocallySimplyConnectedSpace

/-- Every chosen point of a semilocally simply connected space satisfies the
pointwise open-neighborhood condition. -/
theorem isSemilocallySimplyConnectedAt [SemilocallySimplyConnectedSpace X] (x : X) :
    IsSemilocallySimplyConnectedAt x :=
  SemilocallySimplyConnectedSpace.isSemilocallySimplyConnectedAt x

/-! ## Fundamental-group characterization -/

/-- Semilocal simple connectivity at `x` is equivalent to an open neighborhood
whose inclusion has trivial image on the fundamental group based at `⟨x, hx⟩`.
There is no connectedness hypothesis on the neighborhood. -/
theorem isSemilocallySimplyConnectedAt_iff_exists_range_eq_bot (x : X) :
    IsSemilocallySimplyConnectedAt x ↔
      ∃ (U : Set X) (hx : x ∈ U), IsOpen U ∧
        (FundamentalGroup.map (ContinuousMap.subtypeVal U) ⟨x, hx⟩).range = ⊥ := by
  constructor
  · intro h
    obtain ⟨U, hU, hx, hloops⟩ := h.exists_isOpen
    exact ⟨U, hx, hU, (FundamentalGroup.range_map_subtypeVal_eq_bot_iff hx).2 hloops⟩
  · rintro ⟨U, hx, hU, h⟩
    exact IsSemilocallySimplyConnectedAt.of_isOpen hU hx
      ((FundamentalGroup.range_map_subtypeVal_eq_bot_iff hx).1 h)

/-! ## Simply connected spaces and reflection -/

namespace IsSemilocallySimplyConnectedAt

/-- In a simply connected space every chosen point satisfies the semilocal
condition, using the whole space as its neighborhood. No local path
connectedness is needed. -/
theorem of_simplyConnectedSpace [SimplyConnectedSpace X] (x : X) :
    IsSemilocallySimplyConnectedAt x :=
  of_isOpen isOpen_univ (Set.mem_univ x)
    (fun γ _ => SimplyConnectedSpace.paths_homotopic γ (Path.refl x))

/-- A continuous map whose induced based fundamental-group homomorphism is
injective reflects semilocal simple connectivity at the chosen point.
Injectivity of the underlying map is not assumed. -/
theorem of_injective_fundamentalGroup_map (f : C(X, Y)) {x : X}
    (hinj : Function.Injective (FundamentalGroup.map f x))
    (h : IsSemilocallySimplyConnectedAt (f x)) : IsSemilocallySimplyConnectedAt x := by
  obtain ⟨V, hV, hfx, hloops⟩ := h.exists_isOpen
  refine of_isOpen (hV.preimage f.continuous) hfx ?_
  intro γ hγ
  have hm : (γ.map f.continuous).Homotopic (Path.refl (f x)) :=
    hloops _ (by
      rintro y ⟨t, rfl⟩
      exact hγ ⟨t, rfl⟩)
  have hm' :
      (Path.Homotopic.Quotient.mk (γ.map f.continuous) : FundamentalGroup Y (f x)) =
        (1 : FundamentalGroup Y (f x)) :=
    (FundamentalGroup.mk_eq_one_iff (γ.map f.continuous)).mpr hm
  apply (FundamentalGroup.mk_eq_one_iff γ).mp
  apply hinj
  simpa only [map_one, FundamentalGroup.map_apply,
    ← Path.Homotopic.Quotient.mk_map] using hm'

end IsSemilocallySimplyConnectedAt

/-- Simply connected spaces are semilocally simply connected, without any
local path connectedness hypothesis. -/
instance SimplyConnectedSpace.semilocallySimplyConnectedSpace [SimplyConnectedSpace X] :
    SemilocallySimplyConnectedSpace X :=
  ⟨IsSemilocallySimplyConnectedAt.of_simplyConnectedSpace⟩
