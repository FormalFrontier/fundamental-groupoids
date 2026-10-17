/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# The based covering-map lifting criterion

A continuous map from a path connected, locally path connected domain has a
unique lift with a prescribed value exactly when its induced fundamental-group
image lies in that of the covering map. The necessity is functoriality of the
fundamental group; sufficiency and uniqueness are supplied by Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le`.

The spaces have independent universes. Only the domain needs connectedness or
local path connectedness. The specified equality transports both subgroup ranges
to the fundamental group at the image of the domain basepoint, without choosing
a path. No global surjectivity of the covering map is required.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3 §7,
  based lifting criterion and uniqueness.
* Mathlib's `Mathlib.Topology.Homotopy.Lifting`, in particular the lifting
  approach of Junyan Xu.
-/

@[expose] public section

universe u v w

/-- The based lifting criterion of May, *A Concise Course in Algebraic Topology*,
Chapter 3 §7: a continuous map has a unique lift with the prescribed value if
and only if its fundamental-group image lies in the covering map's image.
Sufficiency and uniqueness are Mathlib's
`IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` (Junyan Xu's lifting
approach). Unlike the book's standing connected, locally path connected spaces
and surjective-cover convention, only the domain is path connected and locally
path connected here; the base and total space are unrestricted, and no global
surjectivity is assumed. -/
public theorem IsCoveringMap.existsUnique_continuousMap_lifts_iff_range_le
    {A : Type u} {E : Type v} {X : Type w}
    [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (cov : IsCoveringMap p)
    [PathConnectedSpace A] [LocallyPathConnectedSpace A]
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀) :
    (∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f) ↔
      (FundamentalGroup.map f a₀).range ≤
        (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).range := by
  constructor
  · rintro ⟨F, ⟨h₀, hF⟩, _⟩
    have hcomp : (⟨p, cov.continuous⟩ : C(E, X)).comp F = f :=
      ContinuousMap.ext fun a ↦ congrFun hF a
    have hπ : (FundamentalGroup.mapOfEq ⟨p, cov.continuous⟩ he).comp
        (FundamentalGroup.mapOfEq F h₀) = FundamentalGroup.map f a₀ := by
      -- Equality induction removes basepoint transport before functoriality.
      subst e₀
      subst f
      ext γ
      simp only [MonoidHom.comp_apply, FundamentalGroup.mapOfEq_apply,
        FundamentalGroup.map_apply, Path.Homotopic.Quotient.cast_rfl_rfl,
        Path.Homotopic.Quotient.map_comp]
    rw [← hπ, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  · exact cov.existsUnique_continuousMap_lifts_of_range_le he
