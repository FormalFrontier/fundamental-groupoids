/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Cube
public import Mathlib.Logic.Equiv.Basic

/-!
# Cubes indexed by an option type

The cube on `Option N` is the cylinder on the cube on `N`. The distinguished
coordinate is the cylinder coordinate. Its coordinate-face boundary consists
of the two end faces and the cylinder on `Cube.boundary N`.

The homeomorphism uses Mathlib's `Equiv.piOptionEquivProd`.
-/

public section

universe u

open scoped unitInterval

namespace Cube

/-- Separate the distinguished coordinate of a cube indexed by `Option N`. -/
@[expose]
def optionHomeomorph (N : Type u) : (Option N → I) ≃ₜ I × (N → I) where
  toEquiv := Equiv.piOptionEquivProd
  continuous_toFun :=
    (continuous_apply none).prodMk (continuous_pi fun i => continuous_apply (some i))
  continuous_invFun := continuous_pi fun i => by
    cases i with
    | none => exact continuous_fst
    | some i => exact (continuous_apply i).comp continuous_snd

@[simp]
theorem optionHomeomorph_apply (N : Type u) (z : Option N → I) :
    optionHomeomorph N z = (z none, fun i => z (some i)) :=
  rfl

@[simp]
theorem optionHomeomorph_symm_apply_none (N : Type u) (r : I × (N → I)) :
    (optionHomeomorph N).symm r none = r.1 :=
  rfl

@[simp]
theorem optionHomeomorph_symm_apply_some (N : Type u) (r : I × (N → I)) (i : N) :
    (optionHomeomorph N).symm r (some i) = r.2 i :=
  rfl

/-- The boundary of an option-indexed cube is the union of its two end faces
and the cylinder on the boundary of the remaining cube. -/
theorem option_mem_boundary_iff {N : Type u} (z : Option N → I) :
    z ∈ boundary (Option N) ↔
      z none = 0 ∨ z none = 1 ∨ (fun i => z (some i)) ∈ boundary N := by
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | none =>
      rcases hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    | some i => exact Or.inr (Or.inr ⟨i, hi⟩)
  · rintro (h | h | h)
    · exact ⟨none, Or.inl h⟩
    · exact ⟨none, Or.inr h⟩
    · obtain ⟨i, hi⟩ := h
      exact ⟨some i, hi⟩

/-- The cylinder description of the boundary, pulled back along the option
cube homeomorphism. -/
@[simp]
theorem optionHomeomorph_symm_mem_boundary_iff (N : Type u) (r : I × (N → I)) :
    (optionHomeomorph N).symm r ∈ boundary (Option N) ↔
      r.1 = 0 ∨ r.1 = 1 ∨ r.2 ∈ boundary N := by
  rw [option_mem_boundary_iff]
  rfl

end Cube
