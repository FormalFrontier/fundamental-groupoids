/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Data.Set.Image

/-!
# Transport of range–point-fiber equalities

A commuting diagram of ordinary functions transports a range–point-fiber
identity to another row. Surjectivity in the first column and injectivity in
the last two columns suffice; neither algebraic structures nor equal
universes are required. Specializing to monoid homomorphisms at `1` gives the
reverse implication of Mathlib's exactness transport theorem.

## References

* `MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective` in
  `Mathlib.Algebra.Exact.Basic`.
-/

@[expose] public section

universe uA uB uC uA' uB' uC'

namespace Function

/-- Pull back a range–point-fiber equality along commuting coordinates.
Only the first coordinate must be surjective, and only the last two must be
injective. In particular, all three coordinates may be equivalences between
independently sized types. -/
theorem range_eq_preimage_singleton_of_coordinates
    {A : Type uA} {B : Type uB} {C : Type uC}
    {A' : Type uA'} {B' : Type uB'} {C' : Type uC'}
    {f : A → B} {g : B → C} {f' : A' → B'} {g' : B' → C'}
    (a : A' → A) (b : B' → B) (c : C' → C)
    (ha : Surjective a) (hb : Injective b) (hc : Injective c)
    (hf : ∀ x, b (f' x) = f (a x))
    (hg : ∀ y, c (g' y) = g (b y)) (p' : C')
    (hex : Set.range f = g ⁻¹' {c p'}) :
    Set.range f' = g' ⁻¹' {p'} := by
  ext y
  change (∃ x, f' x = y) ↔ g' y = p'
  constructor
  · rintro ⟨x, rfl⟩
    apply hc
    rw [hg, hf]
    have hx : f (a x) ∈ Set.range f := ⟨a x, rfl⟩
    rw [hex] at hx
    exact hx
  · intro hy
    have hby : b y ∈ Set.range f := by
      rw [hex]
      change g (b y) = c p'
      rw [← hg, hy]
    obtain ⟨x, hx⟩ := hby
    obtain ⟨x', hx'⟩ := ha x
    refine ⟨x', hb ?_⟩
    rw [hf, hx', hx]

private theorem mulExact_iff_range_eq_preimage_one
    {A : Type uA} {B : Type uB} {C : Type uC} [One C]
    {f : A → B} {g : B → C} :
    MulExact f g ↔ Set.range f = g ⁻¹' {1} :=
  ⟨fun h => Set.ext fun y => (h y).symm,
    fun h y => (Set.ext_iff.mp h y).symm⟩

end Function

namespace MonoidHom

/-- In a commuting diagram of commutative monoids, exactness of the lower row
implies exactness of the upper row when the left vertical map is surjective,
the middle vertical map is bijective, and the right vertical map is injective.
This is the reverse implication of
`MonoidHom.mulExact_iff_of_surjective_of_bijective_of_injective`, obtained from
`Function.range_eq_preimage_singleton_of_coordinates` at `1`. -/
theorem mulExact_of_surjective_of_bijective_of_injective
    {M₁ : Type uA} {M₂ : Type uB} {M₃ : Type uC}
    {N₁ : Type uA'} {N₂ : Type uB'} {N₃ : Type uC'}
    [CommMonoid M₁] [CommMonoid M₂] [CommMonoid M₃]
    [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]
    (f : M₁ →* M₂) (g : M₂ →* M₃) (f' : N₁ →* N₂) (g' : N₂ →* N₃)
    (τ₁ : M₁ →* N₁) (τ₂ : M₂ →* N₂) (τ₃ : M₃ →* N₃)
    (comm₁₂ : f'.comp τ₁ = τ₂.comp f)
    (comm₂₃ : g'.comp τ₂ = τ₃.comp g)
    (h₁ : Function.Surjective τ₁) (h₂ : Function.Bijective τ₂)
    (h₃ : Function.Injective τ₃) (h : Function.MulExact f' g') :
    Function.MulExact f g := by
  apply Function.mulExact_iff_range_eq_preimage_one.2
  refine Function.range_eq_preimage_singleton_of_coordinates
    (f := (f' : N₁ → N₂)) (g := (g' : N₂ → N₃))
    τ₁ τ₂ τ₃ h₁ h₂.1 h₃
    (fun x => (DFunLike.congr_fun comm₁₂ x).symm)
    (fun y => (DFunLike.congr_fun comm₂₃ y).symm) 1 ?_
  simpa only [map_one] using Function.mulExact_iff_range_eq_preimage_one.1 h

end MonoidHom
