/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Path

/-!
# Corestriction of paths to subspaces

A path whose range is contained in a set can be regarded as a path in that subspace.
The inclusion recovers the original path. A homotopy between paths in a subspace
can likewise be recovered from an ambient based homotopy whose range stays in the
subspace.

## References

* Mathlib's paths and path homotopies supply the underlying constructions.
* The path corestriction factors the construction used in the open-cover descent
  and fundamental-group subspace arguments in this library.
-/

@[expose] public section

namespace Path

variable {X : Type*} [TopologicalSpace X] {a b : X} {s : Set X}

/-- Regard a path whose range lies in a set as a path in the corresponding subspace. -/
def codRestrict (γ : Path a b) (hγ : Set.range γ ⊆ s) :
    Path (⟨a, hγ γ.source_mem_range⟩ : s) ⟨b, hγ γ.target_mem_range⟩ where
  toFun t := ⟨γ t, hγ ⟨t, rfl⟩⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp]
theorem codRestrict_apply (γ : Path a b) (hγ : Set.range γ ⊆ s) (t : unitInterval) :
    γ.codRestrict hγ t = ⟨γ t, hγ ⟨t, rfl⟩⟩ := rfl

/-- Inclusion of a corestricted path recovers the original path. -/
@[simp]
theorem codRestrict_map_subtypeVal (γ : Path a b) (hγ : Set.range γ ⊆ s) :
    (γ.codRestrict hγ).map continuous_subtype_val = γ := by
  ext t
  rfl

/-- Corestriction of a constant path is constant. -/
@[simp]
theorem codRestrict_refl (a : X) (h : Set.range (Path.refl a) ⊆ s) :
    (Path.refl a).codRestrict h = Path.refl (⟨a, h (Path.refl a).source_mem_range⟩ : s) := by
  ext t
  rfl

/-- Corestriction respects concatenation. -/
theorem codRestrict_trans {c : X} (γ : Path a b) (δ : Path b c)
    (hγ : Set.range γ ⊆ s) (hδ : Set.range δ ⊆ s)
    (hγδ : Set.range (γ.trans δ) ⊆ s) :
    (γ.trans δ).codRestrict hγδ = (γ.codRestrict hγ).trans (δ.codRestrict hδ) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change (((γ.trans δ).codRestrict hγδ).map continuous_subtype_val) t =
    (((γ.codRestrict hγ).trans (δ.codRestrict hδ)).map continuous_subtype_val) t
  rw [codRestrict_map_subtypeVal, Path.map_trans,
    codRestrict_map_subtypeVal, codRestrict_map_subtypeVal]

/-- Corestricting the inclusion of a subspace path recovers that path. -/
@[simp]
theorem map_subtypeVal_codRestrict {a b : s} (γ : Path a b)
    (h : Set.range (γ.map continuous_subtype_val) ⊆ s) :
    (γ.map continuous_subtype_val).codRestrict h = γ := by
  ext t
  rfl

/-- A based ambient homotopy between paths in a subspace gives a homotopy in that
subspace if its whole range is contained there. -/
theorem Homotopic.of_subtypeVal {a b : s} {γ δ : Path a b}
    (H : (γ.map continuous_subtype_val).Homotopy (δ.map continuous_subtype_val))
    (hH : Set.range H ⊆ s) : γ.Homotopic δ := by
  refine ⟨{
    toFun := fun z => ⟨H z, hH ⟨z, rfl⟩⟩
    continuous_toFun := H.continuous.subtype_mk _
    map_zero_left := fun t => Subtype.ext (H.map_zero_left t)
    map_one_left := fun t => Subtype.ext (H.map_one_left t)
    prop' := fun t x hx => Subtype.ext (ContinuousMap.HomotopyRel.eq_fst H t hx) }⟩

end Path
