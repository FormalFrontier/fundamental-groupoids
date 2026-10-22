/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.SemilocallySimplyConnected.Basic
public import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Locally path-connected refinement of semilocal simple connectivity

In a locally path-connected space, semilocal simple connectivity at `x` gives
an open path-connected neighborhood `V` of `x` whose loops at every basepoint
in `V` are nullhomotopic in the ambient space. The homotopies need not stay
in `V`, and no simple connectivity of the subspace `V` is asserted.

The basepoint-transfer argument only needs a path-connected subset, not local
path connectedness. It uses the naturality of fundamental-group change of
basepoint for the inclusion of that subset.

## References

The proof uses Mathlib's `isOpen_isPathConnected_basis` and paths in a
path-connected subset, together with the inclusion-range criterion and
change-of-basepoint naturality in `FundamentalGroupoids.FundamentalGroup`.
-/

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X]

/-- If all loops in a path-connected set based at one of its points are
nullhomotopic in the ambient space, the same holds at every point of the set.
Neither openness nor local path connectedness is needed for this transfer. -/
theorem IsPathConnected.forall_loops_homotopic_refl {U : Set X}
    (hU : IsPathConnected U) {x : X} (hx : x ∈ U)
    (hloops : ∀ γ : Path x x, Set.range γ ⊆ U → γ.Homotopic (Path.refl x)) :
    ∀ y ∈ U, ∀ γ : Path y y, Set.range γ ⊆ U → γ.Homotopic (Path.refl y) := by
  have hxmap : FundamentalGroup.map (ContinuousMap.subtypeVal U) ⟨x, hx⟩ = 1 :=
    MonoidHom.range_eq_bot_iff.mp
      ((FundamentalGroup.range_map_subtypeVal_eq_bot_iff hx).mpr hloops)
  intro y hy
  apply (FundamentalGroup.range_map_subtypeVal_eq_bot_iff hy).mp
  apply MonoidHom.range_eq_bot_iff.mpr
  apply MonoidHom.ext
  intro γ
  obtain ⟨a⟩ := (joinedIn_iff_joined hx hy).mp (hU.joinedIn x hx y hy)
  obtain ⟨δ, rfl⟩ := (FundamentalGroup.fundamentalGroupMulEquivOfPath a).surjective γ
  simp only [FundamentalGroup.map_fundamentalGroupMulEquivOfPath, hxmap,
    MonoidHom.one_apply, map_one]

namespace IsSemilocallySimplyConnectedAt

/-- In a locally path-connected space, a semilocally simply connected point has
an open path-connected neighborhood all of whose loops, at every basepoint in
the neighborhood, are nullhomotopic in the ambient space. -/
theorem exists_isOpen_isPathConnected [LocallyPathConnectedSpace X] {x : X}
    (h : IsSemilocallySimplyConnectedAt x) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsPathConnected V ∧
      ∀ y ∈ V, ∀ γ : Path y y, Set.range γ ⊆ V → γ.Homotopic (Path.refl y) := by
  obtain ⟨U, hU, hx, hloops⟩ := h.exists_isOpen
  obtain ⟨V, ⟨hV, hxV, hVpc⟩, hVU⟩ :=
    (isOpen_isPathConnected_basis x).mem_iff.mp (hU.mem_nhds hx)
  refine ⟨V, hV, hxV, hVpc, ?_⟩
  exact hVpc.forall_loops_homotopic_refl hxV (fun γ hγ => hloops γ (hγ.trans hVU))

end IsSemilocallySimplyConnectedAt

/-- Under local path connectedness, semilocal simple connectivity at `x` is
equivalent to an open path-connected neighborhood with ambient nullhomotopies
for loops at every basepoint. The reverse implication uses only the loops at
`x` and does not need local path connectedness. -/
theorem isSemilocallySimplyConnectedAt_iff_exists_isOpen_isPathConnected
    [LocallyPathConnectedSpace X] (x : X) :
    IsSemilocallySimplyConnectedAt x ↔
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ IsPathConnected V ∧
        ∀ y ∈ V, ∀ γ : Path y y, Set.range γ ⊆ V → γ.Homotopic (Path.refl y) := by
  constructor
  · exact IsSemilocallySimplyConnectedAt.exists_isOpen_isPathConnected
  · rintro ⟨V, hV, hx, _, hloops⟩
    exact IsSemilocallySimplyConnectedAt.of_isOpen hV hx (hloops x hx)
