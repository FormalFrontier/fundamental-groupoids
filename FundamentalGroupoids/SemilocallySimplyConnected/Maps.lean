/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.SemilocallySimplyConnected.Basic
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Semilocal simple connectivity and local homeomorphisms

Local homeomorphisms preserve semilocal simple connectivity at a chosen point.
A chart is shrunk inside a witnessing neighborhood, and loops in its image are
lifted through the resulting homeomorphism of subspaces. Their nullhomotopies
are taken in the whole source space and then mapped by the globally continuous
map; they need not stay in the chart.

Covering maps also reflect the pointwise property, since their induced maps on
fundamental groups are injective. Consequently the base property implies the
total-space property for every covering, including coverings with empty fibers.
Global descent requires surjectivity, and holds for local homeomorphisms without
any covering hypothesis.

## References

Mathlib's `OpenPartialHomeomorph.homeomorphOfImageSubsetSource` supplies the
restricted chart. Junyan Xu's covering path-homotopy injectivity in
`Mathlib.Topology.Homotopy.Lifting` supplies the based fundamental-group bridge.
-/

@[expose] public section

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

namespace IsLocalHomeomorph

/-- A local homeomorphism preserves semilocal simple connectivity at a chosen
point. The nullhomotopies in the source are ambient, not confined to a chart. -/
theorem isSemilocallySimplyConnectedAt {f : X → Y} (hf : IsLocalHomeomorph f) {x : X}
    (h : IsSemilocallySimplyConnectedAt x) : IsSemilocallySimplyConnectedAt (f x) := by
  obtain ⟨U, hU, hx, hloops⟩ := h.exists_isOpen
  obtain ⟨e, hxe, hfe⟩ := hf x
  let W : Set X := e.source ∩ U
  let V : Set Y := e '' W
  let g : W ≃ₜ V := e.homeomorphOfImageSubsetSource Set.inter_subset_left rfl
  let xW : W := ⟨x, hxe, hx⟩
  have hxV : f x ∈ V := by
    rw [hfe]
    exact ⟨x, ⟨hxe, hx⟩, rfl⟩
  refine IsSemilocallySimplyConnectedAt.of_isOpen
    (U := V) (e.isOpen_image_source_inter hU) hxV ?_
  intro γ hγ
  let γV : Path (g xW) (g xW) :=
    { toFun := fun t => ⟨γ t, hγ ⟨t, rfl⟩⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext (γ.source.trans (congrFun hfe x))
      target' := Subtype.ext (γ.target.trans (congrFun hfe x)) }
  let δ : Path x x :=
    { toFun := fun t => (g.symm (γV t)).val
      continuous_toFun := continuous_subtype_val.comp (g.symm.continuous.comp γV.continuous)
      source' := by
        rw [γV.source, g.symm_apply_apply]
      target' := by
        rw [γV.target, g.symm_apply_apply] }
  have hδ : Set.range δ ⊆ U := by
    rintro y ⟨t, rfl⟩
    exact (g.symm (γV t)).property.2
  have hmap : δ.map hf.continuous = γ := by
    apply Path.ext
    funext t
    change f (g.symm (γV t)).val = γ t
    calc
      f (g.symm (γV t)).val = e (g.symm (γV t)).val :=
        congrFun hfe (g.symm (γV t)).val
      _ = γ t := congrArg Subtype.val (g.apply_symm_apply (γV t))
  rw [← hmap]
  exact (hloops δ hδ).map ⟨f, hf.continuous⟩

/-- A surjective local homeomorphism descends global semilocal simple
connectivity. No covering-space hypothesis is needed. -/
theorem semilocallySimplyConnectedSpace_of_surjective {f : X → Y}
    (hf : IsLocalHomeomorph f) (hsurj : Function.Surjective f)
    [SemilocallySimplyConnectedSpace X] : SemilocallySimplyConnectedSpace Y := by
  refine SemilocallySimplyConnectedSpace.of_forall fun y => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  exact hf.isSemilocallySimplyConnectedAt (_root_.isSemilocallySimplyConnectedAt x)

end IsLocalHomeomorph

namespace IsCoveringMap

/-- A covering map induces an injective homomorphism on each based fundamental
group, by its injectivity on the homotopy classes of paths with fixed endpoints. -/
theorem injective_fundamentalGroup_map {f : X → Y} (hf : IsCoveringMap f) (x : X) :
    Function.Injective (FundamentalGroup.map ⟨f, hf.continuous⟩ x) :=
  hf.injective_path_homotopic_map x x

/-- For a covering map, semilocal simple connectivity at a point of the total
space is equivalent to the property at its image. Surjectivity is not needed. -/
theorem isSemilocallySimplyConnectedAt_iff {f : X → Y} (hf : IsCoveringMap f) (x : X) :
    IsSemilocallySimplyConnectedAt x ↔ IsSemilocallySimplyConnectedAt (f x) :=
  ⟨hf.isLocalHomeomorph.isSemilocallySimplyConnectedAt,
    fun h => IsSemilocallySimplyConnectedAt.of_injective_fundamentalGroup_map
      ⟨f, hf.continuous⟩ (hf.injective_fundamentalGroup_map x) h⟩

/-- The total space of a covering of a semilocally simply connected base is
semilocally simply connected, without any surjectivity assumption. -/
theorem semilocallySimplyConnectedSpace {f : X → Y} (hf : IsCoveringMap f)
    [SemilocallySimplyConnectedSpace Y] : SemilocallySimplyConnectedSpace X :=
  SemilocallySimplyConnectedSpace.of_forall fun x =>
    (hf.isSemilocallySimplyConnectedAt_iff x).mpr (_root_.isSemilocallySimplyConnectedAt (f x))

/-- A surjective covering descends semilocal simple connectivity from its total
space to its base. -/
theorem semilocallySimplyConnectedSpace_of_surjective {f : X → Y} (hf : IsCoveringMap f)
    (hsurj : Function.Surjective f) [SemilocallySimplyConnectedSpace X] :
    SemilocallySimplyConnectedSpace Y :=
  hf.isLocalHomeomorph.semilocallySimplyConnectedSpace_of_surjective hsurj

/-- For a surjective covering, global semilocal simple connectivity of the total
space is equivalent to global semilocal simple connectivity of the base. -/
theorem semilocallySimplyConnectedSpace_iff {f : X → Y} (hf : IsCoveringMap f)
    (hsurj : Function.Surjective f) :
    SemilocallySimplyConnectedSpace X ↔ SemilocallySimplyConnectedSpace Y := by
  constructor
  · intro h
    let : SemilocallySimplyConnectedSpace X := h
    exact hf.semilocallySimplyConnectedSpace_of_surjective hsurj
  · intro h
    let : SemilocallySimplyConnectedSpace Y := h
    exact hf.semilocallySimplyConnectedSpace

end IsCoveringMap
