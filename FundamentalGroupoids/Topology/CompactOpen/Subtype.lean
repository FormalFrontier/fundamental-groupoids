/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# Compact-open maps into an arbitrary subspace

For an arbitrary subset `S` of a space `Y`, continuous maps from `X` to `S` are
homeomorphic to the subspace of continuous maps from `X` to `Y` whose values lie
in `S`. Both mapping spaces carry their ordinary compact-open topologies, and
both subspaces carry their induced topologies. No local compactness, closedness,
separation, or inhabitance assumption is needed.

The homeomorphism is ordinary postcomposition by the subtype inclusion. Its
inverse retains the original value at every point. The topological assertion
uses `ContinuousMap.isEmbedding_postcomp` for that inclusion.
-/

@[expose] public section

universe x y

open Topology

namespace Homeomorph

variable (X : Type x) {Y : Type y} [TopologicalSpace X] [TopologicalSpace Y]

/-- Continuous maps into an arbitrary subspace are homeomorphic to the subspace
of ordinary compact-open maps whose values lie in that subset. -/
def continuousMapSubtype (S : Set Y) :
    C(X, S) ≃ₜ {f : C(X, Y) // ∀ x : X, f x ∈ S} := by
  let i : C(S, Y) := ContinuousMap.subtypeVal S
  let e : C(X, S) ≃ {f : C(X, Y) // ∀ x : X, f x ∈ S} :=
    { toFun := fun f => ⟨i.comp f, fun x => (f x).property⟩
      invFun := fun f =>
        ⟨fun x => ⟨f.val x, f.property x⟩,
          f.val.continuous.subtype_mk (fun x => f.property x)⟩
      left_inv := by
        intro f
        apply ContinuousMap.ext
        intro x
        rfl
      right_inv := by
        intro f
        apply Subtype.ext
        apply ContinuousMap.ext
        intro x
        rfl }
  have hi : IsEmbedding (i.comp : C(X, S) → C(X, Y)) :=
    ContinuousMap.isEmbedding_postcomp i
      (show IsEmbedding (i : S → Y) from Topology.IsEmbedding.subtypeVal)
  refine
    { toEquiv := e
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · exact hi.continuous.subtype_mk (fun f x => (f x).property)
  · exact hi.isInducing.continuous_iff.2
      (show Continuous (fun f : {f : C(X, Y) // ∀ x : X, f x ∈ S} =>
        i.comp (e.invFun f)) from continuous_subtype_val)

/-- The whole underlying continuous map is postcomposition by the inclusion. -/
@[simp]
theorem continuousMapSubtype_apply_val (S : Set Y) (f : C(X, S)) :
    ((continuousMapSubtype X S) f).val = (ContinuousMap.subtypeVal S).comp f := rfl

/-- The whole forward operator becomes ordinary postcomposition after forgetting
the range constraint. -/
theorem coe_continuousMapSubtype_val (S : Set Y) :
    (fun f : C(X, S) => ((continuousMapSubtype X S) f).val) =
      ((ContinuousMap.subtypeVal S).comp : C(X, S) → C(X, Y)) := rfl

/-- The forward map preserves every original value in the ambient space. -/
theorem continuousMapSubtype_apply_apply (S : Set Y) (f : C(X, S)) (x : X) :
    ((continuousMapSubtype X S) f).val x = (f x).val := rfl

/-- The whole inverse function is the pointwise subtype-valued restriction. -/
theorem coe_continuousMapSubtype_symm_apply (S : Set Y)
    (f : {f : C(X, Y) // ∀ x : X, f x ∈ S}) :
    ⇑((continuousMapSubtype X S).symm f) =
      fun x => (⟨f.val x, f.property x⟩ : S) := rfl

/-- Forgetting the subtype after applying the inverse recovers the whole original
continuous map. -/
@[simp]
theorem subtypeVal_comp_continuousMapSubtype_symm_apply (S : Set Y)
    (f : {f : C(X, Y) // ∀ x : X, f x ∈ S}) :
    (ContinuousMap.subtypeVal S).comp ((continuousMapSubtype X S).symm f) =
      f.val := rfl

/-- The inverse map preserves every original value in the ambient space. -/
@[simp]
theorem continuousMapSubtype_symm_apply_apply_val (S : Set Y)
    (f : {f : C(X, Y) // ∀ x : X, f x ∈ S}) (x : X) :
    (((continuousMapSubtype X S).symm f) x).val = f.val x := rfl

end Homeomorph

namespace ContinuousMap

variable {X : Type x} {Y : Type y} [TopologicalSpace X] [TopologicalSpace Y]

/-- The range of postcomposition by a subtype inclusion consists exactly of the
continuous maps whose values lie in that subset. -/
theorem range_postcomp_subtypeVal (S : Set Y) :
    Set.range ((ContinuousMap.subtypeVal S).comp : C(X, S) → C(X, Y)) =
      {f : C(X, Y) | ∀ x : X, f x ∈ S} := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact fun x => (g x).property
  · intro hf
    refine ⟨(Homeomorph.continuousMapSubtype X S).symm ⟨f, hf⟩, ?_⟩
    exact Homeomorph.subtypeVal_comp_continuousMapSubtype_symm_apply X S ⟨f, hf⟩

end ContinuousMap
