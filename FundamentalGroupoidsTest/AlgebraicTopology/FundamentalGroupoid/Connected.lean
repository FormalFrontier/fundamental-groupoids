/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.Connected
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.CategoryTheory.Groupoid.Discrete

/-!
# Vertex inclusions and connectedness on the interval

The vertex-group inclusion at zero in the fundamental groupoid of the unit interval gives an
equivalence with identity arrow map. The endpoint one lies in its essential image but not in its
object image. Path-connectedness of the interval follows from convexity.

The inclusion at `false` in `Discrete Bool` is full and faithful but misses `true` even up to
isomorphism. The empty space and its fundamental groupoid are both not connected in the
corresponding senses.
-/

open CategoryTheory unitInterval

namespace FundamentalGroupoidsTest.FundamentalGroupoid

private instance : PathConnectedSpace I :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).isPathConnected ⟨0, unitInterval.zero_mem⟩)

private theorem interval_vertex_equivalence_and_endpoint_images (p : FundamentalGroup I 0) :
    let F := SingleObj.functor (MonoidHom.id (End (FundamentalGroupoid.mk (0 : I))))
    let e : SingleObj (FundamentalGroup I 0) ≌ FundamentalGroupoid I := F.asEquivalence
    e.functor = F ∧
      e.functor.map (X := SingleObj.star (FundamentalGroup I 0))
        (Y := SingleObj.star (FundamentalGroup I 0)) p = p ∧
      F.essImage (FundamentalGroupoid.mk (1 : I)) ∧
      FundamentalGroupoid.mk (1 : I) ∉ Set.range F.obj ∧
      FundamentalGroupoid.mk (0 : I) ≠ FundamentalGroupoid.mk (1 : I) ∧
      Joined (0 : I) 1 := by
  have h01 : (0 : I) ≠ 1 := fun h => zero_ne_one (congrArg Subtype.val h)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Functor.asEquivalence_functor _
  · rfl
  · exact Functor.EssSurj.mem_essImage _ _
  · rintro ⟨a, ha⟩
    apply h01
    have h : FundamentalGroupoid.mk (0 : I) = FundamentalGroupoid.mk (1 : I) := by
      simpa only [SingleObj.functor_obj] using ha
    exact congrArg FundamentalGroupoid.as h
  · intro h
    exact h01 (congrArg FundamentalGroupoid.as h)
  · exact PathConnectedSpace.joined _ _

private theorem discrete_bool_vertex_full_faithful_misses_true :
    let F := SingleObj.functor (MonoidHom.id (End (Discrete.mk false)))
    F.Full ∧ F.Faithful ∧ ¬ F.essImage (Discrete.mk true) := by
  dsimp only
  refine ⟨inferInstance, inferInstance, ?_⟩
  rintro ⟨a, ⟨e⟩⟩
  have h : false = true := by
    simpa only [SingleObj.functor_obj] using Discrete.eq_of_hom e.hom
  cases h

/-- The empty space is not path-connected, and its fundamental groupoid is not connected. -/
public theorem empty_not_pathConnectedSpace_and_not_isConnected :
    ¬ PathConnectedSpace Empty ∧
      ¬ CategoryTheory.IsConnected (FundamentalGroupoid Empty) := by
  have h : ¬ PathConnectedSpace Empty := by
    intro h
    obtain ⟨x⟩ := h.nonempty
    exact Empty.elim x
  exact ⟨h, fun hc =>
    h ((FundamentalGroupoid.pathConnectedSpace_iff_isConnected (X := Empty)).mpr hc)⟩

end FundamentalGroupoidsTest.FundamentalGroupoid
