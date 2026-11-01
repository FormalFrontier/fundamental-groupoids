/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.CompactOpen

/-!
# Product-parameter continuity for topological colimits

A supplied topological colimit has its characteristic continuity property after
product with a parameter space `P`, for maps to `Y`, whenever
`LocallyCompactPair P Y` holds. In particular, local compactness of `P` suffices;
no separation condition on `Y` or local compactness of the diagram is needed.
The parameter, target, diagram, indexing-object and indexing-morphism universes
are independent. A one-point parameter recovers the ordinary continuity criterion.

## References

* The product-parameter continuity criterion originates in
  `SphereTopology.Topology.WidePushoutHomotopy` by Formal Frontier Agents.
* Mathlib's topological-colimit API by Patrick Massot, Kim Morrison, Mario
  Carneiro and Andrew Yang, and its concrete-colimit API, supply finality and
  representatives.
* Reid Barton's compact-open formalization supplies individual-map currying;
  Mathlib's evaluation and locally compact pair APIs supply joint evaluation.
* The free-path-space transposition used in the homotopy extension property
  motivates putting the parameter inside the continuous mapping space.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe j k d p y

namespace TopCat

/-- The characteristic continuity criterion for a supplied topological colimit,
with an independent product parameter and target. The pair hypothesis is used
only to evaluate continuous maps from the parameter space. -/
theorem continuous_prod_iff_of_isColimit {J : Type j} [Category.{k} J]
    {F : J ⥤ TopCat.{d}} (c : Cocone F) (hc : IsColimit c)
    {P : Type p} {Y : Type y} [TopologicalSpace P] [TopologicalSpace Y]
    [LocallyCompactPair P Y] (a : P × c.pt → Y) :
    Continuous a ↔ ∀ i, Continuous (fun z : P × F.obj i ↦ a (z.1, c.ι.app i z.2)) := by
  constructor
  · intro ha i
    exact ha.comp (continuous_fst.prodMk ((c.ι.app i).hom.continuous.comp continuous_snd))
  · intro ha
    have hs (x : c.pt) : Continuous (fun t : P ↦ a (t, x)) := by
      obtain ⟨i, z, rfl⟩ := Concrete.isColimit_exists_rep F hc x
      exact (ha i).comp (continuous_id.prodMk continuous_const)
    let b : c.pt → C(P, Y) := fun x ↦ ⟨fun t ↦ a (t, x), hs x⟩
    have hb : Continuous b := by
      apply (continuous_iff_of_isColimit c hc b).2
      intro i
      exact ContinuousMap.continuous_of_continuous_uncurry _ ((ha i).comp continuous_swap)
    exact (hb.comp continuous_snd).eval continuous_fst

/-- The ordinary colimit continuity criterion is recovered from the
product-parameter criterion by using a one-point parameter. -/
theorem continuous_iff_of_isColimit_unit {J : Type j} [Category.{k} J]
    {F : J ⥤ TopCat.{d}} (c : Cocone F) (hc : IsColimit c)
    {Y : Type y} [TopologicalSpace Y] (a : c.pt → Y) :
    Continuous a ↔ ∀ i, Continuous (a ∘ c.ι.app i) := by
  have hunit : Continuous (fun z : PUnit.{1} × c.pt ↦ a z.2) ↔ Continuous a :=
    ⟨fun h ↦ h.comp ((continuous_const (y := PUnit.unit)).prodMk continuous_id),
      fun h ↦ h.comp continuous_snd⟩
  rw [← hunit, continuous_prod_iff_of_isColimit c hc]
  constructor
  · intro h i
    exact (h i).comp ((continuous_const (y := PUnit.unit)).prodMk continuous_id)
  · intro h i
    exact (h i).comp continuous_snd

end TopCat
