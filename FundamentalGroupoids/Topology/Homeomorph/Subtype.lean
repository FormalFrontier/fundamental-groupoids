/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Flattening nested subspaces

A subspace of a subspace defined by two predicates has the same topology as the
subspace defined by their conjunction. The carrier equivalence is Mathlib's
`Equiv.subtypeSubtypeEquivSubtypeInter`; the homeomorphism adds its continuity
properties without changing either function.
-/

@[expose] public section

namespace Homeomorph

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Flatten two nested subspaces into the subspace defined by the conjunction. -/
def subtypeSubtypeEquivSubtypeInter (p q : X → Prop) :
    {x : Subtype p // q x.1} ≃ₜ {x : X // p x ∧ q x} where
  toEquiv := Equiv.subtypeSubtypeEquivSubtypeInter p q
  continuous_toFun := by
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
      (fun x : {x : Subtype p // q x.1} => ⟨x.1.2, x.2⟩)
  continuous_invFun := by
    exact (continuous_subtype_val.subtype_mk
      (fun x : {x : X // p x ∧ q x} => x.2.1)).subtype_mk (fun x => x.2.2)

/-- Flattening subspaces retains the existing carrier equivalence. -/
@[simp]
theorem subtypeSubtypeEquivSubtypeInter_toEquiv (p q : X → Prop) :
    (subtypeSubtypeEquivSubtypeInter p q).toEquiv =
      Equiv.subtypeSubtypeEquivSubtypeInter p q :=
  rfl

@[simp]
theorem subtypeSubtypeEquivSubtypeInter_apply_coe (p q : X → Prop)
    (x : {x : Subtype p // q x.1}) :
    ((subtypeSubtypeEquivSubtypeInter p q x : {x : X // p x ∧ q x}) : X) = x.1.1 :=
  rfl

@[simp]
theorem subtypeSubtypeEquivSubtypeInter_symm_apply_coe (p q : X → Prop)
    (x : {x : X // p x ∧ q x}) :
    ((subtypeSubtypeEquivSubtypeInter p q).symm x).1.1 = x.1 :=
  rfl

end Homeomorph
