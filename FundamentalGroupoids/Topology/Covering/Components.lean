/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Monodromy
public import Mathlib.Data.Setoid.Basic

/-!
# Monodromy orbit classes and path components

Over a path-connected base, the monodromy orbit classes of a point fiber of a covering map
are equivalent to the path components of its total space. The equivalence sends the class
of a fiber point `e` to `ZerothHomotopy.mk e.val`. The total space need not be nonempty or
locally path-connected, and the covering map need not be surjective.

The representative formula determines the forward map uniquely by the quotient universal
property, `Setoid.lift_unique` or `Setoid.liftEquiv`. The inverse representative formula
follows from the inverse laws for equivalences.

The construction uses the orbit–path correspondence in
`IsCoveringMap.exists_monodromy_eq_iff_joined` and the fact that every path component meets
the chosen fiber, `IsCoveringMap.comp_subtypeVal_pathComponent_surjective`. The action,
orbit quotient and path-component carrier are Mathlib's constructions.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 3, §§2–4, for monodromy
  background, especially the discussion on p. 25.
* Junyan Xu, `Mathlib.Topology.Homotopy.Lifting`, for covering-space monodromy and the
  component-meets-fiber theorem.
* Mathlib's `MulAction.orbitRel.Quotient`, `ZerothHomotopy`, and quotient universal property.
-/

@[expose] public section

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}

namespace IsCoveringMap

variable (cov : IsCoveringMap p)

-- The kernel of the component-class map is exactly the monodromy orbit relation.
-- No path-connectedness assumption on the base is needed.
private theorem monodromyOrbit_ker (b : B) :
    Setoid.ker (fun e : p ⁻¹' {b} ↦ ZerothHomotopy.mk e.val) =
      @MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b) := by
  let := cov.fundamentalGroupMulAction b
  refine Setoid.ext fun e e' ↦ ?_
  rw [Setoid.ker_def, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨fun h ↦ (cov.exists_monodromy_eq_iff_joined e' e).mpr
      (Joined.symm (Quotient.exact h)),
    fun h ↦ Quotient.sound
      (Joined.symm ((cov.exists_monodromy_eq_iff_joined e' e).mp h))⟩

-- Every path component is represented by a point of the chosen fiber.
include cov in
private theorem monodromyOrbit_surjective (b : B) [PathConnectedSpace B] :
    Function.Surjective (fun e : p ⁻¹' {b} ↦ ZerothHomotopy.mk e.val) := by
  intro c
  obtain ⟨e, rfl⟩ := ZerothHomotopy.mk_surjective c
  obtain ⟨a, ha⟩ := cov.comp_subtypeVal_pathComponent_surjective e b
  refine ⟨⟨a.val, ha⟩, ?_⟩
  exact Quotient.sound (mem_pathComponent_iff.mp a.property).symm

/-- Monodromy orbit classes in a point fiber of a covering map correspond to path components
of the total space over a path-connected base. This uses the covering map's canonical
fundamental-group action and allows an empty total space. -/
noncomputable def monodromyOrbitEquivZerothHomotopy (b : B) [hB : PathConnectedSpace B] :
    @MulAction.orbitRel.Quotient (FundamentalGroup B b) (p ⁻¹' {b}) _
      (cov.fundamentalGroupMulAction b) ≃ ZerothHomotopy E := by
  letI := cov.fundamentalGroupMulAction b
  -- `let` retains the Prop-valued term `by` boundary for private lemmas.
  -- Tactic `have` would strip that boundary.
  let hdesc : MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) ≤
      Setoid.ker (fun e : p ⁻¹' {b} ↦ ZerothHomotopy.mk e.val) := by
    exact le_of_eq (monodromyOrbit_ker cov b).symm
  exact Equiv.ofBijective (Quotient.lift (fun e ↦ ZerothHomotopy.mk e.val) hdesc) (by
    exact ⟨(Setoid.lift_injective_iff_ker_eq_of_le hdesc).mpr (monodromyOrbit_ker cov b),
      Quotient.lift_surjective _ hdesc (monodromyOrbit_surjective cov b)⟩)

/-- The orbit class of a fiber point maps to its path component in the total space. -/
@[simp] theorem monodromyOrbitEquivZerothHomotopy_apply (b : B) [PathConnectedSpace B]
    (e : p ⁻¹' {b}) :
    cov.monodromyOrbitEquivZerothHomotopy b
      (Quotient.mk (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b)) e) = ZerothHomotopy.mk e.val := rfl

/-- The component of a fiber point maps back to its monodromy orbit class. -/
@[simp] theorem monodromyOrbitEquivZerothHomotopy_symm_apply (b : B) [PathConnectedSpace B]
    (e : p ⁻¹' {b}) :
    (cov.monodromyOrbitEquivZerothHomotopy b).symm (ZerothHomotopy.mk e.val) =
      Quotient.mk (@MulAction.orbitRel (FundamentalGroup B b) (p ⁻¹' {b}) _
        (cov.fundamentalGroupMulAction b)) e := by
  rw [← cov.monodromyOrbitEquivZerothHomotopy_apply b e]
  exact (cov.monodromyOrbitEquivZerothHomotopy b).symm_apply_apply _

end IsCoveringMap
