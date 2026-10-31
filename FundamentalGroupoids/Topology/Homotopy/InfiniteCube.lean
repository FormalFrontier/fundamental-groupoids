/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Cube
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace
public import FundamentalGroupoids.Topology.Homotopy.Relative

/-!
# Generalized loops with infinitely many coordinates

For an infinite index type, the generalized loop space `GenLoop N X x` is
contractible in its subtype topology from the compact-open topology on
continuous maps. Every such loop is also homotopic relative to the coordinate-face
boundary to the constant loop. Consequently, the corresponding homotopy group is
a subsingleton, without separation assumptions on the target.

The boundary is dense, so continuity puts every value of a generalized loop in
the closure of the singleton containing its basepoint. The resulting pointwise
specializations show that the constant loop specializes to every loop, giving
contractibility of the loop space. The canonical comparison with paths and path
components then gives relative nullhomotopies and collapse of the homotopy
quotient. An individual loop need not be pointwise constant.

## References

* Mathlib's `Mathlib.Topology.Homotopy.HomotopyGroup` supplies generalized loops,
  their relative homotopy relation and its quotient.
* Mathlib's `Set.MapsTo.closure` and `specializes_iff_mem_closure` relate
  continuity and closure to specialization.
-/

@[expose] public section

universe u v

open scoped unitInterval Topology

namespace GenLoop

variable {N : Type u} [Infinite N] {X : Type v} [TopologicalSpace X] {x : X}

/-- Every value of a generalized loop with infinitely many coordinates lies in
the closure of the singleton containing its basepoint. -/
theorem mem_closure_singleton_of_infinite (γ : GenLoop N X x) (s : I^N) :
    γ s ∈ closure ({x} : Set X) := by
  have hboundary : Set.MapsTo γ (Cube.boundary N) ({x} : Set X) := by
    intro s hs
    exact Set.mem_singleton_iff.mpr (GenLoop.boundary γ s hs)
  exact hboundary.closure γ.1.continuous (Cube.dense_boundary N s)

/-- The constant loop specializes to every generalized loop with infinitely many
coordinates, in the subtype topology on the space of continuous maps. -/
theorem const_specializes_of_infinite (γ : GenLoop N X x) :
    (GenLoop.const : GenLoop N X x) ⤳ γ := by
  apply (subtype_specializes_iff _ _).mpr
  apply ContinuousMap.specializes_coe.mp
  exact specializes_pi.mpr fun s ↦
    specializes_iff_mem_closure.mpr (GenLoop.mem_closure_singleton_of_infinite γ s)

/-- The generalized loop space with infinitely many coordinates is contractible
in its subtype topology from the compact-open topology on continuous maps,
without separation assumptions on the target. -/
theorem contractibleSpace_of_infinite (N : Type u) [Infinite N] (X : Type v)
    [TopologicalSpace X] (x : X) : ContractibleSpace (GenLoop N X x) :=
  contractibleSpace_of_specializes (GenLoop.const : GenLoop N X x)
    (fun γ ↦ GenLoop.const_specializes_of_infinite γ)

/-- A generalized loop with infinitely many coordinates is homotopic relative to
its boundary to the constant loop, without separation assumptions on the target. -/
theorem homotopic_const_of_infinite (γ : GenLoop N X x) :
    GenLoop.Homotopic γ (GenLoop.const : GenLoop N X x) := by
  let : ContractibleSpace (GenLoop N X x) :=
    GenLoop.contractibleSpace_of_infinite N X x
  exact (GenLoop.homotopic_iff_joined γ GenLoop.const).mpr
    (PathConnectedSpace.joined γ GenLoop.const)

end GenLoop

namespace HomotopyGroup

/-- The homotopy group indexed by an infinite type has only one homotopy class,
without separation assumptions on the target. -/
theorem subsingleton_of_infinite (N : Type u) [Infinite N] (X : Type v)
    [TopologicalSpace X] (x : X) : Subsingleton (HomotopyGroup N X x) := by
  let : ContractibleSpace (GenLoop N X x) :=
    GenLoop.contractibleSpace_of_infinite N X x
  refine ⟨fun a b ↦ (HomotopyGroup.equivZerothHomotopy N x).injective ?_⟩
  exact Subsingleton.elim _ _

end HomotopyGroup
