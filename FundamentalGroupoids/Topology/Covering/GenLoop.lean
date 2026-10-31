/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.Lifting
public import FundamentalGroupoids.Topology.Homotopy.Cube
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Based generalized-loop lifts through covering maps

A covering map has a chosen lift of each based generalized loop whose cube index
has at least two elements. The lift is based at a supplied point of the total
space and maps back to the given loop under `GenLoop.map`. It is unique among
based generalized loops with this property.

The underlying continuous map is chosen using
`IsCoveringMap.existsUnique_continuousMap_lifts` at the zero vertex. The cube is
contractible and locally path connected, even for an infinite index type. The
boundary condition uses path connectedness of the coordinate-face boundary and
discreteness of the original covering's fiber. No connectedness, separation or
local path connectedness of the total or base space, or global surjectivity of
the covering, is assumed.

## References

* Mathlib's `Mathlib.Topology.Homotopy.Lifting`, especially Junyan Xu's unique
  continuous lifting construction.
* Mathlib's generalized loops and homotopy groups, by Roberto Alvarez.
* Mathlib's convex contractibility and homotopy equivalences, by Yury Kudryashov,
  Praneeth Kolichala and contributors, and locally convex spaces, by Anatole
  Dedecker and contributors.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped unitInterval Topology

namespace IsCoveringMap

variable {N : Type u} {E : Type v} {B : Type w}
variable [TopologicalSpace E] [TopologicalSpace B] {q : E → B}

private def continuousMapLiftGenLoop [Nonempty N] (hq : IsCoveringMap q)
    (e : E) (α : GenLoop N B (q e)) :
    { F : C(I^N, E) // (F 0 = e ∧ q ∘ F = α.1) ∧
      ∀ G : C(I^N, E), G 0 = e ∧ q ∘ G = α.1 → G = F } := by
  have hI : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc _ _
  letI : ContractibleSpace I := hI.contractibleSpace ⟨0, unitInterval.zero_mem⟩
  letI : LocallyPathConnectedSpace I := hI.locallyPathConnectedSpace
  letI : PathConnectedSpace I := inferInstance
  let hCube : ContinuousMap.HomotopyEquiv (I^N) (N → Unit) :=
    ContinuousMap.HomotopyEquiv.piCongrRight
      (fun _ : N ↦ Classical.choice (ContractibleSpace.hequiv_unit I))
  letI : ContractibleSpace (I^N) := hCube.contractibleSpace
  letI : SimplyConnectedSpace (I^N) := SimplyConnectedSpace.ofContractible _
  letI : LocallyPathConnectedSpace (I^N) := Pi.locallyPathConnectedSpace
  let h := hq.existsUnique_continuousMap_lifts α.1 0 e
    (GenLoop.boundary α 0 (Cube.zero_mem_boundary N)).symm
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

variable [Nontrivial N]

/-- The based lift of a generalized loop through a covering map, chosen to take
zero to the supplied point. The cube index has at least two elements so that
its coordinate-face boundary is path connected. -/
def liftGenLoop (hq : IsCoveringMap q) (e : E) (α : GenLoop N B (q e)) :
    GenLoop N E e := private_decl% (
  ⟨(continuousMapLiftGenLoop hq e α).1, by
    intro t ht
    have hproj : ∀ s ∈ Cube.boundary N,
        q ((continuousMapLiftGenLoop hq e α).1 s) = q e := by
      intro s hs
      exact (congrFun (continuousMapLiftGenLoop hq e α).2.1.2 s).trans
        (GenLoop.boundary α s hs)
    exact (hq.constOn_of_comp
      (Cube.isPathConnected_boundary N).isConnected.isPreconnected
      (continuousMapLiftGenLoop hq e α).1.continuous.continuousOn
      (fun s hs s' hs' ↦ (hproj s hs).trans (hproj s' hs').symm)
      ht (Cube.zero_mem_boundary N)).trans
        (continuousMapLiftGenLoop hq e α).2.1.1⟩)

/-- Mapping the chosen based lift through the covering recovers the given loop. -/
@[simp]
theorem map_liftGenLoop (hq : IsCoveringMap q) (e : E) (α : GenLoop N B (q e)) :
    GenLoop.map ⟨q, hq.continuous⟩ rfl (hq.liftGenLoop e α) = α := by
  apply GenLoop.ext
  intro t
  exact congrFun (continuousMapLiftGenLoop hq e α).2.1.2 t

/-- The chosen lift takes the zero vertex to the supplied point. -/
@[simp]
theorem liftGenLoop_zero (hq : IsCoveringMap q) (e : E) (α : GenLoop N B (q e)) :
    hq.liftGenLoop e α 0 = e :=
  (continuousMapLiftGenLoop hq e α).2.1.1

/-- Any based generalized loop mapping to the given loop is its chosen lift. -/
theorem liftGenLoop_unique (hq : IsCoveringMap q) (e : E) (α : GenLoop N B (q e))
    (β : GenLoop N E e) (hβ : GenLoop.map ⟨q, hq.continuous⟩ rfl β = α) :
    β = hq.liftGenLoop e α := by
  apply Subtype.ext
  apply (continuousMapLiftGenLoop hq e α).2.2 β.1
  refine ⟨GenLoop.boundary β 0 (Cube.zero_mem_boundary N), ?_⟩
  funext t
  exact congrArg (fun γ : GenLoop N B (q e) ↦ γ t) hβ

/-- Lifting the image of a based generalized loop returns that loop. -/
@[simp]
theorem liftGenLoop_map (hq : IsCoveringMap q) (e : E) (β : GenLoop N E e) :
    hq.liftGenLoop e (GenLoop.map ⟨q, hq.continuous⟩ rfl β) = β :=
  (hq.liftGenLoop_unique e (GenLoop.map ⟨q, hq.continuous⟩ rfl β) β rfl).symm

end IsCoveringMap
