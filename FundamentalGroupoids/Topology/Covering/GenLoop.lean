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
# Coverings on compact-open generalized-loop spaces

A covering map has a chosen lift of each based generalized loop whose cube index
has at least two elements. The lift is based at a supplied point of the total
space and maps back to the given loop under `GenLoop.map`. It is unique among
based generalized loops with this property.

With the inherited compact-open topologies, `IsCoveringMap.genLoopHomeomorph`
identifies the based generalized-loop spaces of the total and base spaces. Its
forward map is `GenLoop.map` and its inverse is `IsCoveringMap.liftGenLoop`.
The chosen lift is natural in commuting squares with arbitrary continuous
horizontal maps, and the forward homeomorphism agrees with
`HomotopyGroup.mapFun` on representative classes.

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

section

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

end

variable {N : Type u} {E : Type v} {X : Type w}
variable [TopologicalSpace E] [TopologicalSpace X] {p : E → X} [Nontrivial N]

/-- The chosen based lift is continuous for the inherited compact-open topologies. -/
@[fun_prop]
theorem continuous_liftGenLoop (hp : IsCoveringMap p) (e : E) :
    Continuous (hp.liftGenLoop (N := N) e) := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty N)
  let Γ := GenLoop N X (p e)
  let A := Γ × ({j : N // j ≠ i} → I)
  -- Use one cube coordinate as time, keeping the loop and other coordinates as parameters.
  have hcoord : Continuous (fun z : I × A ↦ Cube.insertAt i (z.1, z.2.2)) :=
    (Cube.insertAt i).continuous.comp (continuous_fst.prodMk continuous_snd.snd)
  have hloop : Continuous (fun z : I × A ↦ z.2.1) := continuous_snd.fst
  let H : C(I × A, X) :=
    ⟨fun z ↦ z.2.1 (Cube.insertAt i (z.1, z.2.2)), hloop.eval hcoord⟩
  have hlift : Continuous (fun z : I × A ↦
      hp.liftGenLoop e z.2.1 (Cube.insertAt i (z.1, z.2.2))) := by
    apply hp.isLocalHomeomorph.continuous_lift hp.isSeparatedMap H
    · funext z
      exact congrArg (fun α : GenLoop N X (p e) ↦
        α (Cube.insertAt i (z.1, z.2.2))) (hp.map_liftGenLoop e z.2.1)
    · have hzero : (fun a : A ↦ hp.liftGenLoop e a.1 (Cube.insertAt i (0, a.2))) =
          (fun _ : A ↦ e) := by
        funext a
        exact GenLoop.boundary (hp.liftGenLoop e a.1) _
          (Cube.insertAt_boundary i (Or.inl (Or.inl rfl)))
      exact hzero.symm ▸ (continuous_const : Continuous fun _ : A ↦ e)
    · intro a
      have hrest : Continuous (fun _ : I ↦ a.2) := continuous_const
      exact (hp.liftGenLoop e a.1).1.continuous.comp
        ((Cube.insertAt i).continuous.comp (continuous_id.prodMk hrest))
  have hsplit : Continuous (fun z : Γ × (N → I) ↦ Cube.splitAt i z.2) :=
    (Cube.splitAt i).continuous.comp continuous_snd
  have hparam : Continuous (fun z : Γ × (N → I) ↦
      ((Cube.splitAt i z.2).1, (z.1, (Cube.splitAt i z.2).2))) :=
    hsplit.fst.prodMk (continuous_fst.prodMk hsplit.snd)
  apply continuous_induced_rng.mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  simpa only [Function.comp_def, Function.uncurry_def, GenLoop.coe_coe, Cube.insertAt,
    Cube.splitAt, Prod.mk.eta, Homeomorph.symm_apply_apply] using hlift.comp hparam

/-- A covering map identifies the based generalized-loop spaces homeomorphically
when the cube index has at least two elements. The forward map is based
postcomposition and the inverse is the chosen based lift. -/
noncomputable def genLoopHomeomorph (hp : IsCoveringMap p)
    (N : Type u) [Nontrivial N] (e : E) :
    GenLoop N E e ≃ₜ GenLoop N X (p e) where
  toFun := GenLoop.map ⟨p, hp.continuous⟩ rfl
  invFun := hp.liftGenLoop e
  left_inv := hp.liftGenLoop_map e
  right_inv := hp.map_liftGenLoop e
  continuous_toFun := GenLoop.continuous_map ⟨p, hp.continuous⟩ rfl
  continuous_invFun := hp.continuous_liftGenLoop e

/-- The covering homeomorphism acts by based postcomposition. -/
@[simp]
theorem genLoopHomeomorph_apply (hp : IsCoveringMap p) (e : E)
    (β : GenLoop N E e) :
    hp.genLoopHomeomorph N e β = GenLoop.map ⟨p, hp.continuous⟩ rfl β := by
  rfl

/-- The inverse covering homeomorphism is the chosen based lift. -/
@[simp]
theorem genLoopHomeomorph_symm_apply (hp : IsCoveringMap p) (e : E)
    (α : GenLoop N X (p e)) :
    (hp.genLoopHomeomorph N e).symm α = hp.liftGenLoop e α := by
  rfl

universe v' w'

/-- Chosen based generalized-loop lifts are natural in a commuting square of
covering maps. The horizontal maps need only be continuous. -/
theorem liftGenLoop_naturality
    {E' : Type v'} {X' : Type w'} [TopologicalSpace E'] [TopologicalSpace X']
    {q : E' → X'} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (F : C(E, E')) (G : C(X, X')) (e : E) (e' : E')
    (hF : F e = e') (hcomm : ∀ a, q (F a) = G (p a))
    (α : GenLoop N X (p e)) :
    GenLoop.map F hF (hp.liftGenLoop e α) =
      hq.liftGenLoop e'
        (GenLoop.map G ((hcomm e).symm.trans (congrArg q hF)) α) := by
  refine hq.liftGenLoop_unique e'
    (GenLoop.map G ((hcomm e).symm.trans (congrArg q hF)) α)
    (GenLoop.map F hF (hp.liftGenLoop e α)) ?_
  apply GenLoop.ext
  intro t
  exact (hcomm (hp.liftGenLoop e α t)).trans
    (congrArg G (congrArg (fun γ : GenLoop N X (p e) ↦ γ t)
      (hp.map_liftGenLoop e α)))

/-- On representative classes, based postcomposition on the homotopy quotient
agrees with the forward covering homeomorphism, without a group structure. -/
theorem genLoopHomeomorph_mapFun_class (hp : IsCoveringMap p) (e : E)
    (β : GenLoop N E e) :
    HomotopyGroup.mapFun N ⟨p, hp.continuous⟩ rfl
        (⟦β⟧ : HomotopyGroup N E e) =
      (⟦hp.genLoopHomeomorph N e β⟧ : HomotopyGroup N X (p e)) := by
  exact HomotopyGroup.mapFun_class N ⟨p, hp.continuous⟩ rfl β

end IsCoveringMap
