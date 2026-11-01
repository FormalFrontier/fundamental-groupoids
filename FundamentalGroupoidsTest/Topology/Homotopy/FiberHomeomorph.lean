/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber.Homeomorph

/-!
# Coordinate changes on projection homotopy fibers

Product coordinate homeomorphisms compare the fibers of the two projections,
without assuming that those projections are embeddings. A coordinate swap on
`I × I` changes both the starting point and an entire nonconstant path.
-/

@[expose] public section

open unitInterval
open scoped Topology
open ContinuousMap.HomotopyFiber

universe uX uX' uD

variable {X : Type uX} {X' : Type uX'} {D : Type uD}
variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace D]

-- The auxiliary space may be empty, and no injectivity of either projection is used.
example (h : X ≃ₜ X') (y : X) :
    ContinuousMap.HomotopyFiber (ContinuousMap.fst : C(X × D, X)) y ≃ₜ
      ContinuousMap.HomotopyFiber (ContinuousMap.snd : C(D × X', X')) (h y) :=
  homeomorph
    ((h.prodCongr (Homeomorph.refl D)).trans (Homeomorph.prodComm X' D))
    h (fun _ => rfl) rfl

-- A supplied d constructs a witness; the general construction needs no Nonempty D.
-- The input path t ↦ (t, 1) becomes t ↦ (1, t), not just the same pair of endpoints.
example (d : D) :
    let H :
        ContinuousMap.HomotopyFiber
            (ContinuousMap.fst : C((I × I) × D, I × I)) ((0, 1) : I × I) ≃ₜ
          ContinuousMap.HomotopyFiber
            (ContinuousMap.snd : C(D × (I × I), I × I)) ((1, 0) : I × I) :=
      homeomorph
        (((Homeomorph.prodComm I I).prodCongr (Homeomorph.refl D)).trans
          (Homeomorph.prodComm (I × I) D))
        (Homeomorph.prodComm I I) (fun _ => rfl) rfl
    let z : ContinuousMap.HomotopyFiber
        (ContinuousMap.fst : C((I × I) × D, I × I)) ((0, 1) : I × I) :=
      mk (((1, 1) : I × I), d)
        ((ContinuousMap.id I).prodMk (ContinuousMap.const I (1 : I))) rfl rfl
    point (H z) = (d, ((1, 1) : I × I)) ∧
      path (H z) = (ContinuousMap.const I (1 : I)).prodMk (ContinuousMap.id I) := by
  intro H z
  let e : (I × I) × D ≃ₜ D × (I × I) :=
    (((Homeomorph.prodComm I I).prodCongr (Homeomorph.refl D)).trans
      (Homeomorph.prodComm (I × I) D))
  constructor
  · exact point_homeomorph e (Homeomorph.prodComm I I) (fun _ => rfl) rfl z
  · exact (path_homeomorph e (Homeomorph.prodComm I I) (fun _ => rfl) rfl z).trans
      (ContinuousMap.ext fun _ => rfl)
