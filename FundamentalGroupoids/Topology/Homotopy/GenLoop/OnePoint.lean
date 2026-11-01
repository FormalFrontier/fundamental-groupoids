/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Compactification.OnePoint.ContinuousMap
public import FundamentalGroupoids.Topology.Homotopy.Cube
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Generalized loops as maps out of a one-point compactification

For every finite index type `N`, the generalized-loop space `GenLoop N X x`
is homeomorphic to the continuous maps from the one-point compactification of
the complement of `Cube.boundary N` that take infinity to `x`. The topologies
are the inherited compact-open topologies, and the target requires only a
topology and a chosen point.

The forward map keeps the values of the generalized loop on the boundary
complement and assigns `x` at infinity. Its inverse precomposes with the
collapse of the cube boundary. The index type may be empty: in that case the
cube has one point and empty boundary, and the added point at infinity is
still distinct from the cube point.

## References

* Mathlib's `Mathlib.Topology.Homotopy.HomotopyGroup`, by Roberto Alvarez,
  supplies the cube boundary, generalized loops and their subtype topology.
* Mathlib supplies `Homeomorph.setCongr` for identifying equal subsets.
* `OnePoint.collapsePullbackHomeomorph` supplies the open-subspace comparison,
  using Mathlib's compact-open and quotient-descent APIs and Group Theory's
  compact-covering precomposition embedding.
-/

@[expose] public section

universe u v

open scoped unitInterval Topology OnePoint

namespace GenLoop

/-- Generalized loops on a finite cube are based maps from the one-point
compactification of its boundary complement. The forward map extends the
restriction by the basepoint at infinity; the inverse pulls back along the
collapse of the cube boundary. -/
noncomputable def onePointHomeomorph (N : Type u) [Finite N]
    {X : Type v} [TopologicalSpace X] (x : X) :
    GenLoop N X x ≃ₜ
      {F : C(OnePoint ((Cube.boundary N)ᶜ : Set (I^N)), X) // F ∞ = x} :=
  (Homeomorph.setCongr (show GenLoop N X x =
      {f : C(I^N, X) | ∀ k, k ∉ (Cube.boundary N)ᶜ → f k = x} by
    ext f
    simp only [GenLoop, Set.mem_ofPred_eq, Set.mem_compl_iff, not_not])).trans
    (OnePoint.collapsePullbackHomeomorph
      (⟨(Cube.boundary N)ᶜ, (Cube.isClosed_boundary N).isOpen_compl⟩ :
        TopologicalSpace.Opens (I^N)) x).symm

variable (N : Type u) [Finite N] {X : Type v} [TopologicalSpace X] (x : X)

/-- The forward map is the one-point recursor applied to the restriction of
the generalized loop to the boundary complement. -/
theorem coe_onePointHomeomorph_apply (p : GenLoop N X x) :
    ⇑(onePointHomeomorph N x p).val =
      OnePoint.rec x (fun k : ((Cube.boundary N)ᶜ : Set (I^N)) => p k.val) :=
  rfl

/-- The image of a generalized loop takes infinity to its basepoint. -/
@[simp]
theorem onePointHomeomorph_apply_infty (p : GenLoop N X x) :
    (onePointHomeomorph N x p).val ∞ = x :=
  rfl

/-- On the boundary complement, the image has the values of the generalized loop. -/
@[simp]
theorem onePointHomeomorph_apply_coe (p : GenLoop N X x)
    (k : ((Cube.boundary N)ᶜ : Set (I^N))) :
    (onePointHomeomorph N x p).val
      (k : OnePoint ((Cube.boundary N)ᶜ : Set (I^N))) = p k.val :=
  rfl

/-- The inverse map is precomposition with the collapse of the cube boundary. -/
@[simp]
theorem coe_onePointHomeomorph_symm_apply
    (F : {F : C(OnePoint ((Cube.boundary N)ᶜ : Set (I^N)), X) // F ∞ = x}) :
    ((onePointHomeomorph N x).symm F).val = F.val.comp
      (OnePoint.collapse
        (⟨(Cube.boundary N)ᶜ, (Cube.isClosed_boundary N).isOpen_compl⟩ :
          TopologicalSpace.Opens (I^N))) :=
  rfl

/-- Evaluate the inverse comparison at any cube point, including boundary points. -/
@[simp]
theorem onePointHomeomorph_symm_apply_apply
    (F : {F : C(OnePoint ((Cube.boundary N)ᶜ : Set (I^N)), X) // F ∞ = x})
    (k : I^N) :
    (onePointHomeomorph N x).symm F k = F.val
      (OnePoint.collapse
        (⟨(Cube.boundary N)ᶜ, (Cube.isClosed_boundary N).isOpen_compl⟩ :
          TopologicalSpace.Opens (I^N)) k) :=
  rfl

end GenLoop
