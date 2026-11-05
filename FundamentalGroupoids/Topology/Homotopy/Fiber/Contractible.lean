/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber
public import FundamentalGroupoids.Topology.Homotopy.Fiber.HomotopyEquiv
public import FundamentalGroupoids.Topology.Homotopy.RelativePathSpace.Contractible
public import FundamentalGroupoids.Topology.Homotopy.Relative

/-!
# Contractibility of homotopy fibers

The ordinary homotopy fiber of the identity contracts to its specified
constant-path point. The contraction is transported from
`ContinuousMap.RelativePathSpace.contraction` through
`ContinuousMap.HomotopyFiber.endpointHomeomorph`, using the identity map's full
range. The source point moves along the shortened path: at contraction time `t`,
it is the original path evaluated at `1 - t`.

The fiber of a homotopy equivalence is also contractible. Its contraction is
obtained from the identity fiber through the induced fiber homotopy equivalence
and its named inverse homotopies.

## Implementation notes

Only ordinary compact-open and subspace topologies are used. The existing
relative-homotopy precomposition, postcomposition and endpoint-cast operations
transport the contraction without another path or continuity construction.
The target topology is arbitrary. This does not contract a fixed-endpoint path
space, a loop space or the ambient target.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 7, §3, p. 50:
  time-shortening deformation of the mapping-path space.
* `ContinuousMap.RelativePathSpace.contraction`, for the fixed-start,
  free-endpoint time-shortening deformation and its attribution.
* Mathlib's `Mathlib.Topology.Homotopy.Basic` and
  `Mathlib.Topology.Homotopy.Contractible`, for homotopy composition and the
  characterization of contractibility by nullhomotopy of the identity.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

universe u v

variable {B : Type u} [TopologicalSpace B]

/-- Contract the ordinary homotopy fiber of the identity to its constant-path
point, fixing that point throughout. The entire path is shortened and its
terminal source point moves with it. This transports May's time-shortening
deformation (*A Concise Course in Algebraic Topology*, Chapter 7, §3, p. 50)
through the endpoint-path comparison. -/
noncomputable def idContraction (b : B) :
    (ContinuousMap.id (HomotopyFiber (ContinuousMap.id B) b)).HomotopyRel
      (ContinuousMap.const _ (const (f := ContinuousMap.id B) b rfl))
      {const (f := ContinuousMap.id B) b rfl} := by
  have hRange : Set.range (ContinuousMap.id B) = Set.univ := by
    simpa only [ContinuousMap.coe_id] using (Set.range_id (α := B))
  let e : HomotopyFiber (ContinuousMap.id B) b ≃ₜ RelativePathSpace b Set.univ :=
    (endpointHomeomorph
      (Topology.IsEmbedding.id : Topology.IsEmbedding (ContinuousMap.id B)) b).trans
      ((Homeomorph.refl C(I, B)).subtype (fun γ => by
        rw [hRange]
        exact Iff.rfl))
  have hconst : e (const (f := ContinuousMap.id B) b rfl) =
      RelativePathSpace.const (Set.mem_univ b) := by
    apply RelativePathSpace.ext
    exact (endpointHomeomorph_path
      (f := ContinuousMap.id B) (b := b)
      (Topology.IsEmbedding.id : Topology.IsEmbedding (ContinuousMap.id B))
      (const (f := ContinuousMap.id B) b rfl)).trans
        (path_const (f := ContinuousMap.id B) (b := b) b rfl)
  have hfixed : Set.MapsTo
      (e : C(HomotopyFiber (ContinuousMap.id B) b, RelativePathSpace b Set.univ))
      {const (f := ContinuousMap.id B) b rfl}
      {RelativePathSpace.const (Set.mem_univ b)} := by
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Set.mem_singleton_iff.mpr hconst
  let H := ((RelativePathSpace.contraction b).precomp
    (e : C(HomotopyFiber (ContinuousMap.id B) b, RelativePathSpace b Set.univ))
    hfixed).compContinuousMap
      (e.symm : C(RelativePathSpace b Set.univ, HomotopyFiber (ContinuousMap.id B) b))
  exact H.cast
    (by
      apply ContinuousMap.ext
      intro z
      exact e.symm_apply_apply z)
    (by
      apply ContinuousMap.ext
      intro z
      exact (e.symm_apply_eq).2 hconst.symm)

/-- The complete underlying path is the original path on its shortened interval. -/
theorem path_idContraction (b : B) (t : I)
    (z : HomotopyFiber (ContinuousMap.id B) b) :
    (path (idContraction b (t, z)) : I → B) =
      fun s => path z (unitInterval.symm t * s) := by
  let γ : RelativePathSpace b Set.univ :=
    RelativePathSpace.mk (path z) (path_zero z) (Set.mem_univ _)
  calc
    (path (idContraction b (t, z)) : I → B) =
        (RelativePathSpace.path (RelativePathSpace.contraction b (t, γ)) : I → B) := by
      -- Both endpoint comparisons and the change of endpoint set retain the path.
      rfl
    _ = fun s => path z (unitInterval.symm t * s) := by
      funext s
      exact RelativePathSpace.eval_contraction b t γ s

/-- Every coordinate of the shortened path retains the original parametrization. -/
@[simp]
theorem path_idContraction_apply (b : B) (t : I)
    (z : HomotopyFiber (ContinuousMap.id B) b) (s : I) :
    path (idContraction b (t, z)) s = path z (unitInterval.symm t * s) := by
  exact congrFun (path_idContraction b t z) s

/-- Evaluation of the contraction at any path time is shortened evaluation. -/
theorem eval_idContraction (b : B) (t : I)
    (z : HomotopyFiber (ContinuousMap.id B) b) (s : I) :
    eval s (idContraction b (t, z)) = eval (unitInterval.symm t * s) z := by
  simpa only [eval_apply] using path_idContraction_apply b t z s

/-- The source point follows the original path backwards as it is shortened. -/
@[simp]
theorem point_idContraction (b : B) (t : I)
    (z : HomotopyFiber (ContinuousMap.id B) b) :
    point (idContraction b (t, z)) = eval (unitInterval.symm t) z := by
  simpa only [eval_one, ContinuousMap.id_apply, mul_one] using
    eval_idContraction b t z 1

/-- At initial contraction time, the whole fiber point is unchanged. -/
theorem idContraction_zero (b : B) (z : HomotopyFiber (ContinuousMap.id B) b) :
    idContraction b (0, z) = z := by
  exact (idContraction b).apply_zero z

/-- At final contraction time, the whole fiber point is the specified constant point. -/
theorem idContraction_one (b : B) (z : HomotopyFiber (ContinuousMap.id B) b) :
    idContraction b (1, z) = const (f := ContinuousMap.id B) b rfl := by
  exact (idContraction b).apply_one z

/-- The distinguished constant-path point is fixed at every contraction time. -/
@[simp]
theorem idContraction_const (b : B) (t : I) :
    idContraction b (t, const (f := ContinuousMap.id B) b rfl) =
      const (f := ContinuousMap.id B) b rfl := by
  exact (idContraction b).eq_fst t (Set.mem_singleton _)

/-- Postcomposition by a fixed continuous map commutes with the chosen contraction
of identity homotopy fibers at every time. -/
theorem idContraction_naturality {B' : Type v} [TopologicalSpace B'] (G : C(B, B'))
    (b : B) (b' : B') (hb : G b = b') (s : I)
    (z : HomotopyFiber (ContinuousMap.id B) b) :
    map (f := ContinuousMap.id B) (f' := ContinuousMap.id B')
        G G (fun _ => rfl) hb (idContraction b (s, z)) =
      idContraction b' (s,
        map (f := ContinuousMap.id B) (f' := ContinuousMap.id B')
          G G (fun _ => rfl) hb z) := by
  apply ext
  · simp only [point_map (f := ContinuousMap.id B) (f' := ContinuousMap.id B')
      (b := b) (b' := b') G G (fun _ => rfl) hb, point_idContraction,
      eval_map (f := ContinuousMap.id B) (f' := ContinuousMap.id B')
        (b := b) (b' := b') G G (fun _ => rfl) hb]
  · apply ContinuousMap.ext
    intro t
    simp only [path_map (f := ContinuousMap.id B) (f' := ContinuousMap.id B')
      (b := b) (b' := b') G G (fun _ => rfl) hb,
      ContinuousMap.comp_apply, path_idContraction_apply]

/-- The ordinary homotopy fiber of the identity is contractible, with no restriction
on the target topology, via `idContraction` and May's time-shortening deformation
(*A Concise Course in Algebraic Topology*, Chapter 7, §3, p. 50). -/
instance instContractibleSpaceId (b : B) :
    ContractibleSpace (HomotopyFiber (ContinuousMap.id B) b) := by
  exact (contractible_iff_id_nullhomotopic (HomotopyFiber (ContinuousMap.id B) b)).2
    ⟨const (f := ContinuousMap.id B) b rfl, ⟨(idContraction b).toHomotopy⟩⟩

variable {E : Type v} [TopologicalSpace E]

/-- The ordinary homotopy fiber of a homotopy equivalence is contractible.
May's time-shortening deformation (*A Concise Course in Algebraic Topology*,
Chapter 7, §3, p. 50) is transported through `precompHomotopyEquiv`, using its
named left inverse homotopy. -/
theorem contractibleSpace_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv E B) (b : B) :
    ContractibleSpace (HomotopyFiber e.toFun b) := by
  let P := precompHomotopyEquiv (ContinuousMap.id B) e b
  let F := P.toFun
  let T := P.symm.toFun
  let c := const (f := ContinuousMap.id B) b rfl
  let U := precompLeftHomotopy (ContinuousMap.id B) e b
  let H : (T.comp F).Homotopy
      (ContinuousMap.const (HomotopyFiber e.toFun b) (T c)) :=
    (ContinuousMap.Homotopy.refl T).comp
      ((idContraction b).toHomotopy.compContinuousMap F)
  exact (contractible_iff_id_nullhomotopic (HomotopyFiber e.toFun b)).2
    ⟨T c, ⟨U.symm.trans H⟩⟩

end ContinuousMap.HomotopyFiber
