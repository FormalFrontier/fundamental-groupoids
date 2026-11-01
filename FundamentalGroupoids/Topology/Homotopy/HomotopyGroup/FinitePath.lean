/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Cube.Extension

/-!
# Moving the basepoint of finite-dimensional generalized loops

`GenLoop.pathMapOfFinite` moves a generalized loop along a path between its
basepoints. It is a continuous map jointly in the path and the generalized
loop, for their existing compact-open topologies. The construction applies to
an arbitrary finite coordinate type, including the empty type.

`GenLoop.homotopyAlongOfFinite` is a homotopy from the original cube map to
the transported cube map. Its trace on every coordinate face is the given
path, and the homotopies depend jointly continuously on the path and loop.

The construction uses `Cube.homotopyExtension`, with evaluation of the loop
as its bottom data and evaluation of the path as its side data. Mathlib's
`GenLoop`, `Path`, continuous evaluation and compact-open currying supply the
mapping-space constructions. No topology on a mapping space is changed, and
no separation or local compactness assumption on the target is needed.
-/

public section

noncomputable section

universe u v

open scoped unitInterval

namespace GenLoop

variable {N : Type u} {X : Type v} [TopologicalSpace X] {x y : X}

private def pathInitial : C((Path x y × GenLoop N X x) × (N → I), X) where
  toFun q := q.1.2 q.2
  continuous_toFun := (continuous_snd.comp continuous_fst).eval continuous_snd

private def pathSide :
    C((Path x y × GenLoop N X x) × (I × Cube.boundary N), X) where
  toFun q := q.1.1 q.2.1
  continuous_toFun :=
    (continuous_fst.comp continuous_fst).eval (continuous_fst.comp continuous_snd)

private theorem pathSide_zero (q : Path x y × GenLoop N X x)
    (a : Cube.boundary N) :
    pathSide (q, (0, a)) = pathInitial (q, a.val) :=
  q.1.source.trans (GenLoop.boundary q.2 a.val a.property).symm

variable [Finite N]

private def pathExtension :
    C((Path x y × GenLoop N X x) × (I × (N → I)), X) :=
  Cube.homotopyExtension pathInitial pathSide pathSide_zero

private theorem pathExtension_apply_zero (q : Path x y × GenLoop N X x)
    (z : N → I) : pathExtension (q, (0, z)) = q.2 z :=
  Cube.homotopyExtension_apply_zero pathInitial pathSide pathSide_zero q z

private theorem pathExtension_boundary (q : Path x y × GenLoop N X x)
    (t : I) (a : Cube.boundary N) : pathExtension (q, (t, a.val)) = q.1 t :=
  Cube.homotopyExtension_boundary pathInitial pathSide pathSide_zero q t a

/-- Move the basepoint of a finite-dimensional generalized loop along a path.
This map is jointly continuous in the path and the generalized loop. -/
def pathMapOfFinite : C(Path x y × GenLoop N X x, GenLoop N X y) := by
  let top : C((Path x y × GenLoop N X x) × (N → I), X) :=
    pathExtension.comp
      { toFun := fun q => (q.1, (1, q.2))
        continuous_toFun := continuous_fst.prodMk (continuous_const.prodMk continuous_snd) }
  let endpoint : C(Path x y × GenLoop N X x, C((N → I), X)) := top.curry
  have h : ∀ q, endpoint q ∈ GenLoop N X y := by
    intro q z hz
    exact (pathExtension_boundary q 1 ⟨z, hz⟩).trans q.1.target
  exact ⟨(GenLoop N X y).codRestrict endpoint h, endpoint.continuous.codRestrict h⟩

/-- The cube homotopy moving the basepoint along `γ`. On the boundary its
value at time `t` is `γ t`, rather than a fixed basepoint. -/
def homotopyAlongOfFinite (γ : Path x y) (p : GenLoop N X x) :
    ContinuousMap.Homotopy p.val (pathMapOfFinite (γ, p)).val where
  toFun q := pathExtension ((γ, p), q)
  continuous_toFun :=
    (pathExtension (N := N) (x := x) (y := y)).continuous.comp
      (continuous_const.prodMk continuous_id)
  map_zero_left z := pathExtension_apply_zero (γ, p) z
  map_one_left _ := rfl

/-- Evaluation of basepoint transport is the final value of its moving-boundary
homotopy. -/
theorem pathMapOfFinite_apply (γ : Path x y) (p : GenLoop N X x) (z : N → I) :
    pathMapOfFinite (γ, p) z = homotopyAlongOfFinite γ p (1, z) := by
  rfl

/-- The moving-boundary homotopy starts at the original generalized loop. -/
theorem homotopyAlongOfFinite_apply_zero (γ : Path x y) (p : GenLoop N X x)
    (z : N → I) : homotopyAlongOfFinite γ p (0, z) = p z :=
  (homotopyAlongOfFinite γ p).map_zero_left z

/-- The moving-boundary homotopy ends at the transported generalized loop. -/
theorem homotopyAlongOfFinite_apply_one (γ : Path x y) (p : GenLoop N X x)
    (z : N → I) : homotopyAlongOfFinite γ p (1, z) = pathMapOfFinite (γ, p) z :=
  (homotopyAlongOfFinite γ p).map_one_left z

/-- Every boundary point follows precisely the path used to move the basepoint. -/
@[simp]
theorem homotopyAlongOfFinite_boundary (γ : Path x y) (p : GenLoop N X x)
    (t : I) (z : N → I) (hz : z ∈ Cube.boundary N) :
    homotopyAlongOfFinite γ p (t, z) = γ t :=
  pathExtension_boundary (γ, p) t ⟨z, hz⟩

/-- The transported cube map sends the boundary to the new basepoint. -/
@[simp]
theorem pathMapOfFinite_boundary (γ : Path x y) (p : GenLoop N X x)
    (z : N → I) (hz : z ∈ Cube.boundary N) : pathMapOfFinite (γ, p) z = y :=
  GenLoop.boundary (pathMapOfFinite (γ, p)) z hz

/-- The moving-boundary homotopies are jointly continuous in the path,
generalized loop, time and cube point. -/
@[fun_prop]
theorem continuous_homotopyAlongOfFinite :
    Continuous fun q : (Path x y × GenLoop N X x) × (I × (N → I)) =>
      homotopyAlongOfFinite q.1.1 q.1.2 q.2 :=
  (pathExtension (N := N) (x := x) (y := y)).continuous

end GenLoop
