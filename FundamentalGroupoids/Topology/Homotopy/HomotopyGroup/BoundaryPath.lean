/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map

/-!
# Concatenation of homotopies with a common boundary path

`GenLoop.homotopyTransAt` concatenates two homotopies of generalized loops along
an explicitly chosen cube coordinate. Both input homotopies may move the
basepoint, provided that their restrictions to the cube boundary follow the
same path. The resulting homotopy follows that path as well.

The construction reuses Mathlib's `GenLoop.transAt` in the continuous-map space
`C(I, X)`, based at the boundary path. Currying and uncurrying exchange the time
and cube variables. Endpoint and time-slice identities follow from
`GenLoop.map_transAt` applied to evaluation. Only the time interval needs to be
locally compact; no finiteness assumption on the cube index or additional
assumption on the target space is needed.

Temporal concatenation and reversal use the existing homotopy operations;
their boundary traces are respectively path concatenation and path reversal.
-/

public section

noncomputable section

open scoped unitInterval

universe u v

namespace GenLoop

variable {N : Type u} {X : Type v} [TopologicalSpace X] {x y : X}

/-- Temporal concatenation concatenates the paths traced on the cube boundary. -/
theorem homotopy_trans_boundary {w : X}
    {p : GenLoop N X x} {q : GenLoop N X y} {r : GenLoop N X w}
    {γ : Path x y} {δ : Path y w}
    (H0 : ContinuousMap.Homotopy p.val q.val)
    (H1 : ContinuousMap.Homotopy q.val r.val)
    (h0 : ∀ t a, a ∈ Cube.boundary N → H0 (t, a) = γ t)
    (h1 : ∀ t a, a ∈ Cube.boundary N → H1 (t, a) = δ t)
    (t : I) (a : N → I) (ha : a ∈ Cube.boundary N) :
    (H0.trans H1) (t, a) = (γ.trans δ) t := by
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs
  · exact h0 _ a ha
  · exact h1 _ a ha

/-- Reversing a homotopy reverses the path traced on the cube boundary. -/
theorem homotopy_symm_boundary
    {p : GenLoop N X x} {q : GenLoop N X y} {γ : Path x y}
    (H : ContinuousMap.Homotopy p.val q.val)
    (h : ∀ t a, a ∈ Cube.boundary N → H (t, a) = γ t)
    (t : I) (a : N → I) (ha : a ∈ Cube.boundary N) :
    H.symm (t, a) = γ.symm t := by
  rw [ContinuousMap.Homotopy.symm_apply, Path.symm_apply]
  exact h _ a ha

private def timeCurry (γ : Path x y) {p : GenLoop N X x} {q : GenLoop N X y}
    (H : ContinuousMap.Homotopy p.val q.val)
    (h : ∀ t z, z ∈ Cube.boundary N → H (t, z) = γ t) :
    GenLoop N C(I, X) γ.toContinuousMap :=
  ⟨(H.toContinuousMap.comp ContinuousMap.prodSwap).curry, by
    intro z hz
    apply ContinuousMap.ext
    intro t
    exact h t z hz⟩

private theorem timeCurry_map_eval (γ : Path x y)
    {p : GenLoop N X x} {q : GenLoop N X y}
    (H : ContinuousMap.Homotopy p.val q.val)
    (h : ∀ t z, z ∈ Cube.boundary N → H (t, z) = γ t)
    (t : I) {a : X} (ha : γ t = a) (r : GenLoop N X a)
    (hr : ∀ z, H (t, z) = r z) :
    map (⟨fun f : C(I, X) ↦ f t, continuous_eval_const t⟩ : C(C(I, X), X))
      ha (timeCurry γ H h) = r := by
  apply GenLoop.ext
  intro z
  exact hr z

variable [DecidableEq N]

/-- Concatenate homotopies along a cube coordinate when their boundaries follow
one common path. The homotopy parameter is the first coordinate. -/
def homotopyTransAt (i : N) (γ : Path x y)
    {p0 p1 : GenLoop N X x} {q0 q1 : GenLoop N X y}
    (H0 : ContinuousMap.Homotopy p0.val q0.val)
    (H1 : ContinuousMap.Homotopy p1.val q1.val)
    (h0 : ∀ t z, z ∈ Cube.boundary N → H0 (t, z) = γ t)
    (h1 : ∀ t z, z ∈ Cube.boundary N → H1 (t, z) = γ t) :
    ContinuousMap.Homotopy (transAt i p0 p1).val (transAt i q0 q1).val where
  toContinuousMap :=
    (transAt i (timeCurry γ H0 h0) (timeCurry γ H1 h1)).val.uncurry.comp
      ContinuousMap.prodSwap
  map_zero_left z := by
    change ((transAt i (timeCurry γ H0 h0) (timeCurry γ H1 h1)).val z) 0 =
      (transAt i p0 p1).val z
    rw [congrFun (GenLoop.coe_coe
      (transAt i (timeCurry γ H0 h0) (timeCurry γ H1 h1))) z,
      congrFun (GenLoop.coe_coe (transAt i p0 p1)) z]
    have hp0 := timeCurry_map_eval γ H0 h0 0 γ.source p0
      (fun a => (H0.apply_zero a).trans (congrFun (GenLoop.coe_coe p0) a))
    have hp1 := timeCurry_map_eval γ H1 h1 0 γ.source p1
      (fun a => (H1.apply_zero a).trans (congrFun (GenLoop.coe_coe p1) a))
    have h := congrArg (fun r : GenLoop N X x ↦ r z)
      (map_transAt
        (⟨fun f : C(I, X) ↦ f 0, continuous_eval_const 0⟩ : C(C(I, X), X))
        γ.source i (timeCurry γ H0 h0) (timeCurry γ H1 h1))
    rw [map_apply, ContinuousMap.coe_mk] at h
    simpa only [hp0, hp1] using h
  map_one_left z := by
    change ((transAt i (timeCurry γ H0 h0) (timeCurry γ H1 h1)).val z) 1 =
      (transAt i q0 q1).val z
    rw [congrFun (GenLoop.coe_coe
      (transAt i (timeCurry γ H0 h0) (timeCurry γ H1 h1))) z,
      congrFun (GenLoop.coe_coe (transAt i q0 q1)) z]
    have hq0 := timeCurry_map_eval γ H0 h0 1 γ.target q0
      (fun a => (H0.apply_one a).trans (congrFun (GenLoop.coe_coe q0) a))
    have hq1 := timeCurry_map_eval γ H1 h1 1 γ.target q1
      (fun a => (H1.apply_one a).trans (congrFun (GenLoop.coe_coe q1) a))
    have h := congrArg (fun r : GenLoop N X y ↦ r z)
      (map_transAt
        (⟨fun f : C(I, X) ↦ f 1, continuous_eval_const 1⟩ : C(C(I, X), X))
        γ.target i (timeCurry γ H0 h0) (timeCurry γ H1 h1))
    rw [map_apply, ContinuousMap.coe_mk] at h
    simpa only [hq0, hq1] using h

/-- Each time slice of the concatenated homotopy is the concatenation of the
input time slices, based at the corresponding point of the boundary path. -/
theorem homotopyTransAt_apply (i : N) (γ : Path x y)
    {p0 p1 : GenLoop N X x} {q0 q1 : GenLoop N X y}
    (H0 : ContinuousMap.Homotopy p0.val q0.val)
    (H1 : ContinuousMap.Homotopy p1.val q1.val)
    (h0 : ∀ t z, z ∈ Cube.boundary N → H0 (t, z) = γ t)
    (h1 : ∀ t z, z ∈ Cube.boundary N → H1 (t, z) = γ t)
    (t : I) (z : N → I) :
    homotopyTransAt i γ H0 H1 h0 h1 (t, z) =
      transAt i (⟨H0.curry t, h0 t⟩ : GenLoop N X (γ t))
        (⟨H1.curry t, h1 t⟩ : GenLoop N X (γ t)) z := by
  unfold homotopyTransAt
  change ((transAt i (timeCurry γ H0 h0) (timeCurry γ H1 h1)).val z) t = _
  rw [congrFun (GenLoop.coe_coe
    (transAt i (timeCurry γ H0 h0) (timeCurry γ H1 h1))) z]
  have hp0 := timeCurry_map_eval γ H0 h0 t rfl
    (⟨H0.curry t, h0 t⟩ : GenLoop N X (γ t)) (fun _ ↦ rfl)
  have hp1 := timeCurry_map_eval γ H1 h1 t rfl
    (⟨H1.curry t, h1 t⟩ : GenLoop N X (γ t)) (fun _ ↦ rfl)
  have h := congrArg (fun r : GenLoop N X (γ t) ↦ r z)
    (map_transAt
      (⟨fun f : C(I, X) ↦ f t, continuous_eval_const t⟩ : C(C(I, X), X))
      rfl i (timeCurry γ H0 h0) (timeCurry γ H1 h1))
  change ((transAt i (timeCurry γ H0 h0) (timeCurry γ H1 h1)) z) t = _ at h
  simpa only [hp0, hp1] using h

/-- Concatenation preserves the prescribed path on the whole cube boundary. -/
@[simp]
theorem homotopyTransAt_boundary (i : N) (γ : Path x y)
    {p0 p1 : GenLoop N X x} {q0 q1 : GenLoop N X y}
    (H0 : ContinuousMap.Homotopy p0.val q0.val)
    (H1 : ContinuousMap.Homotopy p1.val q1.val)
    (h0 : ∀ t z, z ∈ Cube.boundary N → H0 (t, z) = γ t)
    (h1 : ∀ t z, z ∈ Cube.boundary N → H1 (t, z) = γ t)
    (t : I) (z : N → I) (hz : z ∈ Cube.boundary N) :
    homotopyTransAt i γ H0 H1 h0 h1 (t, z) = γ t := by
  rw [homotopyTransAt_apply]
  exact GenLoop.boundary _ z hz

end GenLoop
