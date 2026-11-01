/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Cube.Cylinder
public import FundamentalGroupoids.Topology.Homotopy.Cube.Extension
public import FundamentalGroupoids.Topology.Homotopy.InfiniteCube
public import Mathlib.Topology.Homotopy.Path

/-!
# Changing the path traced by a homotopy on a cube boundary

A homotopy between generalized loops may move the boundary along a path between
their basepoints. A homotopy of that path, fixing its endpoints, can be extended
to change the boundary trace while retaining both endpoint loops.

For finite coordinate types, view the original homotopy cylinder as the cube
on `Option N`. Paste the two endpoint loops and the prescribed path homotopy
on its boundary, then apply `Cube.homotopyExtension` with a further, outer
homotopy parameter. Only the bottom and sides of this higher cylinder are
retracted; no retraction onto the full boundary of the original cylinder is
used. For infinite coordinate types, `GenLoop.homotopyAlongOfInfinite` supplies
the replacement directly. The empty coordinate type is included in the finite
construction. No separation assumptions on the target are needed.

## References

* Mathlib's `Path.Homotopy` supplies homotopies relative to the path endpoints.
* `Cube.homotopyExtension` supplies homotopy extension for finite cubes.
* `GenLoop.homotopyAlongOfInfinite` supplies the infinite-coordinate case.
-/

public section

noncomputable section

universe u v

open scoped unitInterval

namespace GenLoop

variable {N : Type u} {X : Type v} [TopologicalSpace X] {x y : X}
  {γ δ : Path x y} {p : GenLoop N X x} {q : GenLoop N X y}

private def boundaryValue (p : GenLoop N X x) (q : GenLoop N X y)
    (K : Path.Homotopy γ δ) (r : I × Cube.boundary (Option N)) : X := by
  classical
  exact if r.2.val none = 0 then p (fun i => r.2.val (some i))
    else if r.2.val none = 1 then q (fun i => r.2.val (some i))
    else K (r.1, r.2.val none)

private theorem boundaryValue_of_zero (K : Path.Homotopy γ δ)
    (r : I × Cube.boundary (Option N)) (ht : r.2.val none = 0) :
    boundaryValue p q K r = p (fun i => r.2.val (some i)) := by
  classical
  simp only [boundaryValue, ite_eq_left ht]

private theorem boundaryValue_of_one (K : Path.Homotopy γ δ)
    (r : I × Cube.boundary (Option N)) (ht : r.2.val none = 1) :
    boundaryValue p q K r = q (fun i => r.2.val (some i)) := by
  classical
  have ht₀ : r.2.val none ≠ 0 := by
    rw [ht]
    exact one_ne_zero
  simp only [boundaryValue, ite_eq_right ht₀, ite_eq_left ht]

private theorem boundaryValue_of_boundary (K : Path.Homotopy γ δ)
    (r : I × Cube.boundary (Option N))
    (hz : (fun i => r.2.val (some i)) ∈ Cube.boundary N) :
    boundaryValue p q K r = K (r.1, r.2.val none) := by
  classical
  by_cases ht₀ : r.2.val none = 0
  · rw [boundaryValue_of_zero K r ht₀, ht₀, K.source]
    change p.val (fun i => r.2.val (some i)) = x
    exact (congrFun (GenLoop.coe_coe p) _).trans (GenLoop.boundary p _ hz)
  by_cases ht₁ : r.2.val none = 1
  · rw [boundaryValue_of_one K r ht₁, ht₁, K.target]
    change q.val (fun i => r.2.val (some i)) = y
    exact (congrFun (GenLoop.coe_coe q) _).trans (GenLoop.boundary q _ hz)
  simp only [boundaryValue, ite_eq_right ht₀, ite_eq_right ht₁]

private def boundaryHomotopy [Finite N]
    (p : GenLoop N X x) (q : GenLoop N X y) (K : Path.Homotopy γ δ) :
    C(I × Cube.boundary (Option N), X) where
  toFun := boundaryValue p q K
  continuous_toFun := by
    let A : Set (I × Cube.boundary (Option N)) := {r | r.2.val none = 0}
    let B : Set (I × Cube.boundary (Option N)) := {r | r.2.val none = 1}
    let C : Set (I × Cube.boundary (Option N)) :=
      {r | (fun i => r.2.val (some i)) ∈ Cube.boundary N}
    have ht : Continuous (fun r : I × Cube.boundary (Option N) => r.2.val none) :=
      (continuous_apply none).comp (continuous_subtype_val.comp continuous_snd)
    have hz : Continuous (fun r : I × Cube.boundary (Option N) =>
        fun i => r.2.val (some i)) :=
      continuous_pi fun i =>
        (continuous_apply (some i)).comp (continuous_subtype_val.comp continuous_snd)
    have hA : IsClosed A := isClosed_eq ht continuous_const
    have hB : IsClosed B := isClosed_eq ht continuous_const
    have hC : IsClosed C := by
      change IsClosed {r : I × Cube.boundary (Option N) |
        (fun i => r.2.val (some i)) ∈ Cube.boundary N}
      simp_rw [← Cube.radius_eq_one_iff]
      exact isClosed_eq ((Cube.radius N).continuous.comp hz) continuous_const
    have hp : ContinuousOn (boundaryValue p q K) A := by
      apply (p.val.continuous.comp hz).continuousOn.congr
      intro r hr
      exact (boundaryValue_of_zero K r hr).trans
        (congrFun (GenLoop.coe_coe p) _).symm
    have hq : ContinuousOn (boundaryValue p q K) B := by
      apply (q.val.continuous.comp hz).continuousOn.congr
      intro r hr
      exact (boundaryValue_of_one K r hr).trans
        (congrFun (GenLoop.coe_coe q) _).symm
    have hK : ContinuousOn (boundaryValue p q K) C := by
      apply (K.continuous.comp (continuous_fst.prodMk ht)).continuousOn.congr
      intro r hr
      exact boundaryValue_of_boundary K r hr
    apply continuousOn_univ.mp
    apply ((hp.union_of_isClosed hq hA hB).union_of_isClosed hK (hA.union hB) hC).mono
    intro r _
    rcases (Cube.option_mem_boundary_iff r.2.val).mp r.2.property with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

private def cylinderInitial (H : ContinuousMap.Homotopy p.val q.val) :
    C(Unit × (Option N → I), X) where
  toFun := fun r => H (Cube.optionHomeomorph N r.2)
  continuous_toFun :=
    H.continuous.comp ((Cube.optionHomeomorph N).continuous.comp continuous_snd)

private def cylinderBoundary [Finite N]
    (p : GenLoop N X x) (q : GenLoop N X y) (K : Path.Homotopy γ δ) :
    C(Unit × (I × Cube.boundary (Option N)), X) where
  toFun := fun r => boundaryHomotopy p q K r.2
  continuous_toFun := (boundaryHomotopy p q K).continuous.comp continuous_snd

private theorem cylinderBoundary_zero [Finite N]
    (H : ContinuousMap.Homotopy p.val q.val)
    (htrace : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t)
    (K : Path.Homotopy γ δ) (s : Unit) (a : Cube.boundary (Option N)) :
    cylinderBoundary p q K (s, (0, a)) = cylinderInitial H (s, a.val) := by
  change boundaryValue p q K (0, a) = H (a.val none, fun i => a.val (some i))
  rcases (Cube.option_mem_boundary_iff a.val).mp a.property with ht | ht | hz
  · rw [boundaryValue_of_zero K (0, a) ht, ht, H.apply_zero]
    exact (congrFun (GenLoop.coe_coe p) _).symm
  · rw [boundaryValue_of_one K (0, a) ht, ht, H.apply_one]
    exact (congrFun (GenLoop.coe_coe q) _).symm
  · rw [boundaryValue_of_boundary K (0, a) hz]
    exact (K.toHomotopy.apply_zero (a.val none)).trans (htrace _ _ hz).symm

private def boundaryPathExtension [Finite N]
    (H : ContinuousMap.Homotopy p.val q.val)
    (htrace : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t)
    (K : Path.Homotopy γ δ) : C(Unit × (I × (Option N → I)), X) :=
  Cube.homotopyExtension (N := Option N) (P := Unit)
    (cylinderInitial H) (cylinderBoundary p q K) (cylinderBoundary_zero H htrace K)

private theorem boundaryPathExtension_boundary [Finite N]
    (H : ContinuousMap.Homotopy p.val q.val)
    (htrace : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t)
    (K : Path.Homotopy γ δ) (s : I) (a : Cube.boundary (Option N)) :
    boundaryPathExtension H htrace K ((), (s, a.val)) = boundaryValue p q K (s, a) := by
  exact Cube.homotopyExtension_boundary
    (cylinderInitial H) (cylinderBoundary p q K) (cylinderBoundary_zero H htrace K) () s a

private def homotopyChangeBoundaryPathOfFinite [Finite N]
    (H : ContinuousMap.Homotopy p.val q.val)
    (htrace : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t)
    (K : Path.Homotopy γ δ) : ContinuousMap.Homotopy p.val q.val where
  toFun := fun r => boundaryPathExtension H htrace K
    ((), (1, (Cube.optionHomeomorph N).symm r))
  continuous_toFun := (boundaryPathExtension H htrace K).continuous.comp
    (continuous_const.prodMk
      (continuous_const.prodMk (Cube.optionHomeomorph N).symm.continuous))
  map_zero_left := by
    intro z
    let a : Cube.boundary (Option N) :=
      ⟨(Cube.optionHomeomorph N).symm (0, z),
        (Cube.optionHomeomorph_symm_mem_boundary_iff N (0, z)).mpr (Or.inl rfl)⟩
    change boundaryPathExtension H htrace K ((), (1, a.val)) = p.val z
    rw [boundaryPathExtension_boundary H htrace K 1 a]
    rw [boundaryValue_of_zero K (1, a) (show a.val none = 0 from rfl)]
    change p z = p.val z
    exact (congrFun (GenLoop.coe_coe p) z).symm
  map_one_left := by
    intro z
    let a : Cube.boundary (Option N) :=
      ⟨(Cube.optionHomeomorph N).symm (1, z),
        (Cube.optionHomeomorph_symm_mem_boundary_iff N (1, z)).mpr (Or.inr (Or.inl rfl))⟩
    change boundaryPathExtension H htrace K ((), (1, a.val)) = q.val z
    rw [boundaryPathExtension_boundary H htrace K 1 a]
    rw [boundaryValue_of_one K (1, a) (show a.val none = 1 from rfl)]
    change q z = q.val z
    exact (congrFun (GenLoop.coe_coe q) z).symm

private theorem homotopyChangeBoundaryPathOfFinite_boundary [Finite N]
    (H : ContinuousMap.Homotopy p.val q.val)
    (htrace : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t)
    (K : Path.Homotopy γ δ) (t : I) (z : N → I) (hz : z ∈ Cube.boundary N) :
    homotopyChangeBoundaryPathOfFinite H htrace K (t, z) = δ t := by
  let a : Cube.boundary (Option N) :=
    ⟨(Cube.optionHomeomorph N).symm (t, z),
      (Cube.optionHomeomorph_symm_mem_boundary_iff N (t, z)).mpr (Or.inr (Or.inr hz))⟩
  change boundaryPathExtension H htrace K ((), (1, a.val)) = δ t
  rw [boundaryPathExtension_boundary H htrace K 1 a]
  rw [boundaryValue_of_boundary K (1, a)
    (show (fun i => a.val (some i)) ∈ Cube.boundary N from hz)]
  exact K.toHomotopy.apply_one t

/-- Replace the path traced on the boundary of a generalized-loop homotopy by
an endpoint-fixed homotopic path, leaving its initial and final loops unchanged.
The homotopy parameter is the first coordinate. -/
def homotopyChangeBoundaryPath
    (H : ContinuousMap.Homotopy p.val q.val)
    (htrace : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t)
    (K : Path.Homotopy γ δ) : ContinuousMap.Homotopy p.val q.val := by
  classical
  exact if h : Finite N then
    letI : Finite N := h
    homotopyChangeBoundaryPathOfFinite H htrace K
  else
    letI : Infinite N := not_finite_iff_infinite.mp h
    homotopyAlongOfInfinite δ p q

/-- The replacement homotopy traces the final path of the given path homotopy
on every coordinate face, at every time. -/
theorem homotopyChangeBoundaryPath_boundary
    (H : ContinuousMap.Homotopy p.val q.val)
    (htrace : ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t)
    (K : Path.Homotopy γ δ) (t : I) (z : N → I) (hz : z ∈ Cube.boundary N) :
    homotopyChangeBoundaryPath H htrace K (t, z) = δ t := by
  classical
  by_cases h : Finite N
  · let : Finite N := h
    simpa only [homotopyChangeBoundaryPath, dite_eq_left h] using
      homotopyChangeBoundaryPathOfFinite_boundary H htrace K t z hz
  · let : Infinite N := not_finite_iff_infinite.mp h
    simpa only [homotopyChangeBoundaryPath, dite_eq_right h] using
      homotopyAlongOfInfinite_boundary δ p q t hz

/-- Existence of a homotopy between generalized loops with a prescribed
boundary trace depends only on the endpoint-fixed homotopy class of that path.
This includes empty and infinite coordinate types and arbitrary target spaces. -/
theorem exists_homotopy_boundary_iff_of_homotopic (h : γ.Homotopic δ) :
    (∃ H : ContinuousMap.Homotopy p.val q.val,
      ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t) ↔
    (∃ H : ContinuousMap.Homotopy p.val q.val,
      ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = δ t) := by
  obtain ⟨K⟩ := h
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨homotopyChangeBoundaryPath H hH K,
      homotopyChangeBoundaryPath_boundary H hH K⟩
  · rintro ⟨H, hH⟩
    exact ⟨homotopyChangeBoundaryPath H hH K.symm,
      homotopyChangeBoundaryPath_boundary H hH K.symm⟩

end GenLoop
