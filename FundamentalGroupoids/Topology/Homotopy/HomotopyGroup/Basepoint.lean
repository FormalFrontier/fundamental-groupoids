/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.FinitePath
public import FundamentalGroupoids.Topology.Homotopy.InfiniteCube

/-!
# Basepoint maps along paths

`GenLoop.pathMap` is a continuous map between generalized-loop spaces with
basepoints joined by a path. For finitely many coordinates it is the finite
cube construction; for infinitely many coordinates it is the constant map to
the constant loop at the new basepoint. These are the existing generalized-loop
spaces with their compact-open subtype topologies.

`GenLoop.homotopyAlong` joins each original cube map to its image, with boundary
trace equal to the prescribed path. It uses finite cube homotopy extension in
the finite case and the moving-boundary homotopy for infinite cubes otherwise.
The coordinate type may be empty, and the target requires only a topology.

`HomotopyGroup.pathMap` is the function on the existing homotopy groups induced
by the continuous generalized-loop map, using their identification with path
components. Its representative action is `HomotopyGroup.pathMap_class`.
-/

public section

noncomputable section

universe u v

open scoped unitInterval

namespace GenLoop

variable {N : Type u} {X : Type v} [TopologicalSpace X] {x y : X}

/-- Move the basepoint along `γ`. For finite coordinate types use finite cube
transport, and for infinite coordinate types send every loop to the constant
loop at the new basepoint. -/
def pathMap (γ : Path x y) : C(GenLoop N X x, GenLoop N X y) := by
  classical
  exact if h : Finite N then
    letI : Finite N := h
    (pathMapOfFinite (N := N) (x := x) (y := y)).curry γ
  else
    ContinuousMap.const (GenLoop N X x) (GenLoop.const : GenLoop N X y)

/-- On a finite coordinate type, basepoint transport is the jointly continuous
finite cube construction with the path fixed. -/
@[simp]
theorem pathMap_apply_of_finite [Finite N] (γ : Path x y) (p : GenLoop N X x) :
    pathMap γ p = pathMapOfFinite (γ, p) := by
  classical
  simp only [pathMap, dite_eq_left (inferInstance : Finite N), ContinuousMap.curry_apply]

/-- On an infinite coordinate type, basepoint transport is the constant loop
at the new basepoint. -/
@[simp]
theorem pathMap_apply_of_infinite [Infinite N] (γ : Path x y) (p : GenLoop N X x) :
    pathMap γ p = (GenLoop.const : GenLoop N X y) := by
  classical
  simp only [pathMap,
    dite_eq_right (not_finite_iff_infinite.mpr (inferInstance : Infinite N)),
    ContinuousMap.const_apply]

/-- A homotopy from the original cube map to its transported cube map, whose
boundary follows the prescribed path. -/
def homotopyAlong (γ : Path x y) (p : GenLoop N X x) :
    ContinuousMap.Homotopy p.val (pathMap γ p).val := by
  classical
  exact if h : Finite N then
    letI : Finite N := h
    (homotopyAlongOfFinite γ p).cast rfl
      (congrArg Subtype.val (pathMap_apply_of_finite γ p).symm)
  else
    letI : Infinite N := not_finite_iff_infinite.mp h
    (homotopyAlongOfInfinite γ p (GenLoop.const : GenLoop N X y)).cast rfl
      (congrArg Subtype.val (pathMap_apply_of_infinite γ p).symm)

/-- On finite cubes, the homotopy is the finite moving-boundary construction. -/
theorem homotopyAlong_apply_of_finite [Finite N] (γ : Path x y)
    (p : GenLoop N X x) (r : I × (N → I)) :
    homotopyAlong γ p r = homotopyAlongOfFinite γ p r := by
  classical
  simp only [homotopyAlong, dite_eq_left (inferInstance : Finite N),
    ContinuousMap.Homotopy.cast_apply]

/-- On infinite cubes, the homotopy is the moving-boundary construction ending
at the constant loop. -/
theorem homotopyAlong_apply_of_infinite [Infinite N] (γ : Path x y)
    (p : GenLoop N X x) (r : I × (N → I)) :
    homotopyAlong γ p r = homotopyAlongOfInfinite γ p GenLoop.const r := by
  classical
  simp only [homotopyAlong,
    dite_eq_right (not_finite_iff_infinite.mpr (inferInstance : Infinite N)),
    ContinuousMap.Homotopy.cast_apply]

/-- Evaluation of basepoint transport is the final value of its homotopy. -/
theorem pathMap_apply (γ : Path x y) (p : GenLoop N X x) (z : N → I) :
    pathMap γ p z = homotopyAlong γ p (1, z) :=
  ((homotopyAlong γ p).map_one_left z).symm

/-- The moving-boundary homotopy starts at the original generalized loop. -/
theorem homotopyAlong_apply_zero (γ : Path x y) (p : GenLoop N X x) (z : N → I) :
    homotopyAlong γ p (0, z) = p z :=
  (homotopyAlong γ p).map_zero_left z

/-- The moving-boundary homotopy ends at the transported generalized loop. -/
theorem homotopyAlong_apply_one (γ : Path x y) (p : GenLoop N X x) (z : N → I) :
    homotopyAlong γ p (1, z) = pathMap γ p z :=
  (homotopyAlong γ p).map_one_left z

/-- Every boundary point follows exactly the path used to move the basepoint. -/
@[simp]
theorem homotopyAlong_boundary (γ : Path x y) (p : GenLoop N X x)
    (t : I) (z : N → I) (hz : z ∈ Cube.boundary N) :
    homotopyAlong γ p (t, z) = γ t := by
  rcases finite_or_infinite N with h | h
  · let : Finite N := h
    rw [homotopyAlong_apply_of_finite]
    exact homotopyAlongOfFinite_boundary γ p t z hz
  · let : Infinite N := h
    rw [homotopyAlong_apply_of_infinite]
    exact homotopyAlongOfInfinite_boundary γ p GenLoop.const t hz

end GenLoop

namespace HomotopyGroup

variable {N : Type u} {X : Type v} [TopologicalSpace X] {x y : X}

/-- The function on homotopy groups induced on path components by the continuous
map of generalized loops along `γ`. -/
def pathMap (γ : Path x y) : HomotopyGroup N X x → HomotopyGroup N X y :=
  fun a => (equivZerothHomotopy N y).symm
    (ZerothHomotopy.map (GenLoop.pathMap γ) (equivZerothHomotopy N x a))

/-- Basepoint transport corresponds to the component map of the same continuous
generalized-loop map. -/
theorem equivZerothHomotopy_pathMap (γ : Path x y) (a : HomotopyGroup N X x) :
    equivZerothHomotopy N y (pathMap γ a) =
      ZerothHomotopy.map (GenLoop.pathMap γ) (equivZerothHomotopy N x a) :=
  (equivZerothHomotopy N y).apply_symm_apply _

/-- The class of a generalized loop maps to the class of its transported loop. -/
@[simp]
theorem pathMap_class (γ : Path x y) (p : GenLoop N X x) :
    pathMap γ (⟦p⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.pathMap γ p⟧ : HomotopyGroup N X y) := by
  simp only [pathMap, equivZerothHomotopy_class, ZerothHomotopy.map_mk,
    equivZerothHomotopy_symm_mk]
  rfl

end HomotopyGroup
