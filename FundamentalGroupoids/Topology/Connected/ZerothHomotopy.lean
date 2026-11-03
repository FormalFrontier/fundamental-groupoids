/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Connected.PathConnected
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Evaluation of path components that are points

For a space whose path components are subsingletons, the identity function descends to
an evaluator on `ZerothHomotopy X`. The evaluator and the canonical class map are continuous
for the original topology on `X` and the existing quotient topology on `ZerothHomotopy X`.
They form `ZerothHomotopy.homeomorphOfSubsingletonPathComponent`, and both maps commute
with continuous maps between such spaces.

The class map and its naturality need no hypothesis on path components. Neither the
class map nor evaluation chooses a basepoint or assumes the space is nonempty.

`ZerothHomotopy.homeomorphOfTotallyDisconnectedSpace` specializes the homeomorphism to
totally disconnected spaces. The existing instances include spaces with a discrete topology.
-/

@[expose] public section

universe u v

namespace ZerothHomotopy

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The canonical continuous map sending a point to its path component. -/
@[no_expose]
def mkContinuousMap : C(X, ZerothHomotopy X) where
  toFun := mk
  continuous_toFun := isQuotientMap_mk.continuous

/-- The underlying function of the continuous class map is `ZerothHomotopy.mk`. -/
theorem coe_mkContinuousMap : ⇑(mkContinuousMap (X := X)) = mk :=
  ContinuousMap.coe_mk _ _

/-- The continuous class map agrees with `ZerothHomotopy.mk` on every point. -/
@[simp]
theorem mkContinuousMap_apply (x : X) : mkContinuousMap x = mk x :=
  congrFun coe_mkContinuousMap x

private theorem eq_of_path (hX : ∀ x : X, (pathComponent x).Subsingleton)
    {x y : X} (p : Path x y) : x = y :=
  hX x (mem_pathComponent_self x) (mem_pathComponent_iff.mpr ⟨p⟩)

/-- Evaluation of a path component when each path component contains at most one point. -/
@[no_expose]
def eval (hX : ∀ x : X, (pathComponent x).Subsingleton) : C(ZerothHomotopy X, X) where
  toFun := lift (fun x : X => x) (by
    exact fun {x y} p => eq_of_path hX (x := x) (y := y) p)
  continuous_toFun := by
    apply (isQuotientMap_mk (X := X)).continuous_iff.mpr
    apply (continuous_id : Continuous (id : X → X)).congr
    intro x
    exact (lift_mk (fun x : X => x)
      (fun {x y} p => eq_of_path hX (x := x) (y := y) p) x).symm

/-- Evaluation sends the path component of a point back to that point. -/
@[simp]
theorem eval_mk (hX : ∀ x : X, (pathComponent x).Subsingleton) (x : X) :
    eval hX (mk x) = x :=
  lift_mk (fun x : X => x) (fun {x y} p => eq_of_path hX (x := x) (y := y) p) x

/-- The class of the evaluation of a path component is the original component. -/
theorem mk_eval (hX : ∀ x : X, (pathComponent x).Subsingleton) (q : ZerothHomotopy X) :
    mk (eval hX q) = q := by
  rcases mk_surjective q with ⟨x, rfl⟩
  rw [eval_mk]

/-- Evaluation is bijective when every path component is a subsingleton. -/
theorem eval_bijective (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    Function.Bijective (eval hX) := by
  constructor
  · intro q r h
    calc
      q = mk (eval hX q) := (mk_eval hX q).symm
      _ = mk (eval hX r) := congrArg mk h
      _ = r := mk_eval hX r
  · intro x
    exact ⟨mk x, eval_mk hX x⟩

/-- Evaluation is a homeomorphism when every path component contains at most one point.
Its inverse is the canonical continuous class map. -/
@[no_expose]
def homeomorphOfSubsingletonPathComponent (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    ZerothHomotopy X ≃ₜ X where
  toFun := eval hX
  invFun := mkContinuousMap
  left_inv := by
    intro q
    simpa only [mkContinuousMap_apply] using mk_eval hX q
  right_inv := by
    intro x
    simpa only [mkContinuousMap_apply] using eval_mk hX x
  continuous_toFun := (eval hX).continuous
  continuous_invFun := (mkContinuousMap (X := X)).continuous

/-- The forward function of the homeomorphism is evaluation of path components. -/
theorem homeomorphOfSubsingletonPathComponent_coe
    (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    (homeomorphOfSubsingletonPathComponent hX : ZerothHomotopy X → X) = eval hX :=
  Homeomorph.homeomorph_mk_coe _ _ _

/-- The inverse function of the homeomorphism is the continuous class map. -/
theorem homeomorphOfSubsingletonPathComponent_symm_coe
    (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    ((homeomorphOfSubsingletonPathComponent hX).symm : X → ZerothHomotopy X) =
      mkContinuousMap :=
  Homeomorph.homeomorph_mk_coe_symm _ _ _

/-- The homeomorphism of pointlike path components evaluates each component. -/
@[simp]
theorem homeomorphOfSubsingletonPathComponent_apply
    (hX : ∀ x : X, (pathComponent x).Subsingleton) (q : ZerothHomotopy X) :
    homeomorphOfSubsingletonPathComponent hX q = eval hX q :=
  congrFun (homeomorphOfSubsingletonPathComponent_coe hX) q

/-- The inverse homeomorphism is the canonical continuous class map on every point. -/
theorem homeomorphOfSubsingletonPathComponent_symm_apply
    (hX : ∀ x : X, (pathComponent x).Subsingleton) (x : X) :
    (homeomorphOfSubsingletonPathComponent hX).symm x = mkContinuousMap x :=
  congrFun (homeomorphOfSubsingletonPathComponent_symm_coe hX) x

/-- Evaluation and the canonical class map are the two maps of a homeomorphism. -/
theorem exists_homeomorph (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    ∃ e : ZerothHomotopy X ≃ₜ X,
      (∀ q, e q = eval hX q) ∧ ∀ x, e.symm x = mkContinuousMap x := by
  exact ⟨homeomorphOfSubsingletonPathComponent hX,
    homeomorphOfSubsingletonPathComponent_apply hX,
    homeomorphOfSubsingletonPathComponent_symm_apply hX⟩

/-- Taking path components commutes with a continuous map, as an equality of functions. -/
theorem mkContinuousMap_natural (f : C(X, Y)) :
    map f ∘ mkContinuousMap = mkContinuousMap ∘ f := by
  funext x
  simp only [Function.comp_apply, mkContinuousMap_apply, map_mk]

/-- Evaluation commutes with continuous maps between spaces with pointlike path components. -/
theorem eval_natural (hX : ∀ x : X, (pathComponent x).Subsingleton)
    (hY : ∀ y : Y, (pathComponent y).Subsingleton) (f : C(X, Y)) :
    eval hY ∘ map f = f ∘ eval hX := by
  funext q
  rcases mk_surjective q with ⟨x, rfl⟩
  simp only [Function.comp_apply, map_mk, eval_mk]

/-- A totally disconnected space is homeomorphic to its space of path components,
with inverse given by the canonical continuous class map. -/
@[no_expose]
noncomputable def homeomorphOfTotallyDisconnectedSpace [TotallyDisconnectedSpace X] :
    ZerothHomotopy X ≃ₜ X :=
  homeomorphOfSubsingletonPathComponent (by
    intro x y hy z hz
    exact
      (totallyDisconnectedSpace_iff_connectedComponent_subsingleton.mp
        (inferInstance : TotallyDisconnectedSpace X) x)
        (pathComponent_subset_component x hy) (pathComponent_subset_component x hz))

/-- The inverse homeomorphism for a totally disconnected space is the class map. -/
theorem homeomorphOfTotallyDisconnectedSpace_symm_apply [TotallyDisconnectedSpace X] (x : X) :
    (homeomorphOfTotallyDisconnectedSpace (X := X)).symm x = mkContinuousMap x :=
  homeomorphOfSubsingletonPathComponent_symm_apply _ x

/-- The homeomorphism for a totally disconnected space sends a point's class to that point. -/
@[simp]
theorem homeomorphOfTotallyDisconnectedSpace_mk [TotallyDisconnectedSpace X] (x : X) :
    homeomorphOfTotallyDisconnectedSpace (mk x) = x := by
  have h := (homeomorphOfTotallyDisconnectedSpace (X := X)).apply_symm_apply x
  simpa only [homeomorphOfTotallyDisconnectedSpace_symm_apply, mkContinuousMap_apply] using h

end ZerothHomotopy
