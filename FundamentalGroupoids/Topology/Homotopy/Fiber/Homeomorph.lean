/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber

/-!
# Homeomorphisms of ordinary homotopy fibers

A commutative square with homeomorphisms on its two coordinate spaces induces
an ordinary compact-open homotopy-fiber homeomorphism. It sends the retained
point through the source homeomorphism and postcomposes the entire path with
the target homeomorphism, without changing the path parameter. The forward and
inverse functions are the existing maps of homotopy fibers. Their inverse,
identity and composition laws follow from `map_comp` and `map_id`.

## Implementation notes

The spaces have the ordinary product/subspace and compact-open topologies.
The four coordinate spaces have independent universes and arbitrary topologies;
no embedding or separation assumption is required. Paths run from the specified
point at time zero to the image of the retained source point at time one.

## References

* `FundamentalGroupoids.Topology.Homotopy.Fiber`, for the homotopy-fiber map,
  its functorial laws and the endpoint-path comparison.
* Mathlib's homeomorphism and bundled continuous-map APIs, for coordinate
  cancellation and composition.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

universe uX uY uX' uY' uX'' uY''

variable {X : Type uX} {Y : Type uY} {X' : Type uX'} {Y' : Type uY'}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [TopologicalSpace X'] [TopologicalSpace Y']
variable {f : C(X, Y)} {g : C(X', Y')} {y : Y} {y' : Y'}

/-- Reversing the coordinate homeomorphisms reverses a commuting square. -/
theorem homeomorph_symm_comm (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) :
    ∀ x', f (eX.symm x') = eY.symm (g x') := by
  intro x'
  apply eY.eq_symm_apply.2
  simpa only [Homeomorph.apply_symm_apply] using (w (eX.symm x')).symm

/-- The homeomorphism of ordinary homotopy fibers induced by a commutative square
whose source and target coordinate maps are homeomorphisms, at the specified
points `y` and `y'` satisfying `eY y = y'`. -/
def homeomorph (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') :
    HomotopyFiber f y ≃ₜ HomotopyFiber g y' where
  toFun := map (f := f) (f' := g) (b := y) (b' := y')
    (eX : C(X, X')) (eY : C(Y, Y')) w hy
  invFun := map (f := g) (f' := f) (b := y') (b' := y)
    (eX.symm : C(X', X)) (eY.symm : C(Y', Y))
    (homeomorph_symm_comm eX eY w) ((eY.symm_apply_eq).2 hy.symm)
  left_inv := by
    intro z
    have hcomp := map_comp (f := f) (f' := g) (f'' := f)
      (b := y) (b' := y') (b'' := y)
      (eX : C(X, X')) (eY : C(Y, Y'))
      (eX.symm : C(X', X)) (eY.symm : C(Y', Y))
      w (homeomorph_symm_comm eX eY w) hy ((eY.symm_apply_eq).2 hy.symm)
    simpa only [Homeomorph.symm_comp_toContinuousMap, map_id,
      ContinuousMap.comp_apply, ContinuousMap.id_apply] using
      congrArg (fun k : C(HomotopyFiber f y, HomotopyFiber f y) => k z) hcomp
  right_inv := by
    intro z
    have hcomp := map_comp (f := g) (f' := f) (f'' := g)
      (b := y') (b' := y) (b'' := y')
      (eX.symm : C(X', X)) (eY.symm : C(Y', Y))
      (eX : C(X, X')) (eY : C(Y, Y'))
      (homeomorph_symm_comm eX eY w) w ((eY.symm_apply_eq).2 hy.symm) hy
    simpa only [Homeomorph.toContinuousMap_comp_symm, map_id,
      ContinuousMap.comp_apply, ContinuousMap.id_apply] using
      congrArg (fun k : C(HomotopyFiber g y', HomotopyFiber g y') => k z) hcomp
  continuous_toFun := (map (f := f) (f' := g) (b := y) (b' := y')
    (eX : C(X, X')) (eY : C(Y, Y')) w hy).continuous
  continuous_invFun := (map (f := g) (f' := f) (b := y') (b' := y)
    (eX.symm : C(X', X)) (eY.symm : C(Y', Y))
    (homeomorph_symm_comm eX eY w) ((eY.symm_apply_eq).2 hy.symm)).continuous

/-- The forward continuous map is the existing map of homotopy fibers. -/
@[simp]
theorem homeomorph_toContinuousMap (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') :
    (homeomorph eX eY w hy : C(HomotopyFiber f y, HomotopyFiber g y')) =
      map (eX : C(X, X')) (eY : C(Y, Y')) w hy := by
  rfl

/-- The inverse continuous map is the existing map for the inverse coordinates. -/
theorem homeomorph_symm_toContinuousMap (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') :
    ((homeomorph eX eY w hy).symm : C(HomotopyFiber g y', HomotopyFiber f y)) =
      map (eX.symm : C(X', X)) (eY.symm : C(Y', Y))
        (homeomorph_symm_comm eX eY w) ((eY.symm_apply_eq).2 hy.symm) := by
  rfl

/-- The retained point follows the source coordinate homeomorphism. -/
@[simp]
theorem point_homeomorph (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') (z : HomotopyFiber f y) :
    point (homeomorph eX eY w hy z) = eX (point z) := by
  exact point_map (eX : C(X, X')) (eY : C(Y, Y')) w hy z

/-- The whole compact-open path is postcomposed, with its parameter unchanged. -/
@[simp]
theorem path_homeomorph (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') (z : HomotopyFiber f y) :
    path (homeomorph eX eY w hy z) = (eY : C(Y, Y')).comp (path z) := by
  exact path_map (eX : C(X, X')) (eY : C(Y, Y')) w hy z

/-- At every time the path value follows the target coordinate homeomorphism. -/
theorem eval_homeomorph (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y')
    (z : HomotopyFiber f y) (t : I) :
    eval t (homeomorph eX eY w hy z) = eY (eval t z) := by
  exact eval_map (eX : C(X, X')) (eY : C(Y, Y')) w hy z t

/-- The inverse retained point follows the inverse source homeomorphism. -/
theorem point_homeomorph_symm (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') (z : HomotopyFiber g y') :
    point ((homeomorph eX eY w hy).symm z) = eX.symm (point z) := by
  exact point_map (eX.symm : C(X', X)) (eY.symm : C(Y', Y))
    (homeomorph_symm_comm eX eY w) ((eY.symm_apply_eq).2 hy.symm) z

/-- The inverse keeps the complete path parameter and postcomposes by `eY.symm`. -/
theorem path_homeomorph_symm (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') (z : HomotopyFiber g y') :
    path ((homeomorph eX eY w hy).symm z) =
      (eY.symm : C(Y', Y)).comp (path z) := by
  exact path_map (eX.symm : C(X', X)) (eY.symm : C(Y', Y))
    (homeomorph_symm_comm eX eY w) ((eY.symm_apply_eq).2 hy.symm) z

/-- At every time the inverse path value follows the inverse target homeomorphism. -/
theorem eval_homeomorph_symm (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y')
    (z : HomotopyFiber g y') (t : I) :
    eval t ((homeomorph eX eY w hy).symm z) = eY.symm (eval t z) := by
  exact eval_map (eX.symm : C(X', X)) (eY.symm : C(Y', Y))
    (homeomorph_symm_comm eX eY w) ((eY.symm_apply_eq).2 hy.symm) z t

/-- Reversing the coordinate square reverses the homotopy-fiber homeomorphism. -/
@[simp]
theorem homeomorph_symm (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') :
    (homeomorph eX eY w hy).symm =
      homeomorph (f := g) (g := f) (y := y') (y' := y) eX.symm eY.symm
        (homeomorph_symm_comm eX eY w) ((eY.symm_apply_eq).2 hy.symm) := by
  apply ContinuousMap.coe_injective'
  simp only [homeomorph_symm_toContinuousMap, homeomorph_toContinuousMap]

/-- The identity coordinate square induces the identity homeomorphism. -/
@[simp]
theorem homeomorph_refl :
    homeomorph (f := f) (g := f) (y := y) (y' := y)
        (Homeomorph.refl X) (Homeomorph.refl Y) (fun _ => rfl) rfl =
      Homeomorph.refl (HomotopyFiber f y) := by
  apply ContinuousMap.coe_injective'
  exact map_id (f := f) (b := y)

/-- Composing coordinate squares composes their homotopy-fiber homeomorphisms. -/
theorem homeomorph_trans
    {X'' : Type uX''} {Y'' : Type uY''} [TopologicalSpace X''] [TopologicalSpace Y'']
    {h : C(X'', Y'')} {y'' : Y''}
    (eX : X ≃ₜ X') (eY : Y ≃ₜ Y') (eX' : X' ≃ₜ X'') (eY' : Y' ≃ₜ Y'')
    (w : ∀ x, g (eX x) = eY (f x)) (w' : ∀ x', h (eX' x') = eY' (g x'))
    (hy : eY y = y') (hy' : eY' y' = y'') :
    (homeomorph eX eY w hy).trans
        (homeomorph (f := g) (g := h) (y := y') (y' := y'') eX' eY' w' hy') =
      homeomorph (f := f) (g := h) (y := y) (y' := y'')
        (eX.trans eX') (eY.trans eY')
        (fun x => (w' (eX x)).trans (congrArg eY' (w x)))
        ((congrArg eY' hy).trans hy') := by
  apply ContinuousMap.coe_injective'
  exact map_comp (eX : C(X, X')) (eY : C(Y, Y'))
    (eX' : C(X', X'')) (eY' : C(Y', Y'')) w w' hy hy'

/-- The point projection commutes with the coordinate homeomorphism square. -/
theorem point_comp_homeomorph (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') :
    (point (f := g) (b := y')).comp
        (homeomorph eX eY w hy : C(HomotopyFiber f y, HomotopyFiber g y')) =
      (eX : C(X, X')).comp (point (f := f) (b := y)) := by
  apply ContinuousMap.ext
  intro z
  exact point_homeomorph eX eY w hy z

/-- The fiber homeomorphism commutes with the existing endpoint-path comparison. -/
theorem endpointHomeomorph_homeomorph
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g)
    (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (w : ∀ x, g (eX x) = eY (f x)) (hy : eY y = y') (z : HomotopyFiber f y) :
    endpointHomeomorph hg y' (homeomorph eX eY w hy z) =
      RelativePathSpace.map (eY : C(Y, Y'))
        (mapsTo_range (eX : C(X, X')) (eY : C(Y, Y')) w) hy
        (endpointHomeomorph hf y z) := by
  exact endpointHomeomorph_naturality hf hg (eX : C(X, X')) (eY : C(Y, Y')) w hy z

end ContinuousMap.HomotopyFiber
