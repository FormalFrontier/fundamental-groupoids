/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Path

/-!
# Maps on path components

`ZerothHomotopy.map` is the map on path components induced by a continuous map.
It uses the existing quotient by `Joined`, preserves representatives, and obeys
the identity and composition laws. Homotopic continuous maps induce the same
function on path components. `ZerothHomotopy.equivOfHomotopyEquiv` bundles the
component map of a homotopy equivalence as an equivalence, compatibly with
identities, inverses and composition. Space universes are independent, and no
separation or connectedness assumption is imposed.

## References

The definition and proofs originate in the path-component API of Restricted
Product Duality's `RestrictedProductDuality.HomotopyMaps`, by Formal Frontier
Agents, with their Apache-2.0 and authorship notices retained. They reuse Mathlib's
path components and `Joined.map` (Patrick Massot and contributors), homotopies
(Shing Tak Lam and contributors), and quotient maps.
-/

@[expose] public section

universe u v w

namespace ZerothHomotopy

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The map on path components induced by a continuous map. -/
def map (f : C(X, Y)) : ZerothHomotopy X → ZerothHomotopy Y :=
  @Quotient.map X Y (pathSetoid X) (pathSetoid Y) f
    (fun _ _ h ↦ h.map f.continuous)

/-- The induced component map sends the component of a point to that of its image. -/
@[simp]
theorem map_mk (f : C(X, Y)) (x : X) :
    map f (mk x) = mk (f x) :=
  rfl

/-- A point's component is in the induced map's range exactly when the image of some
source point can be joined to it by a path. -/
theorem mem_range_map_iff (f : C(X, Y)) (y : Y) :
    mk y ∈ Set.range (map f) ↔ ∃ x : X, Joined y (f x) := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨x, rfl⟩ := mk_surjective q
    rw [map_mk] at hq
    exact ⟨x, Joined.symm (Quotient.eq.mp hq)⟩
  · rintro ⟨x, h⟩
    refine ⟨mk x, ?_⟩
    rw [map_mk]
    exact Quotient.eq.mpr h.symm

/-- The identity fixes every path component. -/
@[simp]
theorem map_id (q : ZerothHomotopy X) :
    map (ContinuousMap.id X) q = q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- The component map of a composite acts by successive component maps. -/
theorem map_comp (g : C(Y, Z)) (f : C(X, Y)) (q : ZerothHomotopy X) :
    map (g.comp f) q = map g (map f q) := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- Homotopic continuous maps induce the same function on path components. -/
theorem map_eq_of_homotopy (f g : C(X, Y))
    (H : ContinuousMap.Homotopy f g) : map f = map g := by
  funext q
  induction q using ZerothHomotopy.rec with
  | mk x =>
    rw [map_mk, map_mk]
    exact ZerothHomotopy.sound (H.evalAt x)

/-- A homotopy equivalence induces a bijection on path components. -/
theorem bijective_map_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    Function.Bijective (map e.toFun) := by
  rcases e.left_inv with ⟨hleft⟩
  rcases e.right_inv with ⟨hright⟩
  refine Function.bijective_iff_has_inverse.mpr ⟨map e.invFun, ?_, ?_⟩
  · intro q
    simpa only [map_comp, map_id] using
      congrFun (map_eq_of_homotopy _ _ hleft) q
  · intro q
    simpa only [map_comp, map_id] using
      congrFun (map_eq_of_homotopy _ _ hright) q

/-- The equivalence on path components induced by a homotopy equivalence. -/
noncomputable def equivOfHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    ZerothHomotopy X ≃ ZerothHomotopy Y :=
  Equiv.ofBijective (map e.toFun) (bijective_map_of_homotopyEquiv e)

/-- The underlying function is the component map of the forward continuous map. -/
@[simp]
theorem coe_equivOfHomotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    (equivOfHomotopyEquiv e : ZerothHomotopy X → ZerothHomotopy Y) = map e.toFun :=
  rfl

/-- The induced equivalence sends a point's component to its image's component. -/
theorem equivOfHomotopyEquiv_mk (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    equivOfHomotopyEquiv e (mk x) = mk (e x) := by
  simpa only [coe_equivOfHomotopyEquiv] using map_mk e.toFun x

/-- The identity homotopy equivalence induces the identity on path components. -/
@[simp]
theorem equivOfHomotopyEquiv_refl :
    equivOfHomotopyEquiv (ContinuousMap.HomotopyEquiv.refl X) =
      Equiv.refl (ZerothHomotopy X) := by
  have h : (ContinuousMap.HomotopyEquiv.refl X).toFun = ContinuousMap.id X := by
    apply ContinuousMap.ext
    intro x
    simpa only [ContinuousMap.id_apply] using
      ContinuousMap.HomotopyEquiv.refl_apply X x
  ext q
  simpa only [coe_equivOfHomotopyEquiv, h, Equiv.refl_apply] using map_id q

/-- Composition of homotopy equivalences induces composition on path components. -/
@[simp]
theorem equivOfHomotopyEquiv_trans (e : ContinuousMap.HomotopyEquiv X Y)
    (f : ContinuousMap.HomotopyEquiv Y Z) :
    equivOfHomotopyEquiv (e.trans f) =
      (equivOfHomotopyEquiv e).trans (equivOfHomotopyEquiv f) := by
  have h : (e.trans f).toFun = f.toFun.comp e.toFun := by
    apply ContinuousMap.ext
    intro x
    simpa only [ContinuousMap.comp_apply] using
      ContinuousMap.HomotopyEquiv.trans_apply e f x
  ext q
  simpa only [coe_equivOfHomotopyEquiv, h, Equiv.trans_apply] using
    map_comp f.toFun e.toFun q

/-- The inverse component equivalence is induced by the inverse homotopy equivalence. -/
@[simp]
theorem equivOfHomotopyEquiv_symm (e : ContinuousMap.HomotopyEquiv X Y) :
    (equivOfHomotopyEquiv e).symm = equivOfHomotopyEquiv e.symm := by
  have hsymm : e.symm.toFun = e.invFun := by
    apply ContinuousMap.ext
    intro x
    exact (congrFun (ContinuousMap.HomotopyEquiv.coe_invFun e) x).symm
  apply Eq.symm
  apply Equiv.eq_symm_iff_trans_eq_refl.mpr
  rcases e.right_inv with ⟨H⟩
  ext q
  simpa only [Equiv.trans_apply, coe_equivOfHomotopyEquiv, Equiv.refl_apply,
    hsymm, map_comp, map_id] using congrFun (map_eq_of_homotopy _ _ H) q

/-- Homotopic forward maps induce the same equivalence on path components. -/
theorem equivOfHomotopyEquiv_eq_of_homotopic (e f : ContinuousMap.HomotopyEquiv X Y)
    (h : e.toFun.Homotopic f.toFun) :
    equivOfHomotopyEquiv e = equivOfHomotopyEquiv f := by
  rcases h with ⟨H⟩
  ext q
  simpa only [coe_equivOfHomotopyEquiv] using congrFun (map_eq_of_homotopy _ _ H) q

end ZerothHomotopy
