/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.Path

/-!
# Maps on path components

`ZerothHomotopy.map` is the map on path components induced by a continuous map.
It uses the existing quotient by `Joined`, preserves representatives, and obeys
the identity and composition laws. Homotopic continuous maps induce the same
function on path components. Space universes are independent, and no separation
or connectedness assumption is imposed.

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

end ZerothHomotopy
