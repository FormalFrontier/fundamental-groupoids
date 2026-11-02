/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# The fundamental-group homomorphism of a homotopy equivalence

Mathlib's equivalence of fundamental groupoids gives an equivalence on vertex
groups by `CategoryTheory.Functor.FullyFaithful.mulEquivEnd`. Adjusting its target
basepoint by equality gives precisely `FundamentalGroup.mapOfEq` as the whole
forward homomorphism. No description of the inverse by the inverse space map is
asserted: in general that inverse also depends on the homotopy equivalence's unit.
-/

@[expose] public section

noncomputable section

universe u v

namespace FundamentalGroup

open CategoryTheory

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The vertex-group equivalence induced by a homotopy equivalence, followed by
equality adjustment of its target basepoint, has forward homomorphism `mapOfEq`.
The source and target spaces may lie in independent universes. -/
theorem homotopyEquiv_mulEquivEnd_trans_conj_toMonoidHom
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) (y : Y) (h : e.toFun x = y) :
    ((CategoryTheory.Functor.FullyFaithful.mulEquivEnd
        (C := FundamentalGroupoid X) (D := FundamentalGroupoid Y)
        (f := FundamentalGroupoid.map e.toFun)
        (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor
        (FundamentalGroupoid.mk x)).trans
      (CategoryTheory.Iso.conj (C := FundamentalGroupoid Y)
        (eqToIso (congrArg FundamentalGroupoid.mk h)))).toMonoidHom =
        mapOfEq e.toFun h := by
  rfl

end FundamentalGroup
