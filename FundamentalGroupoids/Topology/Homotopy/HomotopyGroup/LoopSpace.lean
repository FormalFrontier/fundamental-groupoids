/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Connected.PathConnected
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map
public import FundamentalGroupoids.Topology.Homotopy.Relative

/-!
# Homotopy classes as components of generalized-loop spaces

`GenLoop.homotopic_iff_joined` identifies homotopy relative to the cube boundary
with being joined by a path in the same generalized-loop space. The topology on
`GenLoop N X x` is the subtype topology inherited from the compact-open topology
on continuous cube maps; no topology is changed in making this comparison.

`HomotopyGroup.equivZerothHomotopy` descends the identity on representatives to
an equivalence between the existing boundary-relative homotopy quotient and the
path components of that generalized-loop space. Its forward and inverse laws
send the class of a generalized loop to the class of that very same loop, and
in particular preserve the chosen constant class. The comparison commutes with
based postcomposition through the component map of the same continuous
`GenLoop.map`. For an empty cube index, the component map of
`genLoopHomeoOfIsEmpty` recovers `homotopyGroupEquivZerothHomotopyOfIsEmpty`,
including classes represented by arbitrary values of the target.

The cube index and target have independent universes. The index may be empty
or infinite, and the target requires only a topology and a chosen point.

## Limitations

This compact-open cubical comparison does not identify sphere-based classes,
kified mapping spaces or weak-Hausdorff k-spaces, and does not provide a finite
iterated-loop comparison. No group structure on path components is introduced:
the existing positive homotopy-group operations retain
`HomotopyGroup.mul_spec`, whose representative law concatenates the right
factor before the left factor.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 8, §1,
  pp. 57–58, for the based mapping-space interpretation of based homotopy
  classes. The comparison here uses compact-open cube maps.
* Mathlib's generalized loops and homotopy groups are due to Roberto Alvarez;
  its relative homotopies to Shing Tak Lam and contributors. The construction
  uses Mathlib's `Joined`, `ZerothHomotopy` and `Quotient.congr` APIs.
-/

@[expose] public section

universe u v w

namespace GenLoop

variable {N : Type u} {X : Type v} [TopologicalSpace X] {x : X}

/-- Homotopy relative to the cube boundary is equivalent to being joined by a
path in the compact-open generalized-loop space. This is the cubical analogue
of the based mapping-space comparison in May, Chapter 8, §1. -/
theorem homotopic_iff_joined (p q : GenLoop N X x) :
    GenLoop.Homotopic p q ↔ Joined p q := by
  refine Iff.trans ?_ (ContinuousMap.HomotopyWith.nonempty_iff_joined
    (f := p.val) (g := q.val)
    (P := fun f ↦ ∀ y ∈ Cube.boundary N, f y = x) p.property q.property)
  constructor
  · rintro ⟨H⟩
    exact ⟨{ toHomotopy := H.toHomotopy
             prop' := fun t y hy ↦ (H.eq_fst t hy).trans (p.property y hy) }⟩
  · rintro ⟨H⟩
    exact ⟨{ toHomotopy := H.toHomotopy
             prop' := fun t y hy ↦ (H.prop t y hy).trans (p.property y hy).symm }⟩

end GenLoop

namespace HomotopyGroup

variable {X : Type v} [TopologicalSpace X]

/-- The boundary-relative homotopy quotient is the path-component set of the
same compact-open generalized-loop space, by the identity on representatives. -/
def equivZerothHomotopy (N : Type u) (x : X) :
    HomotopyGroup N X x ≃ ZerothHomotopy (GenLoop N X x) :=
  Quotient.congr
    (ra := GenLoop.Homotopic.setoid N x)
    (rb := pathSetoid (GenLoop N X x))
    (Equiv.refl (GenLoop N X x))
    (fun p q ↦ GenLoop.homotopic_iff_joined p q)

/-- The comparison sends a generalized-loop class to its path component. -/
@[simp]
theorem equivZerothHomotopy_class (N : Type u) (x : X) (p : GenLoop N X x) :
    equivZerothHomotopy N x (⟦p⟧ : HomotopyGroup N X x) = ZerothHomotopy.mk p :=
  Quotient.congr_mk
    (ra := GenLoop.Homotopic.setoid N x)
    (rb := pathSetoid (GenLoop N X x))
    (Equiv.refl (GenLoop N X x))
    (fun p q ↦ GenLoop.homotopic_iff_joined p q) p

/-- The inverse comparison sends a component representative to its
boundary-relative homotopy class. -/
@[simp]
theorem equivZerothHomotopy_symm_mk (N : Type u) (x : X) (p : GenLoop N X x) :
    (equivZerothHomotopy N x).symm (ZerothHomotopy.mk p) =
      (⟦p⟧ : HomotopyGroup N X x) :=
  (equivZerothHomotopy N x).symm_apply_eq.mpr (equivZerothHomotopy_class N x p).symm

/-- The chosen constant class maps to the component of the constant loop. -/
theorem equivZerothHomotopy_const (N : Type u) (x : X) :
    equivZerothHomotopy N x (⟦GenLoop.const⟧ : HomotopyGroup N X x) =
      ZerothHomotopy.mk (GenLoop.const : GenLoop N X x) :=
  equivZerothHomotopy_class N x GenLoop.const

/-- The component of the constant loop maps back to the chosen constant class. -/
theorem equivZerothHomotopy_symm_const (N : Type u) (x : X) :
    (equivZerothHomotopy N x).symm
        (ZerothHomotopy.mk (GenLoop.const : GenLoop N X x)) =
      (⟦GenLoop.const⟧ : HomotopyGroup N X x) :=
  equivZerothHomotopy_symm_mk N x GenLoop.const

/-- The comparison commutes with based postcomposition, using the component map
of the same continuous map of generalized-loop spaces. -/
theorem equivZerothHomotopy_mapFun (N : Type u) {Y : Type w}
    [TopologicalSpace Y] {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N X x) :
    equivZerothHomotopy N y (mapFun N f hf a) =
      ZerothHomotopy.map
        (⟨GenLoop.map f hf, GenLoop.continuous_map f hf⟩ :
          C(GenLoop N X x, GenLoop N Y y))
        (equivZerothHomotopy N x a) := by
  refine Quotient.inductionOn a ?_
  intro p
  simp only [mapFun_class, equivZerothHomotopy_class, ZerothHomotopy.map_mk]
  exact congrArg (fun q : GenLoop N Y y ↦ ZerothHomotopy.mk q)
    (show GenLoop.map f hf p =
      (⟨GenLoop.map f hf, GenLoop.continuous_map f hf⟩ :
        C(GenLoop N X x, GenLoop N Y y)).toFun p from rfl)

/-- For an empty cube index, applying the component map of its evaluation
homeomorphism recovers the comparison with components of the target space. -/
theorem equivZerothHomotopy_empty (N : Type u) [IsEmpty N] (x : X)
    (a : HomotopyGroup N X x) :
    ZerothHomotopy.map
        (⟨genLoopHomeoOfIsEmpty N x, (genLoopHomeoOfIsEmpty N x).continuous⟩ :
          C(GenLoop N X x, X))
        (equivZerothHomotopy N x a) =
      homotopyGroupEquivZerothHomotopyOfIsEmpty N x a := by
  refine Quotient.inductionOn a ?_
  intro p
  let e : C(GenLoop N X x, X) :=
    ⟨genLoopHomeoOfIsEmpty N x, (genLoopHomeoOfIsEmpty N x).continuous⟩
  calc
    ZerothHomotopy.map e
        (equivZerothHomotopy N x (⟦p⟧ : HomotopyGroup N X x)) =
        ZerothHomotopy.map e (ZerothHomotopy.mk p) :=
      congrArg (fun c : ZerothHomotopy (GenLoop N X x) ↦ ZerothHomotopy.map e c)
        (equivZerothHomotopy_class N x p)
    _ = ZerothHomotopy.mk (e p) := ZerothHomotopy.map_mk e p
    _ = homotopyGroupEquivZerothHomotopyOfIsEmpty N x
        (⟦p⟧ : HomotopyGroup N X x) := rfl

/-- At an empty cube index, the inverse of the comparison with components of `X`
sends every value to the component of its corresponding generalized loop. The
value need not be the chosen point. -/
@[simp]
theorem equivZerothHomotopy_empty_symm_mk (N : Type u) [IsEmpty N] (x y : X) :
    equivZerothHomotopy N x
        ((homotopyGroupEquivZerothHomotopyOfIsEmpty N x).symm (ZerothHomotopy.mk y)) =
      ZerothHomotopy.mk ((genLoopHomeoOfIsEmpty N x).symm y) :=
  equivZerothHomotopy_class N x ((genLoopHomeoOfIsEmpty N x).symm y)

end HomotopyGroup
