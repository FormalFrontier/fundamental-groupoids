/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Covering.GenLoop

/-!
# Covering maps on homotopy groups

A covering map induces an injection on the cubical homotopy quotient for every
nonempty index type, and a bijection for every nontrivial index type. With the
stock group structures, the latter gives a multiplicative equivalence whose
forward homomorphism is the existing `HomotopyGroup.map`. Its inverse takes a
representative class to the class of its chosen based lift `IsCoveringMap.liftGenLoop`.

The total space, base space and cube index have independent universes. The chosen
point `e` determines the target point `f e`; no global surjectivity, connectedness,
local path connectedness or separation assumption on either space is imposed.
Decidable equality on the index is needed only for the stock group structures,
not for injectivity or bijectivity of `HomotopyGroup.mapFun`.

These statements use Mathlib's generalized loops and homotopies relative to
`Cube.boundary N`, the union of the coordinate faces where a coordinate is zero
or one. For arbitrary index types this is a cubical extension of the classical
finite-degree covering theorem, not an assertion about topological frontiers of
infinite products. It does not identify these groups with sphere-domain or
U-topology homotopy groups. For `N = Fin n`, the bijectivity and multiplicative
equivalence apply in degrees `n ≥ 2`.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 9 §1 and §4,
  pp. 65–67, for based homotopy groups and the classical covering isomorphism
  in degrees at least two.
* Mathlib's `Mathlib.Topology.Homotopy.HomotopyGroup` (Roberto Alvarez) and
  `Mathlib.Topology.Homotopy.Lifting` (Junyan Xu).
-/

@[expose] public section

universe u v w

namespace IsCoveringMap

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {f : E → B}

/-- A covering map induces an injection on the boundary-relative homotopy quotient
for a nonempty cube index, without decidable equality on that index. -/
theorem injective_homotopyGroup_mapFun (hf : IsCoveringMap f)
    (N : Type w) [Nonempty N] (e : E) :
    Function.Injective (HomotopyGroup.mapFun N ⟨f, hf.continuous⟩ (x := e) rfl) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro p q hpq
  rw [HomotopyGroup.mapFun_class, HomotopyGroup.mapFun_class] at hpq
  apply Quotient.sound
  have hz : (0 : N → unitInterval) ∈ Cube.boundary N := Cube.zero_mem_boundary N
  have he : ∃ a ∈ Cube.boundary N, p a = q a :=
    ⟨0, hz, (GenLoop.boundary p 0 hz).trans (GenLoop.boundary q 0 hz).symm⟩
  exact (hf.homotopicRel_iff_comp (f₀ := p.1) (f₁ := q.1) he).mpr
    (Quotient.exact hpq)

/-- A covering map induces a bijection on the boundary-relative homotopy quotient
for a nontrivial cube index, without decidable equality on that index.

For arbitrary index types this is a derived extension in the cubical,
boundary-relative model of the classical finite-degree covering theorem in May,
*A Concise Course in Algebraic Topology*, Chapter 9 §4 (printed p. 66).
No comparison with sphere-domain homotopy groups is supplied. -/
theorem bijective_homotopyGroup_mapFun (hf : IsCoveringMap f)
    (N : Type w) [Nontrivial N] (e : E) :
    Function.Bijective (HomotopyGroup.mapFun N ⟨f, hf.continuous⟩ (x := e) rfl) := by
  refine ⟨hf.injective_homotopyGroup_mapFun N e, ?_⟩
  intro a
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N B (f e) ↦
      ∃ b : HomotopyGroup N E e,
        HomotopyGroup.mapFun N ⟨f, hf.continuous⟩ (x := e) rfl b = a) a ?_
  intro p
  refine ⟨(⟦hf.liftGenLoop e p⟧ : HomotopyGroup N E e), ?_⟩
  exact Eq.trans (α := HomotopyGroup N B (f e))
    (HomotopyGroup.mapFun_class N ⟨f, hf.continuous⟩ rfl (hf.liftGenLoop e p))
    (congrArg (fun r : GenLoop N B (f e) ↦ (⟦r⟧ : HomotopyGroup N B (f e)))
      (hf.map_liftGenLoop e p))

/-- The multiplicative equivalence induced by a covering map for a nontrivial
cube index, with forward homomorphism `HomotopyGroup.map`.

For arbitrary index types this is a derived cubical, boundary-relative extension
of the classical finite-degree covering isomorphism in May, *A Concise Course in
Algebraic Topology*, Chapter 9 §4 (printed p. 66). No comparison with sphere-domain
homotopy groups is supplied. -/
noncomputable def homotopyGroupMulEquiv (hf : IsCoveringMap f)
    (N : Type w) [DecidableEq N] [Nontrivial N] (e : E) :
    HomotopyGroup N E e ≃* HomotopyGroup N B (f e) :=
  MulEquiv.ofBijective (HomotopyGroup.map N ⟨f, hf.continuous⟩ (x := e) rfl) (by
    rw [HomotopyGroup.coe_map_eq_mapFun]
    exact hf.bijective_homotopyGroup_mapFun N e)

/-- The forward homomorphism of the covering equivalence is the canonical
homotopy-group map, with the supplied stock group structures. -/
theorem homotopyGroupMulEquiv_toMonoidHom (hf : IsCoveringMap f)
    (N : Type w) [DecidableEq N] [Nontrivial N] (e : E) :
    (hf.homotopyGroupMulEquiv N e).toMonoidHom =
      HomotopyGroup.map N ⟨f, hf.continuous⟩ (x := e) rfl := by
  rfl

/-- On a representative class, the covering equivalence is postcomposition of
that generalized loop by the covering map. -/
theorem homotopyGroupMulEquiv_apply_class (hf : IsCoveringMap f)
    (N : Type w) [DecidableEq N] [Nontrivial N] (e : E) (p : GenLoop N E e) :
    hf.homotopyGroupMulEquiv N e (⟦p⟧ : HomotopyGroup N E e) =
      (⟦GenLoop.map ⟨f, hf.continuous⟩ rfl p⟧ : HomotopyGroup N B (f e)) := by
  rfl

/-- A generalized-loop lift represents the inverse image of the projected class
under the covering equivalence. The hypothesis specifies only this particular
lift, not the existence of lifts for all generalized loops. -/
theorem homotopyGroupMulEquiv_symm_apply_class_of_map_eq (hf : IsCoveringMap f)
    (N : Type w) [DecidableEq N] [Nontrivial N] (e : E)
    (p : GenLoop N E e) (q : GenLoop N B (f e))
    (h : GenLoop.map ⟨f, hf.continuous⟩ rfl p = q) :
    (hf.homotopyGroupMulEquiv N e).symm (⟦q⟧ : HomotopyGroup N B (f e)) =
      (⟦p⟧ : HomotopyGroup N E e) := by
  apply (hf.homotopyGroupMulEquiv N e).injective
  exact Eq.trans (α := HomotopyGroup N B (f e))
    ((hf.homotopyGroupMulEquiv N e).apply_symm_apply
      (⟦q⟧ : HomotopyGroup N B (f e)))
    (Eq.trans (α := HomotopyGroup N B (f e))
      (hf.homotopyGroupMulEquiv_apply_class N e p)
      (congrArg (fun r : GenLoop N B (f e) ↦ (⟦r⟧ : HomotopyGroup N B (f e))) h)).symm

/-- The inverse covering equivalence sends a representative class to the class
of its chosen based generalized-loop lift. -/
theorem homotopyGroupMulEquiv_symm_apply_class (hf : IsCoveringMap f)
    (N : Type w) [DecidableEq N] [Nontrivial N] (e : E)
    (p : GenLoop N B (f e)) :
    (hf.homotopyGroupMulEquiv N e).symm (⟦p⟧ : HomotopyGroup N B (f e)) =
      (⟦hf.liftGenLoop e p⟧ : HomotopyGroup N E e) :=
  hf.homotopyGroupMulEquiv_symm_apply_class_of_map_eq N e
    (hf.liftGenLoop e p) p (hf.map_liftGenLoop e p)

end IsCoveringMap
