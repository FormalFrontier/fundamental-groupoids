/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Iteration.Basic

/-!
# Multiplicative loop iteration

Flattening an outer `N`-cube of `M`-loops commutes with concatenation along an
outer coordinate: the coordinate `i` becomes `Sum.inl i` in the flattened cube.
When `N` is nonempty, the all-index comparison `HomotopyGroup.genLoopEquiv`
therefore preserves the existing homotopy-group multiplication and refines to
`HomotopyGroup.genLoopMulEquiv`. The inner index `M` may be empty.

Both homotopy-group multiplications use `HomotopyGroup.mul_spec`, so the right
factor is concatenated before the left factor on both sides. The underlying
equivalence is unchanged, and no group structure on path components is used.

## References

Mathlib's generalized loops, sum-flattening homeomorphism, concatenation and
coordinate-independent homotopy-group structures are due to Roberto Alvarez.
The quotient comparison used here is provided by `HomotopyGroup.LoopSpace` and
`HomotopyGroup.Iteration.Basic`.
-/

@[expose] public section

noncomputable section

universe uN uM uX

namespace GenLoop

variable {N : Type uN} {M : Type uM} {X : Type uX} [TopologicalSpace X]

/-- Flattening commutes with concatenation in an outer coordinate, which becomes
the corresponding left-summand coordinate. Neither index need be nonempty. -/
theorem genLoopGenLoopEquiv_transAt [DecidableEq N] [DecidableEq (N ⊕ M)]
    (x : X) (i : N) (p q : GenLoop N (GenLoop M X x) GenLoop.const) :
    genLoopGenLoopEquiv x (M := N) (N := M) (transAt i p q) =
      transAt (Sum.inl i)
        (genLoopGenLoopEquiv x (M := N) (N := M) p)
        (genLoopGenLoopEquiv x (M := N) (N := M) q) := by
  apply GenLoop.ext
  intro t
  change
    (if (t (Sum.inl i) : ℝ) ≤ 1 / 2 then
      p (Function.update (t ∘ Sum.inl) i
        (Set.projIcc 0 1 zero_le_one (2 * t (Sum.inl i))))
    else
      q (Function.update (t ∘ Sum.inl) i
        (Set.projIcc 0 1 zero_le_one (2 * t (Sum.inl i) - 1)))) (t ∘ Sum.inr) =
    if (t (Sum.inl i) : ℝ) ≤ 1 / 2 then
      p (Function.update t (Sum.inl i)
          (Set.projIcc 0 1 zero_le_one (2 * t (Sum.inl i))) ∘ Sum.inl)
        (Function.update t (Sum.inl i)
          (Set.projIcc 0 1 zero_le_one (2 * t (Sum.inl i))) ∘ Sum.inr)
    else
      q (Function.update t (Sum.inl i)
          (Set.projIcc 0 1 zero_le_one (2 * t (Sum.inl i) - 1)) ∘ Sum.inl)
        (Function.update t (Sum.inl i)
          (Set.projIcc 0 1 zero_le_one (2 * t (Sum.inl i) - 1)) ∘ Sum.inr)
  split_ifs <;> simp only [Sum.update_inl_comp_inl, Sum.update_inl_comp_inr]

end GenLoop

namespace HomotopyGroup

variable {X : Type uX} [TopologicalSpace X]

/-- The computed loop-iteration equivalence preserves the given homotopy-group
multiplications. Only the outer cube index must be nonempty. -/
theorem genLoopEquiv_mul (N : Type uN) (M : Type uM)
    [DecidableEq N] [DecidableEq (N ⊕ M)] [Nonempty N] (x : X)
    (a b : HomotopyGroup N (GenLoop M X x) GenLoop.const) :
    genLoopEquiv N M x (a * b) = genLoopEquiv N M x a * genLoopEquiv N M x b := by
  refine Quotient.inductionOn₂
    (motive := fun a b : HomotopyGroup N (GenLoop M X x) GenLoop.const ↦
      genLoopEquiv N M x (a * b) = genLoopEquiv N M x a * genLoopEquiv N M x b)
    a b ?_
  intro p q
  let i : N := Classical.arbitrary N
  have hmulN := HomotopyGroup.mul_spec (N := N) (X := GenLoop M X x)
    (x := (GenLoop.const : GenLoop M X x)) (i := i) (p := p) (q := q)
  have hmulSum := HomotopyGroup.mul_spec (N := N ⊕ M) (X := X) (x := x)
    (i := Sum.inl i)
    (p := GenLoop.genLoopGenLoopEquiv x (M := N) (N := M) p)
    (q := GenLoop.genLoopGenLoopEquiv x (M := N) (N := M) q)
  have hright := congrArg₂ (fun a b : HomotopyGroup (N ⊕ M) X x => a * b)
    (genLoopEquiv_class N M x p) (genLoopEquiv_class N M x q)
  exact Eq.trans (α := HomotopyGroup (N ⊕ M) X x)
    (congrArg (genLoopEquiv N M x) hmulN)
    (Eq.trans (α := HomotopyGroup (N ⊕ M) X x) (genLoopEquiv_class N M x _)
      (Eq.trans (α := HomotopyGroup (N ⊕ M) X x)
        (congrArg (β := HomotopyGroup (N ⊕ M) X x)
          (fun r : GenLoop (N ⊕ M) X x => (⟦r⟧ : HomotopyGroup (N ⊕ M) X x))
          (GenLoop.genLoopGenLoopEquiv_transAt x i q p))
        (Eq.trans (α := HomotopyGroup (N ⊕ M) X x) hmulSum.symm hright.symm)))

/-- Loop iteration as a multiplicative equivalence for the existing source and
target homotopy-group structures, with the computed all-index equivalence as
its underlying equivalence. -/
def genLoopMulEquiv (N : Type uN) (M : Type uM)
    [DecidableEq N] [DecidableEq (N ⊕ M)] [Nonempty N] (x : X) :
    HomotopyGroup N (GenLoop M X x) GenLoop.const ≃* HomotopyGroup (N ⊕ M) X x where
  toEquiv := genLoopEquiv N M x
  map_mul' := genLoopEquiv_mul N M x

/-- Forgetting multiplication recovers the all-index loop-iteration equivalence. -/
theorem genLoopMulEquiv_toEquiv (N : Type uN) (M : Type uM)
    [DecidableEq N] [DecidableEq (N ⊕ M)] [Nonempty N] (x : X) :
    (genLoopMulEquiv N M x).toEquiv = genLoopEquiv N M x :=
  rfl

/-- The multiplicative refinement has the same value as the computed all-index
loop-iteration equivalence. -/
@[simp]
theorem genLoopMulEquiv_apply (N : Type uN) (M : Type uM)
    [DecidableEq N] [DecidableEq (N ⊕ M)] [Nonempty N] (x : X)
    (a : HomotopyGroup N (GenLoop M X x) GenLoop.const) :
    genLoopMulEquiv N M x a = genLoopEquiv N M x a :=
  rfl

end HomotopyGroup
