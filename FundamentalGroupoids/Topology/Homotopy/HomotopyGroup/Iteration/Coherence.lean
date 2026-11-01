/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Iteration.Basic

/-!
# Associativity and empty units for generalized-loop iteration

`HomotopyGroup.genLoopEquiv_assoc` compares the two orders of flattening three
levels of generalized loops, using the ordered sum associator. The empty-index
unit laws retain every component of the inner loop space on the left and use
empty-loop evaluation on the right. All statements concern the existing
homotopy quotients, without a nonemptiness or group-structure assumption.

## References

Mathlib's generalized loops, sum-flattening homeomorphism and empty-index
comparisons are due to Roberto Alvarez. The proofs use the representative API
of `HomotopyGroup.genLoopEquiv`, the same-loop component comparison, based
postcomposition and coordinate transport.
-/

@[expose] public section

noncomputable section

universe uN uM uX uA uB uC uE

namespace HomotopyGroup

/-- Flattening three levels of generalized loops is associative, with the
outer-to-inner coordinate order preserved by the sum associator. -/
theorem genLoopEquiv_assoc (A : Type uA) (B : Type uB) (C : Type uC)
    {X : Type uX} [TopologicalSpace X] (x : X)
    (a : HomotopyGroup A
      (GenLoop B (GenLoop C X x) GenLoop.const) GenLoop.const) :
    congr x (Equiv.sumAssoc A B C)
        (genLoopEquiv (A ⊕ B) C x
          (genLoopEquiv A B (GenLoop.const : GenLoop C X x) a)) =
      genLoopEquiv A (B ⊕ C) x
        (mapFun A
          (_root_.toContinuousMap
            (GenLoop.genLoopGenLoopEquiv x (M := B) (N := C)))
          (by
            apply GenLoop.ext
            intro t
            rfl) a) := by
  refine Quotient.inductionOn a ?_
  intro p
  simp only [genLoopEquiv_class, congr_class, mapFun_class]
  apply congrArg (fun q : GenLoop (A ⊕ (B ⊕ C)) X x ↦
    (⟦q⟧ : HomotopyGroup (A ⊕ (B ⊕ C)) X x))
  apply GenLoop.ext
  intro t
  rfl

/-- An empty outer index removes the outer cube through the components of the
entire inner loop space, not just the component of the constant loop. -/
theorem genLoopEquiv_empty_left (E : Type uE) (M : Type uM)
    {X : Type uX} [IsEmpty E] [TopologicalSpace X] (x : X)
    (a : HomotopyGroup E (GenLoop M X x) GenLoop.const) :
    congr x (Equiv.emptySum E M) (genLoopEquiv E M x a) =
      (equivZerothHomotopy M x).symm
        (homotopyGroupEquivZerothHomotopyOfIsEmpty E
          (GenLoop.const : GenLoop M X x) a) := by
  refine Quotient.inductionOn a ?_
  intro p
  have hcomponent :
      homotopyGroupEquivZerothHomotopyOfIsEmpty E
          (GenLoop.const : GenLoop M X x)
          (⟦p⟧ : HomotopyGroup E (GenLoop M X x) GenLoop.const) =
        ZerothHomotopy.mk (p 0) := rfl
  simp only [genLoopEquiv_class, congr_class, hcomponent,
    equivZerothHomotopy_symm_mk]
  apply congrArg (fun q : GenLoop M X x ↦ (⟦q⟧ : HomotopyGroup M X x))
  apply GenLoop.ext
  intro t
  exact congrArg (fun s : E → unitInterval ↦ p s t) (Subsingleton.elim _ _)

/-- An empty inner index is removed by based postcomposition with the existing
empty-loop evaluation homeomorphism. -/
theorem genLoopEquiv_empty_right (N : Type uN) (E : Type uE)
    {X : Type uX} [IsEmpty E] [TopologicalSpace X] (x : X)
    (a : HomotopyGroup N (GenLoop E X x) GenLoop.const) :
    congr x (Equiv.sumEmpty N E) (genLoopEquiv N E x a) =
      mapFun N
        (_root_.toContinuousMap (genLoopHomeoOfIsEmpty E x)) (by rfl) a := by
  refine Quotient.inductionOn a ?_
  intro p
  simp only [genLoopEquiv_class, congr_class, mapFun_class]
  apply congrArg (fun q : GenLoop N X x ↦ (⟦q⟧ : HomotopyGroup N X x))
  apply GenLoop.ext
  intro t
  exact congrArg (p t) (Subsingleton.elim _ _)

end HomotopyGroup
