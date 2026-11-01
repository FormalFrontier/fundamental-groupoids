/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Iteration.Group
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Iteration.Coherence

/-!
# Ordered finite loop iteration

The finite comparison `HomotopyGroup.genLoopFinEquiv` orders the outer
coordinates before the inner coordinates. Its representative formula uses
`Fin.castAdd` for the outer block and `Fin.natAdd` for the inner block.
Associativity and units use the forward coordinate casts associated to
`Nat.add_assoc`, `Nat.zero_add` and `Nat.add_zero`. These laws hold in every
degree, including all zero-degree cases and all their components.

For positive outer degree, `HomotopyGroup.genLoopFinMulEquiv` equips the same
comparison with multiplication preservation for the existing homotopy-group
structures. The inner degree may be zero.

## References

Mathlib's generalized loops, sum-flattening homeomorphism and homotopy-group
operations are due to Roberto Alvarez. The component comparison, based
postcomposition and coordinate transport are provided by `HomotopyGroup.LoopSpace`,
`HomotopyGroup.Map` and `HomotopyGroup.Congr`. The finite coordinate equivalences
and casts are Mathlib's `finSumFinEquiv` and `finCongr`.
-/

@[expose] public section

noncomputable section

universe uX

namespace GenLoop

/-- Ordered finite flattening evaluates first on the outer `Fin.castAdd` block,
then on the inner `Fin.natAdd` block. -/
theorem genLoopGenLoopEquiv_fin_apply (n m : ℕ) {X : Type uX}
    [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin n) (GenLoop (Fin m) X x) GenLoop.const)
    (t : Fin (n + m) → unitInterval) :
    GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))
        (GenLoop.genLoopGenLoopEquiv x (M := Fin n) (N := Fin m) p) t =
      p (fun i => t (Fin.castAdd m i)) (fun j => t (Fin.natAdd n j)) :=
  rfl

end GenLoop

namespace HomotopyGroup

/-- The finite comparison sends a representative to its ordered, reindexed
flattening, including when either degree is zero. -/
@[simp]
theorem genLoopFinEquiv_class (n m : ℕ) {X : Type uX}
    [TopologicalSpace X] (x : X)
    (p : GenLoop (Fin n) (GenLoop (Fin m) X x) GenLoop.const) :
    genLoopFinEquiv n m x
        (⟦p⟧ : HomotopyGroup (Fin n) (GenLoop (Fin m) X x) GenLoop.const) =
      (⟦GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))
        (GenLoop.genLoopGenLoopEquiv x (M := Fin n) (N := Fin m) p)⟧ :
        HomotopyGroup (Fin (n + m)) X x) := by
  change congr x (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))
    (genLoopEquiv (Fin n) (Fin m) x ⟦p⟧) = _
  rw [genLoopEquiv_class, congr_class]

/-- Ordered finite flattening is associative after the forward cast induced by
`Nat.add_assoc`. No positivity assumption is required. -/
theorem genLoopFinEquiv_assoc (n m k : ℕ) {X : Type uX}
    [TopologicalSpace X] (x : X)
    (a : HomotopyGroup (Fin n)
      (GenLoop (Fin m) (GenLoop (Fin k) X x) GenLoop.const) GenLoop.const) :
    congr x (finCongr (Nat.add_assoc n m k))
        (genLoopFinEquiv (n + m) k x
          (genLoopFinEquiv n m (GenLoop.const : GenLoop (Fin k) X x) a)) =
      genLoopFinEquiv n (m + k) x
        (mapFun (Fin n)
          (_root_.toContinuousMap
            ((GenLoop.genLoopGenLoopEquiv x (M := Fin m) (N := Fin k)).trans
              (GenLoop.congr x
                (finSumFinEquiv : Fin m ⊕ Fin k ≃ Fin (m + k)))))
          (by
            apply GenLoop.ext
            intro t
            rfl) a) := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [genLoopFinEquiv_class n m (GenLoop.const : GenLoop (Fin k) X x) p,
    genLoopFinEquiv_class (n + m) k x, congr_class, mapFun_class,
    genLoopFinEquiv_class]
  apply congrArg (fun q : GenLoop (Fin (n + (m + k))) X x =>
    (⟦q⟧ : HomotopyGroup (Fin (n + (m + k))) X x))
  apply GenLoop.ext
  intro t
  have hn (i : Fin n) :
      finCongr (Nat.add_assoc n m k) (Fin.castAdd k (Fin.castAdd m i)) =
        Fin.castAdd (m + k) i := by
    apply Fin.ext
    rfl
  have hm (j : Fin m) :
      finCongr (Nat.add_assoc n m k) (Fin.castAdd k (Fin.natAdd n j)) =
        Fin.natAdd n (Fin.castAdd k j) := by
    apply Fin.ext
    rfl
  have hk (l : Fin k) :
      finCongr (Nat.add_assoc n m k) (Fin.natAdd (n + m) l) =
        Fin.natAdd n (Fin.natAdd m l) := by
    apply Fin.ext
    exact Nat.add_assoc n m l.val
  change p
      (fun i => t (finCongr (Nat.add_assoc n m k) (Fin.castAdd k (Fin.castAdd m i))))
      (fun j => t (finCongr (Nat.add_assoc n m k) (Fin.castAdd k (Fin.natAdd n j))))
      (fun l => t (finCongr (Nat.add_assoc n m k) (Fin.natAdd (n + m) l))) =
    p (fun i => t (Fin.castAdd (m + k) i))
      (fun j => t (Fin.natAdd n (Fin.castAdd k j)))
      (fun l => t (Fin.natAdd n (Fin.natAdd m l)))
  simp only [hn, hm, hk]

/-- The left zero-degree unit retains every component of the inner loop space,
using the forward cast induced by `Nat.zero_add`. -/
theorem genLoopFinEquiv_zero_left (m : ℕ) {X : Type uX}
    [TopologicalSpace X] (x : X)
    (a : HomotopyGroup (Fin 0) (GenLoop (Fin m) X x) GenLoop.const) :
    congr x (finCongr (Nat.zero_add m)) (genLoopFinEquiv 0 m x a) =
      (equivZerothHomotopy (Fin m) x).symm
        (homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0)
          (GenLoop.const : GenLoop (Fin m) X x) a) := by
  have he :
      (finSumFinEquiv : Fin 0 ⊕ Fin m ≃ Fin (0 + m)).trans
          (finCongr (Nat.zero_add m)) = Equiv.emptySum (Fin 0) (Fin m) := by
    apply Equiv.ext
    intro i
    rcases i with i | j
    · exact Fin.elim0 i
    · apply Fin.ext
      exact Nat.zero_add j.val
  change ((congr x (finSumFinEquiv : Fin 0 ⊕ Fin m ≃ Fin (0 + m))).trans
    (congr x (finCongr (Nat.zero_add m)))) (genLoopEquiv (Fin 0) (Fin m) x a) = _
  rw [← congr_trans, he]
  exact genLoopEquiv_empty_left (Fin 0) (Fin m) x a

/-- The right zero-degree unit evaluates the empty inner loop, using the forward
cast induced by `Nat.add_zero`. -/
theorem genLoopFinEquiv_zero_right (n : ℕ) {X : Type uX}
    [TopologicalSpace X] (x : X)
    (a : HomotopyGroup (Fin n) (GenLoop (Fin 0) X x) GenLoop.const) :
    congr x (finCongr (Nat.add_zero n)) (genLoopFinEquiv n 0 x a) =
      mapFun (Fin n)
        (_root_.toContinuousMap (genLoopHomeoOfIsEmpty (Fin 0) x)) (by rfl) a := by
  have he :
      (finSumFinEquiv : Fin n ⊕ Fin 0 ≃ Fin (n + 0)).trans
          (finCongr (Nat.add_zero n)) = Equiv.sumEmpty (Fin n) (Fin 0) := by
    apply Equiv.ext
    intro i
    rcases i with j | i
    · apply Fin.ext
      rfl
    · exact Fin.elim0 i
  change ((congr x (finSumFinEquiv : Fin n ⊕ Fin 0 ≃ Fin (n + 0))).trans
    (congr x (finCongr (Nat.add_zero n)))) (genLoopEquiv (Fin n) (Fin 0) x a) = _
  rw [← congr_trans, he]
  exact genLoopEquiv_empty_right (Fin n) (Fin 0) x a

section Group

variable (n m : ℕ) [NeZero n]

local instance : NeZero (n + m) :=
  ⟨Nat.ne_of_gt (Nat.lt_of_lt_of_le (NeZero.pos n) (Nat.le_add_right n m))⟩

/-- Ordered finite loop iteration as a multiplicative equivalence for the
existing groups, assuming only that the outer degree is positive. -/
def genLoopFinMulEquiv {X : Type uX} [TopologicalSpace X] (x : X) :
    HomotopyGroup (Fin n) (GenLoop (Fin m) X x) GenLoop.const ≃*
      HomotopyGroup (Fin (n + m)) X x :=
  (genLoopMulEquiv (Fin n) (Fin m) x).trans
    (congrMulEquiv x (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)))

/-- Forgetting multiplication recovers the all-degree finite comparison. -/
theorem genLoopFinMulEquiv_toEquiv {X : Type uX} [TopologicalSpace X] (x : X) :
    (genLoopFinMulEquiv n m x).toEquiv = genLoopFinEquiv n m x := by
  change ((genLoopMulEquiv (Fin n) (Fin m) x).toEquiv).trans
    (congrMulEquiv x (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))).toEquiv = _
  rw [genLoopMulEquiv_toEquiv, congrMulEquiv_toEquiv]
  rfl

/-- The multiplicative finite comparison has the same function as the
all-degree comparison. -/
@[simp]
theorem genLoopFinMulEquiv_apply {X : Type uX} [TopologicalSpace X] (x : X)
    (a : HomotopyGroup (Fin n) (GenLoop (Fin m) X x) GenLoop.const) :
    genLoopFinMulEquiv n m x a = genLoopFinEquiv n m x a :=
  congrArg (fun e :
    HomotopyGroup (Fin n) (GenLoop (Fin m) X x) GenLoop.const ≃
      HomotopyGroup (Fin (n + m)) X x => e a)
    (genLoopFinMulEquiv_toEquiv n m x)

end Group

end HomotopyGroup
