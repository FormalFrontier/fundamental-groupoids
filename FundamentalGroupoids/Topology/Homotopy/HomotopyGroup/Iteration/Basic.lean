/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Congr
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum

/-!
# Iteration of generalized homotopy groups

Sum-indexed loop iteration is expressed using the path-component comparison and
the sum-flattening homeomorphism. The finite specialization preserves the order
of the outer coordinates followed by the inner coordinates. Both comparisons
are defined for arbitrary indices, including empty indices.

`HomotopyGroup.genLoopEquiv_class` and
`HomotopyGroup.genLoopEquiv_symm_class` compute the comparison on representative
classes using the sum-flattening homeomorphism and its inverse. The comparison
preserves the constant class and commutes with based postcomposition. The two
cube indices and the source and target spaces have independent universes.

## References

Mathlib's generalized loops and sum-flattening homeomorphism are due to Roberto
Alvarez. The path-component comparison and reindexing APIs are provided by
`HomotopyGroup.LoopSpace` and `HomotopyGroup.Congr`.
-/

@[expose] public section

noncomputable section

universe uN uM uX uY uA uB uC uE

namespace HomotopyGroup

/-- Flatten an outer `N`-cube of `M`-loops by the existing component
comparisons and sum-flattening homeomorphism, in outer-then-inner order. -/
def genLoopEquiv (N : Type uN) (M : Type uM) {X : Type uX}
    [TopologicalSpace X] (x : X) :
    HomotopyGroup N (GenLoop M X x) (GenLoop.const : GenLoop M X x) ≃
      HomotopyGroup (N ⊕ M) X x :=
  ((equivZerothHomotopy N (GenLoop.const : GenLoop M X x)).trans
    (ZerothHomotopy.equivOfHomotopyEquiv
      (GenLoop.genLoopGenLoopEquiv x (M := N) (N := M)).toHomotopyEquiv)).trans
    (equivZerothHomotopy (N ⊕ M) x).symm

/-- Loop iteration sends a representative class to the class of its
sum-flattened generalized loop, in outer-then-inner coordinate order. -/
@[simp]
theorem genLoopEquiv_class (N : Type uN) (M : Type uM) {X : Type uX}
    [TopologicalSpace X] (x : X)
    (p : GenLoop N (GenLoop M X x) GenLoop.const) :
    genLoopEquiv N M x
        (⟦p⟧ : HomotopyGroup N (GenLoop M X x) GenLoop.const) =
      (⟦GenLoop.genLoopGenLoopEquiv x (M := N) (N := M) p⟧ :
        HomotopyGroup (N ⊕ M) X x) := by
  change (equivZerothHomotopy (N ⊕ M) x).symm
      (ZerothHomotopy.equivOfHomotopyEquiv
        (GenLoop.genLoopGenLoopEquiv x (M := N) (N := M)).toHomotopyEquiv
        (equivZerothHomotopy N (GenLoop.const : GenLoop M X x) ⟦p⟧)) = _
  rw [equivZerothHomotopy_class, ZerothHomotopy.equivOfHomotopyEquiv_mk]
  exact equivZerothHomotopy_symm_mk (N ⊕ M) x
    (GenLoop.genLoopGenLoopEquiv x (M := N) (N := M) p)

/-- Inverse loop iteration sends a representative class to the class of the
corresponding cube of generalized loops. -/
@[simp]
theorem genLoopEquiv_symm_class (N : Type uN) (M : Type uM) {X : Type uX}
    [TopologicalSpace X] (x : X) (q : GenLoop (N ⊕ M) X x) :
    (genLoopEquiv N M x).symm (⟦q⟧ : HomotopyGroup (N ⊕ M) X x) =
      (⟦(GenLoop.genLoopGenLoopEquiv x (M := N) (N := M)).symm q⟧ :
        HomotopyGroup N (GenLoop M X x) GenLoop.const) := by
  apply (genLoopEquiv N M x).symm_apply_eq.mpr
  rw [genLoopEquiv_class, Homeomorph.apply_symm_apply]

/-- Loop iteration preserves the constant class without requiring a group
structure or nonempty cube indices. -/
theorem genLoopEquiv_const (N : Type uN) (M : Type uM) {X : Type uX}
    [TopologicalSpace X] (x : X) :
    genLoopEquiv N M x
        (⟦GenLoop.const⟧ : HomotopyGroup N (GenLoop M X x) GenLoop.const) =
      (⟦GenLoop.const⟧ : HomotopyGroup (N ⊕ M) X x) := by
  rw [genLoopEquiv_class]
  apply congrArg (fun q : GenLoop (N ⊕ M) X x ↦
    (⟦q⟧ : HomotopyGroup (N ⊕ M) X x))
  apply GenLoop.ext
  intro t
  rfl

/-- Loop iteration commutes with based postcomposition for arbitrary cube
indices, using the same continuous map on the inner generalized-loop space. -/
theorem genLoopEquiv_mapFun (N : Type uN) (M : Type uM) {X : Type uX}
    {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup N (GenLoop M X x) GenLoop.const) :
    genLoopEquiv N M y
        (mapFun N
          (⟨GenLoop.map f hf, GenLoop.continuous_map f hf⟩ :
            C(GenLoop M X x, GenLoop M Y y))
          (GenLoop.map_const (N := M) f hf) a) =
      mapFun (N ⊕ M) f hf (genLoopEquiv N M x a) := by
  refine Quotient.inductionOn a ?_
  intro p
  simp only [mapFun_class, genLoopEquiv_class]
  apply congrArg (fun q : GenLoop (N ⊕ M) Y y ↦
    (⟦q⟧ : HomotopyGroup (N ⊕ M) Y y))
  apply GenLoop.ext
  intro t
  rfl

/-- Ordered finite loop iteration: the first `n` coordinates are outer
coordinates and the last `m` coordinates are inner coordinates. -/
def genLoopFinEquiv (n m : ℕ) {X : Type uX} [TopologicalSpace X] (x : X) :
    HomotopyGroup (Fin n) (GenLoop (Fin m) X x) GenLoop.const ≃
      HomotopyGroup (Fin (n + m)) X x :=
  (genLoopEquiv (Fin n) (Fin m) x).trans
    (congr x (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)))

end HomotopyGroup
