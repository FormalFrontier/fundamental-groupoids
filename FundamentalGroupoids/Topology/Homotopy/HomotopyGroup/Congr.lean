/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map
import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Coordinate equivalences on homotopy groups

`HomotopyGroup.congr` descends Mathlib's generalized-loop homeomorphism
`GenLoop.congr` to the boundary-relative homotopy quotient. The cube indices
have independent universes and may be empty or infinite. The equivalence
preserves representative classes and the constant class, respects identity and
composition, and commutes with based postcomposition.

For nonempty indices with decidable equality, `HomotopyGroup.congrMulEquiv`
uses the same equivalence with Mathlib's existing group structures. Its
multiplication convention is that of `HomotopyGroup.mul_spec`: the right
factor is concatenated before the left factor. No condition on the coordinates
selected in the construction of those group structures is imposed.

These are transports in the cubical boundary-relative model. No comparison
with sphere-domain homotopy classes is asserted.

## References

* Mathlib's generalized loops, coordinate homeomorphism, homotopy quotient and
  coordinate-independent group structures are due to Roberto Alvarez, using
  the Eckmann–Hilton argument.
* Mathlib's relative homotopies are due to Shing Tak Lam and contributors.
  The compact-open loop-space bridge `GenLoop.homotopic_iff_joined` in
  `FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace`
  identifies boundary-relative homotopies with paths. Transport of these paths
  along `GenLoop.congr` and its inverse, together with `Quotient.congr`,
  supplies descent to the quotient.
* Based postcomposition is provided by
  `FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Map`.
-/

@[expose] public section

noncomputable section

universe uN uM uL uX uY

namespace GenLoop

variable {N : Type uN} {M : Type uM} {X : Type uX} [TopologicalSpace X]

/-- Coordinate transport evaluates by precomposition with the index equivalence. -/
@[simp]
theorem congr_apply (x : X) (e : N ≃ M) (p : GenLoop N X x)
    (t : M → unitInterval) :
    GenLoop.congr x e p t = p (fun n => t (e n)) :=
  rfl

/-- Coordinate transport preserves the constant generalized loop. -/
@[simp]
theorem congr_const (x : X) (e : N ≃ M) :
    GenLoop.congr x e (GenLoop.const : GenLoop N X x) = GenLoop.const := by
  apply GenLoop.ext
  intro t
  rfl

/-- Coordinate transport commutes with concatenation along corresponding coordinates. -/
theorem congr_transAt [DecidableEq N] [DecidableEq M]
    (x : X) (e : N ≃ M) (i : N) (p q : GenLoop N X x) :
    GenLoop.congr x e (GenLoop.transAt i p q) =
      GenLoop.transAt (e i) (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  apply GenLoop.ext
  intro t
  have hupdate (s : unitInterval) :
      Function.update (fun j => t (e j)) i s =
        (fun j => Function.update t (e i) s (e j)) := by
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using
      (Function.update_comp_equiv t e (e i) s).symm
  simp only [congr_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs
  · exact congrArg p (hupdate _)
  · exact congrArg q (hupdate _)

end GenLoop

namespace HomotopyGroup

variable {N : Type uN} {M : Type uM} {L : Type uL} {X : Type uX}
variable [TopologicalSpace X]

private theorem homotopic_congr_iff (x : X) (e : N ≃ M)
    (p q : GenLoop N X x) :
    GenLoop.Homotopic p q ↔
      GenLoop.Homotopic (GenLoop.congr x e p) (GenLoop.congr x e q) := by
  simp only [GenLoop.homotopic_iff_joined]
  constructor
  · intro h
    exact h.map (GenLoop.congr x e).continuous
  · intro h
    simpa only [Homeomorph.symm_apply_apply] using
      h.map (GenLoop.congr x e).symm.continuous

/-- An equivalence of cube indices induces an equivalence on the existing
boundary-relative homotopy quotients, using `GenLoop.congr` on representatives. -/
def congr (x : X) (e : N ≃ M) :
    HomotopyGroup N X x ≃ HomotopyGroup M X x :=
  Quotient.congr
    (ra := GenLoop.Homotopic.setoid N x)
    (rb := GenLoop.Homotopic.setoid M x)
    (GenLoop.congr x e).toEquiv
    (fun p q => by exact homotopic_congr_iff x e p q)

/-- Coordinate transport sends a representative class to its reindexed class. -/
@[simp]
theorem congr_class (x : X) (e : N ≃ M) (p : GenLoop N X x) :
    congr x e (⟦p⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.congr x e p⟧ : HomotopyGroup M X x) :=
  rfl

/-- Inverse coordinate transport is transport along the inverse index equivalence. -/
@[simp]
theorem congr_symm (x : X) (e : N ≃ M) :
    (congr x e).symm = congr x e.symm := by
  apply Equiv.ext
  intro a
  refine Quotient.inductionOn a ?_
  intro p
  rfl

/-- Coordinate transport preserves the constant class, including at empty indices. -/
theorem congr_const (x : X) (e : N ≃ M) :
    congr x e (⟦GenLoop.const⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.const⟧ : HomotopyGroup M X x) := by
  rw [congr_class, GenLoop.congr_const]

/-- The identity index equivalence induces the identity on homotopy classes. -/
@[simp]
theorem congr_refl (x : X) :
    congr x (Equiv.refl N) = Equiv.refl (HomotopyGroup N X x) := by
  apply Equiv.ext
  intro a
  refine Quotient.inductionOn a ?_
  intro p
  have hp : GenLoop.congr x (Equiv.refl N) p = p := by
    apply GenLoop.ext
    intro t
    rfl
  exact (congr_class x (Equiv.refl N) p).trans
    (congrArg (fun q : GenLoop N X x => (⟦q⟧ : HomotopyGroup N X x)) hp)

/-- Coordinate transport respects composition of index equivalences. -/
theorem congr_trans (x : X) (e : N ≃ M) (d : M ≃ L) :
    congr x (e.trans d) = (congr x e).trans (congr x d) := by
  apply Equiv.ext
  intro a
  refine Quotient.inductionOn a ?_
  intro p
  have hp : GenLoop.congr x (e.trans d) p =
      GenLoop.congr x d (GenLoop.congr x e p) := by
    apply GenLoop.ext
    intro t
    rfl
  change congr x (e.trans d) (⟦p⟧ : HomotopyGroup N X x) =
    congr x d (congr x e (⟦p⟧ : HomotopyGroup N X x))
  exact (congr_class x (e.trans d) p).trans
    ((congrArg (β := HomotopyGroup L X x)
      (fun q : GenLoop L X x => (⟦q⟧ : HomotopyGroup L X x)) hp).trans
      (by rw [congr_class, congr_class]))

/-- Coordinate transport commutes with based postcomposition for every cube index. -/
theorem congr_mapFun {Y : Type uY} [TopologicalSpace Y] {x : X} {y : Y}
    (e : N ≃ M) (f : C(X, Y)) (hf : f x = y) (a : HomotopyGroup N X x) :
    congr y e (mapFun N f hf a) = mapFun M f hf (congr x e a) := by
  refine Quotient.inductionOn a ?_
  intro p
  have hp : GenLoop.congr y e (GenLoop.map f hf p) =
      GenLoop.map f hf (GenLoop.congr x e p) := by
    apply GenLoop.ext
    intro t
    rfl
  have hmap : congr y e (mapFun N f hf (⟦p⟧ : HomotopyGroup N X x)) =
      (⟦GenLoop.congr y e (GenLoop.map f hf p)⟧ : HomotopyGroup M Y y) := by
    rw [mapFun_class, congr_class]
  exact hmap.trans
    ((congrArg (β := HomotopyGroup M Y y)
      (fun q : GenLoop M Y y => (⟦q⟧ : HomotopyGroup M Y y)) hp).trans
      (by rw [congr_class, mapFun_class]))

section Group

variable [DecidableEq N] [Nonempty N] [DecidableEq M] [Nonempty M]

/-- Coordinate transport as a multiplicative equivalence, with the existing
source and target homotopy-group structures. -/
def congrMulEquiv (x : X) (e : N ≃ M) :
    HomotopyGroup N X x ≃* HomotopyGroup M X x where
  toEquiv := congr x e
  map_mul' a b := by
    refine Quotient.inductionOn₂
      (motive := fun a b : HomotopyGroup N X x ↦
        congr x e (a * b) = congr x e a * congr x e b) a b ?_
    intro p q
    let i : N := Classical.arbitrary N
    have hmulN := HomotopyGroup.mul_spec (N := N) (X := X) (x := x)
      (i := i) (p := p) (q := q)
    have hmulM := HomotopyGroup.mul_spec (N := M) (X := X) (x := x)
      (i := e i) (p := GenLoop.congr x e p) (q := GenLoop.congr x e q)
    have hright := congrArg₂ (fun a b : HomotopyGroup M X x => a * b)
      (congr_class x e p) (congr_class x e q)
    exact Eq.trans (α := HomotopyGroup M X x) (congrArg (congr x e) hmulN)
      (Eq.trans (α := HomotopyGroup M X x) (congr_class x e _)
        (Eq.trans (α := HomotopyGroup M X x)
          (congrArg (β := HomotopyGroup M X x)
            (fun r : GenLoop M X x => (⟦r⟧ : HomotopyGroup M X x))
            (GenLoop.congr_transAt x e i q p))
          (Eq.trans (α := HomotopyGroup M X x) hmulM.symm hright.symm)))

/-- Forgetting multiplication recovers the all-index coordinate equivalence. -/
theorem congrMulEquiv_toEquiv (x : X) (e : N ≃ M) :
    (congrMulEquiv x e).toEquiv = congr x e :=
  rfl

/-- The multiplicative and all-index transports have the same underlying function. -/
@[simp]
theorem congrMulEquiv_apply (x : X) (e : N ≃ M) (a : HomotopyGroup N X x) :
    congrMulEquiv x e a = congr x e a :=
  rfl

/-- Multiplicative coordinate transport commutes with the existing based homomorphisms. -/
theorem congrMulEquiv_map {Y : Type uY} [TopologicalSpace Y] {x : X} {y : Y}
    (e : N ≃ M) (f : C(X, Y)) (hf : f x = y) (a : HomotopyGroup N X x) :
    congrMulEquiv y e (map N f hf a) = map M f hf (congrMulEquiv x e a) := by
  simpa only [congrMulEquiv_apply, coe_map_eq_mapFun] using
    (congr_mapFun e f hf a)

end Group

end HomotopyGroup
