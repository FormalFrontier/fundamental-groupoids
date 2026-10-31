/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Based maps on homotopy groups

A continuous map preserving supplied points acts by postcomposition on Mathlib's
`GenLoop` and `HomotopyGroup`. The cube index and all space universes are independent.

* `GenLoop.map` preserves constant loops, identity, composition and homotopies
  relative to the cube boundary; with decidable equality on the cube index it
  also preserves concatenation.
* `HomotopyGroup.mapFun` acts on the homotopy quotient for every cube-index type,
  including an empty type, without decidable equality or a group structure.
* `HomotopyGroup.map` is a homomorphism for a nonempty index type with decidable
  equality. Its underlying function is `mapFun`, with Mathlib's canonical group
  structures and reversed concatenation convention.
* Homotopies fixed at the supplied source point induce equal quotient maps and
  equal homomorphisms. In dimension one the homomorphism agrees with
  `FundamentalGroup.mapOfEq` through `pi1MulEquivFundamentalGroup`.

No separation, connectedness, local path connectedness, finiteness or
well-pointedness assumption is imposed. These constructions use Mathlib's existing
generalized loops, homotopy relation, quotient and positive group structures.

## References

The based-postcomposition definitions and proofs originate in
[Restricted Product Duality](https://github.com/FormalFrontier/restricted-product-duality)
by Formal Frontier Agents, with their Apache-2.0 and authorship notices retained.
They reuse Mathlib's generalized loops and homotopy groups (Roberto Alvarez),
fundamental groups (Mark Lavrentyev and contributors), relative and path homotopies
(Shing Tak Lam and contributors), and quotient maps. The based-postcomposition
packaging in `GenLoop` and `HomotopyGroup` is a candidate for upstream inclusion
in Mathlib.
-/

@[expose] public section

noncomputable section

open Filter Set

universe u v w z s

namespace GenLoop

variable {N : Type s} {X : Type v} {Y : Type w} {Z : Type z}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- Postcompose a based cube map by a continuous map preserving its chosen point. -/
def map (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x) : GenLoop N Y y :=
  ⟨f.comp p.1, fun t ht ↦ (congrArg f (GenLoop.boundary p t ht)).trans hf⟩

/-- Evaluation of based postcomposition. -/
@[simp]
theorem map_apply (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x)
    (t : N → unitInterval) : map f hf p t = f (p t) :=
  rfl

/-- Based postcomposition is continuous for the inherited compact-open topologies. -/
@[fun_prop]
theorem continuous_map (f : C(X, Y)) (hf : f x = y) :
    Continuous (map f hf : GenLoop N X x → GenLoop N Y y) :=
  ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _

/-- The constant loop maps to the constant loop at the target point. -/
@[simp]
theorem map_const (f : C(X, Y)) (hf : f x = y) :
    map f hf (GenLoop.const : GenLoop N X x) = GenLoop.const := by
  apply GenLoop.ext
  intro t
  exact hf

/-- Based postcomposition by the identity fixes every loop. -/
@[simp]
theorem map_id (p : GenLoop N X x) :
    map (ContinuousMap.id X) rfl p = p := by
  apply GenLoop.ext
  intro t
  rfl

/-- Based postcomposition respects composition. -/
theorem map_comp (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop N X x) :
    map (g.comp f) ((congrArg g hf).trans hg) p =
      map g hg (map f hf p) := by
  apply GenLoop.ext
  intro t
  rfl

/-- Postcomposition commutes with concatenation in any cube direction. -/
theorem map_transAt [DecidableEq N] (f : C(X, Y)) (hf : f x = y)
    (j : N) (p q : GenLoop N X x) :
    map f hf (GenLoop.transAt j p q) =
      GenLoop.transAt j (map f hf p) (map f hf q) := by
  apply GenLoop.ext
  intro t
  change f (if (t j : ℝ) ≤ 1 / 2
      then p (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j)))
      else q (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j - 1)))) =
    if (t j : ℝ) ≤ 1 / 2
      then f (p (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j))))
      else f (q (Function.update t j (Set.projIcc 0 1 zero_le_one (2 * t j - 1))))
  split_ifs <;> rfl

/-- Based postcomposition preserves homotopies relative to the cube boundary. -/
theorem Homotopic.map (f : C(X, Y)) (hf : f x = y) {p q : GenLoop N X x}
    (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (GenLoop.map f hf p) (GenLoop.map f hf q) := by
  change p.1.HomotopicRel q.1 (Cube.boundary N) at h
  change (f.comp p.1).HomotopicRel (f.comp q.1) (Cube.boundary N)
  exact h.comp_continuousMap f

/-- A homotopy fixed at the source point gives homotopic postcompositions of any
based cube map, without a positivity assumption on its index type. -/
theorem map_homotopic (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (H : ContinuousMap.HomotopyRel f g ({x} : Set X)) (p : GenLoop N X x) :
    GenLoop.Homotopic (map f hf p) (map g hg p) := by
  change (f.comp p.1).HomotopicRel (g.comp p.1) (Cube.boundary N)
  refine ⟨{ H.toHomotopy.compContinuousMap p.1 with prop' := ?_ }⟩
  intro t a ha
  change H (t, p a) = f (p a)
  rw [GenLoop.boundary p a ha]
  exact H.eq_fst t (Set.mem_singleton_iff.mpr rfl)

end GenLoop

namespace HomotopyGroup

variable {X : Type v} {Y : Type w} {Z : Type z}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {x : X} {y : Y} {z : Z}

/-- Based postcomposition on the generalized-loop homotopy quotient for any
cube-index type, including an empty type. No group structure is required. -/
def mapFun (N : Type s) (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  @Quotient.map (GenLoop N X x) (GenLoop N Y y)
    (GenLoop.Homotopic.setoid N x) (GenLoop.Homotopic.setoid N y)
    (GenLoop.map f hf) (by
      intro p q h
      change GenLoop.Homotopic p q at h
      change GenLoop.Homotopic (GenLoop.map f hf p) (GenLoop.map f hf q)
      exact GenLoop.Homotopic.map f hf h)

/-- Compute based postcomposition on a representative class. -/
@[simp]
theorem mapFun_class (N : Type s) (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop N X x) :
    mapFun N f hf (⟦p⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.map f hf p⟧ : HomotopyGroup N Y y) :=
  rfl

/-- The chosen constant class maps to the chosen constant class. -/
theorem mapFun_const (N : Type s) (f : C(X, Y)) (hf : f x = y) :
    mapFun N f hf (⟦GenLoop.const⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.const⟧ : HomotopyGroup N Y y) := by
  rw [mapFun_class, GenLoop.map_const]

/-- The identity acts as the identity on the homotopy quotient in every dimension. -/
@[simp]
theorem mapFun_id (N : Type s) :
    mapFun N (ContinuousMap.id X) (x := x) rfl = id := by
  funext a
  change mapFun N (ContinuousMap.id X) rfl a = a
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦ mapFun N (ContinuousMap.id X) rfl a = a)
    a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N X x)
    (mapFun_class N (ContinuousMap.id X) rfl p)
    (congrArg (fun r : GenLoop N X x ↦ (⟦r⟧ : HomotopyGroup N X x))
      (GenLoop.map_id p))

/-- Based postcomposition on the homotopy quotient respects composition. -/
theorem mapFun_comp (N : Type s) (g : C(Y, Z)) (hg : g y = z)
    (f : C(X, Y)) (hf : f x = y) :
    mapFun N (g.comp f) ((congrArg g hf).trans hg) =
      (mapFun N g hg) ∘ (mapFun N f hf) := by
  funext a
  change mapFun N (g.comp f) ((congrArg g hf).trans hg) a =
    mapFun N g hg (mapFun N f hf a)
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦
      mapFun N (g.comp f) ((congrArg g hf).trans hg) a =
        mapFun N g hg (mapFun N f hf a)) a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N Z z)
    (mapFun_class N (g.comp f) ((congrArg g hf).trans hg) p)
    (Eq.trans (α := HomotopyGroup N Z z)
      (congrArg (fun r : GenLoop N Z z ↦ (⟦r⟧ : HomotopyGroup N Z z))
        (GenLoop.map_comp g hg f hf p))
      (Eq.trans (α := HomotopyGroup N Z z)
        (mapFun_class N g hg (GenLoop.map f hf p)).symm
        (congrArg (mapFun N g hg) (mapFun_class N f hf p).symm)))

/-- Maps homotopic relative to the chosen source point act identically on the
homotopy quotient, without a positivity assumption on the cube index. -/
theorem mapFun_eq_of_homotopyRel (N : Type s) (f g : C(X, Y))
    (hf : f x = y) (hg : g x = y)
    (H : ContinuousMap.HomotopyRel f g ({x} : Set X)) :
    mapFun N f hf = mapFun N g hg := by
  funext a
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦ mapFun N f hf a = mapFun N g hg a) a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N Y y)
    (mapFun_class N f hf p)
    (Eq.trans (α := HomotopyGroup N Y y)
      (Quotient.sound (GenLoop.map_homotopic f g hf hg H p))
      (mapFun_class N g hg p).symm)

/-- Based postcomposition on the stock quotient, with its canonical positive group
structure. Multiplication uses the stock reversed concatenation convention. -/
def map (N : Type s) [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y :=
  -- Retain the homotopy-group carriers when using the underlying quotient API.
  let classMap : HomotopyGroup N X x → HomotopyGroup N Y y := mapFun N f hf
  { toFun := classMap
    map_one' := by
      have hclass :
          classMap (⟦GenLoop.const⟧ : HomotopyGroup N X x) =
            (⟦GenLoop.map f hf GenLoop.const⟧ : HomotopyGroup N Y y) := rfl
      exact Eq.trans (α := HomotopyGroup N Y y)
        (congrArg classMap (HomotopyGroup.one_def (N := N) (X := X) (x := x)))
        (Eq.trans (α := HomotopyGroup N Y y) hclass
          (Eq.trans (α := HomotopyGroup N Y y)
            (congrArg (fun p : GenLoop N Y y ↦ (⟦p⟧ : HomotopyGroup N Y y))
              (GenLoop.map_const f hf))
            (HomotopyGroup.one_def (N := N) (X := Y) (x := y)).symm))
    map_mul' a b := by
      refine Quotient.inductionOn₂
        (motive := fun a b : HomotopyGroup N X x ↦
          classMap (a * b) = classMap a * classMap b) a b ?_
      intro p q
      let j : N := Classical.arbitrary N
      have hmul := HomotopyGroup.mul_spec (N := N) (X := X) (x := x)
        (i := j) (p := p) (q := q)
      refine Eq.trans (α := HomotopyGroup N Y y) (congrArg classMap hmul) ?_
      change (⟦GenLoop.map f hf (GenLoop.transAt j q p)⟧ : HomotopyGroup N Y y) =
        ((· * ·) : HomotopyGroup N Y y → HomotopyGroup N Y y → HomotopyGroup N Y y)
          ⟦GenLoop.map f hf p⟧ ⟦GenLoop.map f hf q⟧
      exact Eq.trans (α := HomotopyGroup N Y y)
        (congrArg (fun r : GenLoop N Y y ↦ (⟦r⟧ : HomotopyGroup N Y y))
          (GenLoop.map_transAt f hf j q p))
        (HomotopyGroup.mul_spec (N := N) (X := Y) (x := y)
          (i := j) (p := GenLoop.map f hf p) (q := GenLoop.map f hf q)).symm }

/-- The positive homomorphism has the all-index map as its underlying function,
with the given decidable equality and the canonical homotopy-group structures. -/
theorem coe_map_eq_mapFun (N : Type s) [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) :
    (map N f hf : HomotopyGroup N X x → HomotopyGroup N Y y) = mapFun N f hf :=
  rfl

/-- Compute the induced homomorphism on a representative. -/
@[simp]
theorem map_class (N : Type s) [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) (p : GenLoop N X x) :
    map N f hf (⟦p⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.map f hf p⟧ : HomotopyGroup N Y y) :=
  rfl

/-- The identity induces the identity homomorphism. -/
@[simp]
theorem map_id (N : Type s) [DecidableEq N] [Nonempty N] :
    map N (ContinuousMap.id X) (x := x) rfl =
      MonoidHom.id (HomotopyGroup N X x) := by
  apply MonoidHom.ext
  intro a
  change map N (ContinuousMap.id X) rfl a = a
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦ map N (ContinuousMap.id X) rfl a = a)
    a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N X x)
    (map_class N (ContinuousMap.id X) rfl p)
    (congrArg (fun r : GenLoop N X x ↦ (⟦r⟧ : HomotopyGroup N X x))
      (GenLoop.map_id p))

/-- The homomorphism induced by a composite is the composite homomorphism. -/
theorem map_comp (N : Type s) [DecidableEq N] [Nonempty N]
    (g : C(Y, Z)) (hg : g y = z) (f : C(X, Y)) (hf : f x = y) :
    map N (g.comp f) ((congrArg g hf).trans hg) =
      (map N g hg).comp (map N f hf) := by
  apply MonoidHom.ext
  intro a
  change map N (g.comp f) ((congrArg g hf).trans hg) a = map N g hg (map N f hf a)
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦
      map N (g.comp f) ((congrArg g hf).trans hg) a = map N g hg (map N f hf a)) a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N Z z)
    (map_class N (g.comp f) ((congrArg g hf).trans hg) p)
    (Eq.trans (α := HomotopyGroup N Z z)
      (congrArg (fun r : GenLoop N Z z ↦ (⟦r⟧ : HomotopyGroup N Z z))
        (GenLoop.map_comp g hg f hf p))
      (Eq.trans (α := HomotopyGroup N Z z)
        (map_class N g hg (GenLoop.map f hf p)).symm
        (congrArg (map N g hg) (map_class N f hf p).symm)))

/-- Maps homotopic relative to the source point induce the same homomorphism on
positive homotopy groups. -/
theorem map_eq_of_homotopyRel (N : Type s) [DecidableEq N] [Nonempty N]
    (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (H : ContinuousMap.HomotopyRel f g ({x} : Set X)) :
    map N f hf = map N g hg := by
  apply MonoidHom.ext
  intro a
  refine Quotient.inductionOn
    (motive := fun a : HomotopyGroup N X x ↦ map N f hf a = map N g hg a) a ?_
  intro p
  exact Eq.trans (α := HomotopyGroup N Y y)
    (map_class N f hf p)
    (Eq.trans (α := HomotopyGroup N Y y)
      (Quotient.sound (GenLoop.map_homotopic f g hf hg H p))
      (map_class N g hg p).symm)

/-- In dimension one, based postcomposition agrees with Mathlib's fundamental-group
map, under Mathlib's comparison with generalized loops. -/
theorem pi1MulEquivFundamentalGroup_map (f : C(X, Y)) (hf : f x = y)
    (a : HomotopyGroup (Fin 1) X x) :
    pi1MulEquivFundamentalGroup (X := Y) (x := y) (map (Fin 1) f hf a) =
      FundamentalGroup.mapOfEq f hf
        (pi1MulEquivFundamentalGroup (X := X) (x := x) a) := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [map_class, FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
      (genLoopEquivOfUnique (Fin 1) (GenLoop.map f hf p)) =
    ((Path.Homotopic.Quotient.mk (genLoopEquivOfUnique (Fin 1) p)).map f).cast
      hf.symm hf.symm
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_cast]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  rfl

end HomotopyGroup
