/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Homotopy.Basic

/-!
# Relative homotopies into the compactly generated topology

A relative homotopy from a `UCompactlyGeneratedSpace.{u}` source lifts to the
CompHaus-test compactly generated topology on its target without changing its
values. The interval product of the source is `u`-compactly generated, so the
construction lifts the entire jointly continuous map, not just its time slices.
The endpoint maps are their existing `ContinuousMap.toCompactlyGenerated` lifts,
and the homotopy remains fixed on the same arbitrary subset of the source.

Postcomposition by `ContinuousMap.compactlyGeneratedCounit` recovers the original
relative homotopy and is inverse to this lift. Refinement also commutes with
postcomposition, using `ContinuousMap.compactlyGeneratedMap` between refined
targets. Consequently relative-homotopy existence is unchanged by refinement.

The probe, source and target universes are independent. There are no separation
or compact-generation assumptions on the target, and no local compactness or
countability assumptions on the source. All constructions use the existing
relative-homotopy structures and the stock product topology on the cylinder.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 5 §§1–2,
  pp. 39–40, for compact-Hausdorff tests and the continuous identity from the
  compactly generated topology. May's convention also includes weak
  Hausdorffness, which is not assumed here.
* Mathlib's compactly generated topology and source-test continuity API,
  due to Dagur Asgeirsson and Etienne Marion, and its relative homotopies,
  due to Shing Tak Lam and contributors.
-/

@[expose] public section

universe u v w z

open TopologicalSpace unitInterval

namespace ContinuousMap

variable {A : Type v} {X : Type w}
variable [tA : TopologicalSpace A] [tX : TopologicalSpace X]
variable [UCompactlyGeneratedSpace.{u} A]

namespace HomotopyRel

variable {f g : C(A, X)} {s : Set A}

/-- Lift a relative homotopy to the CompHaus-test compactly generated topology
without changing its jointly continuous function or its fixed subset. -/
def toCompactlyGenerated (H : HomotopyRel f g s) :
    @HomotopyRel A X tA (compactlyGenerated.{u} X)
      (ContinuousMap.toCompactlyGenerated.{u} f)
      (ContinuousMap.toCompactlyGenerated.{u} g) s :=
  @ContinuousMap.HomotopyWith.mk A X tA (compactlyGenerated.{u} X)
    (ContinuousMap.toCompactlyGenerated.{u} f)
    (ContinuousMap.toCompactlyGenerated.{u} g)
    (fun k ↦ ∀ a ∈ s, k a = (ContinuousMap.toCompactlyGenerated.{u} f) a)
    (@ContinuousMap.Homotopy.mk A X tA (compactlyGenerated.{u} X)
      (ContinuousMap.toCompactlyGenerated.{u} f)
      (ContinuousMap.toCompactlyGenerated.{u} g)
      (@ContinuousMap.toCompactlyGenerated.{u} (I × A) X
        inferInstance tX inferInstance H.toContinuousMap)
      (fun a ↦ H.apply_zero a)
      (fun a ↦ H.apply_one a))
    (fun t a ha ↦ H.eq_fst t (x := a) ha)

/-- The lifted relative homotopy has the same values on the whole cylinder. -/
@[simp]
theorem toCompactlyGenerated_apply (H : HomotopyRel f g s) (p : I × A) :
    toCompactlyGenerated.{u} H p = H p :=
  rfl

/-- The underlying continuous map is the lift of the joint continuous map. -/
@[simp]
theorem toCompactlyGenerated_toContinuousMap (H : HomotopyRel f g s) :
    @_root_.toContinuousMap
      (@HomotopyRel A X tA (compactlyGenerated.{u} X)
        (ContinuousMap.toCompactlyGenerated.{u} f)
        (ContinuousMap.toCompactlyGenerated.{u} g) s)
      (I × A) X inferInstance (compactlyGenerated.{u} X)
      inferInstance inferInstance (toCompactlyGenerated.{u} H) =
      @ContinuousMap.toCompactlyGenerated.{u} (I × A) X
        inferInstance tX inferInstance H.toContinuousMap :=
  rfl

/-- Postcomposing a lifted relative homotopy with the outward comparison
recovers the original relative homotopy. -/
@[simp]
theorem compactlyGeneratedCounit_comp_toCompactlyGenerated (H : HomotopyRel f g s) :
    @HomotopyRel.compContinuousMap A X X tA (compactlyGenerated.{u} X) tX s
      (ContinuousMap.toCompactlyGenerated.{u} f)
      (ContinuousMap.toCompactlyGenerated.{u} g) (toCompactlyGenerated.{u} H)
      (ContinuousMap.compactlyGeneratedCounit.{u} X) = H := by
  apply @ContinuousMap.HomotopyWith.ext A X tA tX
  intro p
  rfl

/-- Lifting the outward composite recovers a relative homotopy into the
compactly generated topology. -/
@[simp]
theorem toCompactlyGenerated_comp_compactlyGeneratedCounit
    {p q : @ContinuousMap A X tA (compactlyGenerated.{u} X)}
    (H : @HomotopyRel A X tA (compactlyGenerated.{u} X) p q s) :
    toCompactlyGenerated.{u}
      (@HomotopyRel.compContinuousMap A X X tA (compactlyGenerated.{u} X) tX s p q H
        (ContinuousMap.compactlyGeneratedCounit.{u} X)) = H := by
  apply @ContinuousMap.HomotopyWith.ext A X tA (compactlyGenerated.{u} X)
  intro r
  rfl

/-- Refining a relative homotopy commutes with target postcomposition. -/
theorem toCompactlyGenerated_compContinuousMap
    {Y : Type z} [tY : TopologicalSpace Y]
    (H : HomotopyRel f g s) (h : C(X, Y)) :
    toCompactlyGenerated.{u}
      (@HomotopyRel.compContinuousMap A X Y tA tX tY s f g H h) =
      @HomotopyRel.compContinuousMap A X Y tA (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y) s
        (ContinuousMap.toCompactlyGenerated.{u} f)
        (ContinuousMap.toCompactlyGenerated.{u} g) (toCompactlyGenerated.{u} H)
        (ContinuousMap.compactlyGeneratedMap.{u} h) := by
  apply @ContinuousMap.HomotopyWith.ext A Y tA (compactlyGenerated.{u} Y)
  intro p
  rfl

end HomotopyRel

/-- Relative homotopies between the lifted endpoint maps exist exactly when
relative homotopies between the original maps exist, with the same fixed subset. -/
theorem homotopicRel_toCompactlyGenerated_iff (f g : C(A, X)) (s : Set A) :
    @ContinuousMap.HomotopicRel A X tA (compactlyGenerated.{u} X)
      (ContinuousMap.toCompactlyGenerated.{u} f)
      (ContinuousMap.toCompactlyGenerated.{u} g) s ↔ HomotopicRel f g s := by
  constructor
  · intro h
    exact h.map (fun H ↦
      @HomotopyRel.compContinuousMap A X X tA (compactlyGenerated.{u} X) tX s
        (ContinuousMap.toCompactlyGenerated.{u} f)
        (ContinuousMap.toCompactlyGenerated.{u} g) H (compactlyGeneratedCounit.{u} X))
  · intro h
    exact h.map (fun H ↦ HomotopyRel.toCompactlyGenerated.{u} H)

end ContinuousMap
