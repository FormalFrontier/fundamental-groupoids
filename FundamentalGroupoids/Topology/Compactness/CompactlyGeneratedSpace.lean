/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace

/-!
# Maps into the compactly generated topology

Mathlib's `TopologicalSpace.compactlyGenerated.{u} X` is a topology on the same
carrier `X`, tested by continuous maps from `CompHaus.{u}`. The continuous
identity `ContinuousMap.compactlyGeneratedCounit` points from this topology
to the original one.

For a `UCompactlyGeneratedSpace.{u}` source, continuity of a function into the
compactly generated topology is equivalent to continuity into the original
topology. `ContinuousMap.toCompactlyGenerated` bundles this unchanged function;
its two composition identities characterize the lift. The probe, source and
target universes are independent. `ContinuousMap.compactlyGeneratedMap` refines
both topologies of a continuous map without changing its function, compatibly
with identity, composition and the outward comparisons.

No separation hypothesis is imposed. In particular, this is the CompHaus-test
construction, not a claim that an arbitrary target is weak Hausdorff. May's
term "compactly generated" includes weak Hausdorffness. No new type, topology,
category or adjunction is introduced here.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 5 §§1–2,
  pp. 39–40, for compact-Hausdorff tests and the continuous identity to the
  original topology, with the weak-Hausdorff convention described above.
* Mathlib's compactly generated topology and source-test continuity API,
  due to Dagur Asgeirsson and Etienne Marion.
-/

@[expose] public section

universe u v w z

open TopologicalSpace

namespace ContinuousMap

variable (X : Type v) [tX : TopologicalSpace X]

/-- The continuous identity from the CompHaus-test compactly generated topology
to the original topology on the same carrier. This is a continuous map, not a
packaged categorical adjunction. -/
def compactlyGeneratedCounit :
    @ContinuousMap X X (compactlyGenerated.{u} X) tX :=
  @ContinuousMap.mk X X (compactlyGenerated.{u} X) tX (_root_.id : X → X)
    (@continuous_from_compactlyGenerated.{u} X X tX tX (_root_.id : X → X)
      fun _ g ↦ g.continuous)

/-- The outward comparison does not change points. -/
@[simp]
theorem compactlyGeneratedCounit_apply (x : X) :
    compactlyGeneratedCounit.{u} X x = x :=
  rfl

end ContinuousMap

/-- For a `u`-compactly generated source, a function is continuous into the
CompHaus-test compactly generated topology exactly when it is continuous into
the original topology. The target has no compact-generation or separation
hypothesis, and the three universes are independent. -/
theorem continuous_to_compactlyGenerated_iff {Z : Type w} {X : Type v}
    [tZ : TopologicalSpace Z] [tX : TopologicalSpace X]
    [UCompactlyGeneratedSpace.{u} Z] (f : Z → X) :
    @Continuous Z X tZ (compactlyGenerated.{u} X) f ↔ @Continuous Z X tZ tX f := by
  constructor
  · intro h
    exact @Continuous.comp Z X X tZ (compactlyGenerated.{u} X) tX f _root_.id
      (@ContinuousMap.continuous_toFun X X (compactlyGenerated.{u} X) tX
        (@ContinuousMap.compactlyGeneratedCounit.{u} X tX)) h
  · intro h
    refine @continuous_from_uCompactlyGeneratedSpace.{u} Z X tZ
      (compactlyGenerated.{u} X) inferInstance f ?_
    intro S g
    let p : C(S, X) :=
      @ContinuousMap.mk S X inferInstance tX (f ∘ g) (h.comp g.continuous)
    let e : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) → X :=
      fun ⟨⟨_, i⟩, s⟩ ↦ i s
    suffices ∀ (i : (T : CompHaus.{u}) × C(T, X)),
        @Continuous i.fst X inferInstance (compactlyGenerated.{u} X)
          (fun (a : i.fst) ↦ e ⟨i, a⟩) from this ⟨S, p⟩
    rw [← @continuous_sigma_iff]
    apply continuous_coinduced_rng

namespace ContinuousMap

variable {Z : Type w} {X : Type v}
variable [tZ : TopologicalSpace Z] [tX : TopologicalSpace X]
variable [UCompactlyGeneratedSpace.{u} Z]

/-- Lift a continuous map from a `u`-compactly generated source to the
CompHaus-test compactly generated topology, without changing its function. -/
def toCompactlyGenerated (f : C(Z, X)) :
    @ContinuousMap Z X tZ (compactlyGenerated.{u} X) :=
  @ContinuousMap.mk Z X tZ (compactlyGenerated.{u} X) (f : Z → X)
    ((@continuous_to_compactlyGenerated_iff.{u} Z X tZ tX inferInstance
      (f : Z → X)).2 f.continuous)

/-- The lift has the same pointwise values as the original map. -/
@[simp]
theorem toCompactlyGenerated_apply (f : C(Z, X)) (z : Z) :
    toCompactlyGenerated.{u} f z = f z :=
  rfl

/-- Composing a lift with the outward comparison recovers the original map. -/
@[simp]
theorem compactlyGeneratedCounit_comp_toCompactlyGenerated (f : C(Z, X)) :
    @ContinuousMap.comp Z X X tZ (compactlyGenerated.{u} X) tX
      (compactlyGeneratedCounit.{u} X) (toCompactlyGenerated.{u} f) = f :=
  rfl

/-- Lifting the outward composite recovers a map into the compactly generated
topology. Together with the other composition identity, this characterizes the
lift uniquely. -/
@[simp]
theorem toCompactlyGenerated_comp_compactlyGeneratedCounit
    (g : @ContinuousMap Z X tZ (compactlyGenerated.{u} X)) :
    toCompactlyGenerated.{u}
      (@ContinuousMap.comp Z X X tZ (compactlyGenerated.{u} X) tX
        (compactlyGeneratedCounit.{u} X) g) = g :=
  rfl

end ContinuousMap

namespace ContinuousMap

variable {X : Type v} {Y : Type w} {Z : Type z}
variable [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]

/-- A continuous map remains continuous when both its source and target have
the CompHaus-test compactly generated topologies. Its function is unchanged. -/
def compactlyGeneratedMap (f : C(X, Y)) :
    @ContinuousMap X Y (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y) :=
  @ContinuousMap.mk X Y (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y)
    (f : X → Y)
    (@continuous_from_compactlyGenerated.{u} X Y tX (compactlyGenerated.{u} Y) f
      fun S g ↦
        (@continuous_to_compactlyGenerated_iff.{u} S Y inferInstance tY inferInstance
          (f ∘ g)).2 (f.continuous.comp g.continuous))

/-- Refining the topologies does not change the values of a continuous map. -/
@[simp]
theorem compactlyGeneratedMap_apply (f : C(X, Y)) (x : X) :
    compactlyGeneratedMap.{u} f x = f x :=
  rfl

/-- Refinement preserves the identity continuous map. -/
@[simp]
theorem compactlyGeneratedMap_id :
    compactlyGeneratedMap.{u} (ContinuousMap.id X) =
      @ContinuousMap.id X (compactlyGenerated.{u} X) :=
  rfl

/-- Refinement preserves composition of continuous maps. -/
theorem compactlyGeneratedMap_comp (g : C(Y, Z)) (f : C(X, Y)) :
    compactlyGeneratedMap.{u} (@ContinuousMap.comp X Y Z tX tY tZ g f) =
      @ContinuousMap.comp X Y Z (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y) (compactlyGenerated.{u} Z)
        (compactlyGeneratedMap.{u} g) (compactlyGeneratedMap.{u} f) :=
  rfl

/-- The outward comparisons commute with every continuous map. -/
theorem compactlyGeneratedCounit_naturality (f : C(X, Y)) :
    @ContinuousMap.comp X Y Y (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y) tY
      (compactlyGeneratedCounit.{u} Y) (compactlyGeneratedMap.{u} f) =
      @ContinuousMap.comp X X Y (compactlyGenerated.{u} X) tX tY
        f (compactlyGeneratedCounit.{u} X) :=
  rfl

end ContinuousMap
