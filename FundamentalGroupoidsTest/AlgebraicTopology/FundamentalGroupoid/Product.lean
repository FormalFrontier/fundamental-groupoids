/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.Product
import all FundamentalGroupoidsTest.FundamentalGroup

/-!
# Two loop axes in a product of circles

The product of two copies of `AddCircle (1 : ℝ)` has two specified nonidentity loop
classes: each projects to the chosen circle class in one coordinate and to the identity
in the other. The index is `ULift.{1} Bool`, while each circle lies in `Type 0`; the
function space carries the usual Pi topology and is based at the constant zero function.

The circle class and its nonidentity proof are reused from `CircleTransport`. The axes
are assembled using Mathlib's `Path.Homotopic.pi`, and their coordinates are computed by
the induced fundamental-group homomorphisms of evaluation. The concatenation example
uses the reversed order relating quotient-path concatenation to endomorphism
multiplication. No commutativity assertion is needed.

## References

* Mathlib's `Topology.Homotopy.Product` supplies assembly and projection of path classes.
* `FundamentalGroupoidsTest.FundamentalGroup` supplies the nonidentity circle class,
  constructed using Mathlib's quotient covering of the circle.
-/

noncomputable section

namespace CircleProduct

private abbrev Index : Type 1 := ULift.{1} Bool
private abbrev Fiber (_ : Index) : Type := AddCircle (1 : ℝ)
private abbrev Space : Type 1 := ∀ i : Index, Fiber i

private abbrev base : Space := fun _ => 0
private abbrev Loop := FundamentalGroup Space base

private def zeroIndex : Index := ULift.up false
private def oneIndex : Index := ULift.up true

private def firstFamily (i : Index) : FundamentalGroup (Fiber i) (base i) :=
  match i.down with
  | false => CircleTransport.loopClass
  | true => 1

private def secondFamily (i : Index) : FundamentalGroup (Fiber i) (base i) :=
  match i.down with
  | false => 1
  | true => CircleTransport.loopClass

private def firstAxis : Loop :=
  FundamentalGroup.fromPath (Path.Homotopic.pi firstFamily)

private def secondAxis : Loop :=
  FundamentalGroup.fromPath (Path.Homotopic.pi secondFamily)

private def coordinate (i : Index) : Loop →* FundamentalGroup (Fiber i) (base i) :=
  FundamentalGroup.map
    (⟨fun x : Space => x i, continuous_apply i⟩ : C(Space, Fiber i)) base

private theorem coordinate_pi (i : Index)
    (paths : ∀ j, FundamentalGroup (Fiber j) (base j)) :
    coordinate i (FundamentalGroup.fromPath (Path.Homotopic.pi paths)) = paths i := by
  change Path.Homotopic.proj i (Path.Homotopic.pi paths) = paths i
  exact Path.Homotopic.proj_pi i paths

private theorem first_at_zero :
    coordinate zeroIndex firstAxis = CircleTransport.loopClass :=
  coordinate_pi zeroIndex firstFamily

private theorem first_at_one : coordinate oneIndex firstAxis = 1 :=
  coordinate_pi oneIndex firstFamily

private theorem second_at_zero : coordinate zeroIndex secondAxis = 1 :=
  coordinate_pi zeroIndex secondFamily

private theorem second_at_one :
    coordinate oneIndex secondAxis = CircleTransport.loopClass :=
  coordinate_pi oneIndex secondFamily

private theorem independent_axes :
    firstAxis ≠ 1 ∧ secondAxis ≠ 1 ∧ firstAxis ≠ secondAxis := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply CircleTransport.loopClass_ne_one
    simpa only [first_at_zero, map_one] using congrArg (coordinate zeroIndex) h
  · intro h
    apply CircleTransport.loopClass_ne_one
    simpa only [second_at_one, map_one] using congrArg (coordinate oneIndex) h
  · intro h
    apply CircleTransport.loopClass_ne_one
    simpa only [first_at_zero, second_at_zero] using congrArg (coordinate zeroIndex) h

private theorem concatenation_coordinates :
    coordinate zeroIndex
        ((FundamentalGroup.toPath secondAxis).trans (FundamentalGroup.toPath firstAxis)) =
      CircleTransport.loopClass ∧
    coordinate oneIndex
        ((FundamentalGroup.toPath secondAxis).trans (FundamentalGroup.toPath firstAxis)) =
      CircleTransport.loopClass := by
  change coordinate zeroIndex (firstAxis * secondAxis) = CircleTransport.loopClass ∧
    coordinate oneIndex (firstAxis * secondAxis) = CircleTransport.loopClass
  simp only [map_mul, first_at_zero, first_at_one, second_at_zero, second_at_one,
    mul_one, one_mul, and_self]

section ProductFunctors

open CategoryTheory FundamentalGroupoidFunctor

private abbrev circles : Index → TopCat.{0} := fun i => TopCat.of (Fiber i)

private abbrev coordinateBase : ∀ i, FundamentalGroupoid (circles i) :=
  fun i => FundamentalGroupoid.mk (base i)

private theorem assembly_projection_axes :
    (piProj circles zeroIndex).map
        ((piAssembly circles).map (firstFamily : coordinateBase ⟶ coordinateBase)) =
      CircleTransport.loopClass ∧
    (piProj circles oneIndex).map
        ((piAssembly circles).map (secondFamily : coordinateBase ⟶ coordinateBase)) =
      CircleTransport.loopClass := by
  constructor
  · rw [piProj_map, piAssembly_map]
    exact Path.Homotopic.proj_pi zeroIndex firstFamily
  · rw [piProj_map, piAssembly_map]
    exact Path.Homotopic.proj_pi oneIndex secondFamily

private theorem productIso_axes :
    (piProductIso circles).hom.map (firstFamily : coordinateBase ⟶ coordinateBase) =
      FundamentalGroup.toArrow firstAxis ∧
    ((piProductIso circles).inv.map (FundamentalGroup.toArrow secondAxis)) zeroIndex =
      FundamentalGroup.toArrow (1 : FundamentalGroup (Fiber zeroIndex) (base zeroIndex)) ∧
    ((piProductIso circles).inv.map (FundamentalGroup.toArrow secondAxis)) oneIndex =
      CircleTransport.loopClass := by
  refine ⟨?_, ?_, ?_⟩
  · exact piProductIso_hom_map circles (firstFamily : coordinateBase ⟶ coordinateBase)
  · rw [piProductIso_inv_map_apply]
    exact second_at_zero
  · rw [piProductIso_inv_map_apply]
    exact second_at_one

end ProductFunctors

end CircleProduct
