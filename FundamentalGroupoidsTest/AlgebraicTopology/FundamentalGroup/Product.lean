/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Product
import all FundamentalGroupoidsTest.FundamentalGroup

/-!
# Loop classes in an infinite product of circles and lines

The index `ULift.{1} (Bool × ℕ)` lies in `Type 1`. Its false coordinates are
copies of `AddCircle (1 : ℝ)` and its true coordinates are copies of `ℝ`, all in
`Type 0` and based at zero. A family with the chosen nonidentity circle class
at every false coordinate and the identity at every true coordinate assembles
into a nonidentity loop class by `Path.Homotopic.pi`. Its coordinate values and
nonidentity are established directly by projection of path classes.

The product fundamental-group equivalence sends this assembled class to the
chosen family, and its inverse recovers that class. For the empty index, its
injectivity shows that every loop class is the identity. The groups use the
endomorphism and pointwise function-group structures; loop multiplication
traverses the right factor first.

## References

* Mathlib's `Topology.Homotopy.Product` supplies assembly and projection of path classes.
* `FundamentalGroupoidsTest.FundamentalGroup` supplies `CircleTransport.loopClass`
  and its nonidentity proof, using Mathlib's quotient covering of the circle.
-/

noncomputable section

namespace CircleRealProduct

private abbrev Index : Type 1 := ULift.{1} (Bool × ℕ)

private abbrev fibers : Bool → TopCat.{0}
  | false => TopCat.of CircleTransport.A
  | true => TopCat.of ℝ

private abbrev Fiber (i : Index) : Type := fibers i.down.1
private abbrev Space : Type 1 := ∀ i : Index, Fiber i

private def base : Space
  | ⟨(false, _)⟩ => 0
  | ⟨(true, _)⟩ => 0

private def loopFamily : ∀ i, FundamentalGroup (Fiber i) (base i)
  | ⟨(false, _)⟩ => CircleTransport.loopClass
  | ⟨(true, _)⟩ => 1

private def assembledLoop : FundamentalGroup Space base :=
  FundamentalGroup.fromPath (Path.Homotopic.pi loopFamily)

private def circleIndex : Index := ULift.up (false, 0)
private def realIndex : Index := ULift.up (true, 0)

private def coordinate (i : Index) :
    FundamentalGroup Space base →* FundamentalGroup (Fiber i) (base i) :=
  FundamentalGroup.map
    (⟨fun x : Space => x i, continuous_apply i⟩ : C(Space, Fiber i)) base

private theorem coordinates_and_nontriviality :
    coordinate circleIndex assembledLoop = CircleTransport.loopClass ∧
    coordinate realIndex assembledLoop = 1 ∧
    assembledLoop ≠ 1 := by
  have hc : coordinate circleIndex assembledLoop = CircleTransport.loopClass := by
    change Path.Homotopic.proj circleIndex (Path.Homotopic.pi loopFamily) =
      loopFamily circleIndex
    exact Path.Homotopic.proj_pi circleIndex loopFamily
  have hr : coordinate realIndex assembledLoop = 1 := by
    change Path.Homotopic.proj realIndex (Path.Homotopic.pi loopFamily) =
      loopFamily realIndex
    exact Path.Homotopic.proj_pi realIndex loopFamily
  refine ⟨hc, hr, ?_⟩
  intro h
  have hcoord :
      @Eq (FundamentalGroup CircleTransport.A 0)
        (coordinate circleIndex assembledLoop) (coordinate circleIndex 1) :=
    congrArg (coordinate circleIndex) h
  rw [hc, map_one] at hcoord
  exact CircleTransport.loopClass_ne_one hcoord

private theorem pi_characteristics :
    FundamentalGroup.piMulEquiv base assembledLoop = loopFamily ∧
    (FundamentalGroup.piMulEquiv base).symm loopFamily = assembledLoop := by
  constructor
  · funext i
    rw [FundamentalGroup.piMulEquiv_apply]
    change Path.Homotopic.proj i (Path.Homotopic.pi loopFamily) = loopFamily i
    exact Path.Homotopic.proj_pi i loopFamily
  · exact FundamentalGroup.piMulEquiv_symm_apply base loopFamily

private theorem translated_circle_coordinate :
    let f : ∀ i, C(Fiber i, Fiber i) := fun
      | ⟨(false, _)⟩ => CircleTransport.translation
      | ⟨(true, _)⟩ => ContinuousMap.id ℝ
    FundamentalGroup.piMulEquiv (fun i => f i (base i))
      (FundamentalGroup.map (ContinuousMap.piMap f) base assembledLoop) circleIndex =
      FundamentalGroup.map CircleTransport.translation 0 CircleTransport.loopClass := by
  dsimp only
  rw [FundamentalGroup.piMulEquiv_naturality, FundamentalGroup.piMulEquiv_apply]
  exact congrArg (FundamentalGroup.map CircleTransport.translation 0)
    coordinates_and_nontriviality.1

private theorem repeated_circle_coordinate (n : ℕ) :
    FundamentalGroup.piMulEquiv (fun _ : ℕ => base circleIndex)
      (FundamentalGroup.map (ContinuousMap.precomp (fun _ : ℕ => circleIndex))
        base assembledLoop) n = CircleTransport.loopClass := by
  have h :
      @Eq (FundamentalGroup CircleTransport.A 0)
        (FundamentalGroup.piMulEquiv (fun _ : ℕ => base circleIndex)
          (FundamentalGroup.map (ContinuousMap.precomp (fun _ : ℕ => circleIndex))
            base assembledLoop) n)
        (FundamentalGroup.piMulEquiv base assembledLoop circleIndex) :=
    FundamentalGroup.piMulEquiv_reindex (fun _ : ℕ => circleIndex) base assembledLoop n
  exact h.trans (by
    rw [FundamentalGroup.piMulEquiv_apply]
    exact coordinates_and_nontriviality.1)

end CircleRealProduct

private theorem empty_index_loop_eq_one
    (q : FundamentalGroup (∀ _ : Empty, CircleTransport.A) (fun _ => 0)) :
    q = 1 := by
  apply (FundamentalGroup.piMulEquiv (fun _ : Empty => (0 : CircleTransport.A))).injective
  funext i
  exact Empty.elim i
