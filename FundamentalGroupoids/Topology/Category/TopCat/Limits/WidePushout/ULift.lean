/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Limits.WidePushout.PointMap

/-!
# Universe lifting of point-wide-pushouts

The universe lift of a point-wide-pushout is homeomorphic to the
point-wide-pushout of the lifted factors. The comparison preserves the head
and every factor inclusion.

The two point-wide-pushouts have one-point heads in their respective ambient
universes. Point-preserving descent supplies the maps in both directions;
its identity and composition laws supply their strict inverse equations.
The head is retained for an empty index type, without choosing a factor.
No separation or local compactness assumptions are needed.

## References

Mathlib's `Homeomorph.ulift` supplies the homeomorphism between a space and
its universe lift. The point-family descent, identity and composition laws
of Formal Frontier Agents supply the comparison maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

section

namespace TopCat

/-- Descent of the universe-lifting maps on the pointed factors. -/
def widePushoutPointULiftUp.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j) :
    C((widePushout (TopCat.of PUnit.{max u w + 1}) X
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
          TopCat.{max u w}),
      (widePushout (TopCat.of PUnit.{max v (max u w) + 1})
        (fun j ↦ TopCat.of (ULift.{v} (X j)))
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
          TopCat.{max v (max u w)})) :=
  widePushoutDesc
    (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j))
    (ContinuousMap.const (TopCat.of PUnit.{max u w + 1})
      (WidePushout.head
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j))))
        PUnit.unit))
    (fun j ↦ (WidePushout.ι
      (fun j ↦ (TopCat.const (ULift.up (x j)) :
        TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) j).hom.comp
      (((Homeomorph.ulift.{v, max u w} (X := X j)).symm : C(X j, ULift.{v} (X j)))))
    (widePushoutDesc_point_condition (X := X) (Y := (fun j ↦ TopCat.of (ULift.{v} (X j))))
      x (fun j ↦ (ULift.up (x j) : ULift.{v} (X j)))
      (fun j ↦ ((Homeomorph.ulift.{v, max u w} (X := X j)).symm : C(X j, ULift.{v} (X j))))
      (fun _ ↦ rfl))

/-- Descent of the universe-lowering maps on the pointed factors. -/
def widePushoutPointULiftDown.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j) :
    C((widePushout (TopCat.of PUnit.{max v (max u w) + 1})
        (fun j ↦ TopCat.of (ULift.{v} (X j)))
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
          TopCat.{max v (max u w)}),
      (widePushout (TopCat.of PUnit.{max u w + 1}) X
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
          TopCat.{max u w})) :=
  widePushoutDesc
    (fun j ↦ (TopCat.const (ULift.up (x j)) :
      TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j))))
    (ContinuousMap.const (TopCat.of PUnit.{max v (max u w) + 1})
      (WidePushout.head
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit))
    (fun j ↦ (WidePushout.ι
      (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) j).hom.comp
      ((Homeomorph.ulift.{v, max u w} (X := X j) : C(ULift.{v} (X j), X j))))
    (widePushoutDesc_point_condition (X := (fun j ↦ TopCat.of (ULift.{v} (X j)))) (Y := X)
      (fun j ↦ (ULift.up (x j) : ULift.{v} (X j))) x
      (fun j ↦ (Homeomorph.ulift.{v, max u w} (X := X j) : C(ULift.{v} (X j), X j)))
      (fun _ ↦ rfl))

/-- Lifting descent sends the original head to the lifted-factor head. -/
@[simp] theorem widePushoutPointULiftUp_head.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (q : PUnit.{max u w + 1}) :
    widePushoutPointULiftUp.{u, v, w} X x
      (WidePushout.head
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) q) =
      (WidePushout.head
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) PUnit.unit) :=
  widePushoutDesc_point_head (X := X) (Y := (fun j ↦ TopCat.of (ULift.{v} (X j))))
    x (fun j ↦ (ULift.up (x j) : ULift.{v} (X j)))
    (fun j ↦ ((Homeomorph.ulift.{v, max u w} (X := X j)).symm : C(X j, ULift.{v} (X j))))
    (fun _ ↦ rfl) q

/-- Lifting descent preserves the factor index and lifts its value. -/
@[simp] theorem widePushoutPointULiftUp_ι.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (j : J) (z : X j) :
    widePushoutPointULiftUp.{u, v, w} X x
      (WidePushout.ι
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) j z) =
      WidePushout.ι
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) j (ULift.up z) :=
  widePushoutDesc_point_ι (X := X) (Y := (fun j ↦ TopCat.of (ULift.{v} (X j))))
    x (fun j ↦ (ULift.up (x j) : ULift.{v} (X j)))
    (fun j ↦ ((Homeomorph.ulift.{v, max u w} (X := X j)).symm : C(X j, ULift.{v} (X j))))
    (fun _ ↦ rfl) j z

/-- Lowering descent sends the lifted-factor head to the original head. -/
@[simp] theorem widePushoutPointULiftDown_head.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (q : PUnit.{max v (max u w) + 1}) :
    widePushoutPointULiftDown.{u, v, w} X x
      (WidePushout.head
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) q) =
      (WidePushout.head
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit) :=
  widePushoutDesc_point_head (X := (fun j ↦ TopCat.of (ULift.{v} (X j)))) (Y := X)
    (fun j ↦ (ULift.up (x j) : ULift.{v} (X j))) x
    (fun j ↦ (Homeomorph.ulift.{v, max u w} (X := X j) : C(ULift.{v} (X j), X j)))
    (fun _ ↦ rfl) q

/-- Lowering descent preserves the factor index and lowers its value. -/
@[simp] theorem widePushoutPointULiftDown_ι.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (j : J) (z : ULift.{v} (X j)) :
    widePushoutPointULiftDown.{u, v, w} X x
      (WidePushout.ι
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) j z) =
      WidePushout.ι
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) j z.down :=
  widePushoutDesc_point_ι (X := (fun j ↦ TopCat.of (ULift.{v} (X j)))) (Y := X)
    (fun j ↦ (ULift.up (x j) : ULift.{v} (X j))) x
    (fun j ↦ (Homeomorph.ulift.{v, max u w} (X := X j) : C(ULift.{v} (X j), X j)))
    (fun _ ↦ rfl) j z

/-- Lowering after lifting is the identity on the original point-wide-pushout. -/
theorem widePushoutPointULiftDown_comp_up.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j) :
    (widePushoutPointULiftDown.{u, v, w} X x).comp
      (widePushoutPointULiftUp.{u, v, w} X x) = ContinuousMap.id
        (widePushout (TopCat.of PUnit.{max u w + 1}) X
          (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
            TopCat.{max u w}) := by
  exact (widePushoutDesc_point_comp (X := X) (Y := (fun j ↦ TopCat.of (ULift.{v} (X j)))) (Z := X)
    (a := x) (b := (fun j ↦ (ULift.up (x j) : ULift.{v} (X j))))
    (f := (fun j ↦ ((Homeomorph.ulift.{v, max u w} (X := X j)).symm : C(X j, ULift.{v} (X j)))))
    (hf := fun _ ↦ rfl) (c := x)
    (g := (fun j ↦ (Homeomorph.ulift.{v, max u w} (X := X j) : C(ULift.{v} (X j), X j))))
    (hg := fun _ ↦ rfl)).trans
      (widePushoutDesc_point_id (X := X) x)

/-- Lifting after lowering is the identity on the lifted-factor point-wide-pushout. -/
theorem widePushoutPointULiftUp_comp_down.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j) :
    (widePushoutPointULiftUp.{u, v, w} X x).comp
      (widePushoutPointULiftDown.{u, v, w} X x) = ContinuousMap.id
        (widePushout (TopCat.of PUnit.{max v (max u w) + 1})
          (fun j ↦ TopCat.of (ULift.{v} (X j)))
          (fun j ↦ (TopCat.const (ULift.up (x j)) :
            TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
            TopCat.{max v (max u w)}) := by
  exact (widePushoutDesc_point_comp (X := (fun j ↦ TopCat.of (ULift.{v} (X j)))) (Y := X)
    (Z := (fun j ↦ TopCat.of (ULift.{v} (X j))))
    (a := (fun j ↦ (ULift.up (x j) : ULift.{v} (X j)))) (b := x)
    (f := (fun j ↦ (Homeomorph.ulift.{v, max u w} (X := X j) : C(ULift.{v} (X j), X j))))
    (hf := fun _ ↦ rfl) (c := (fun j ↦ (ULift.up (x j) : ULift.{v} (X j))))
    (g := (fun j ↦ ((Homeomorph.ulift.{v, max u w} (X := X j)).symm : C(X j, ULift.{v} (X j)))))
    (hg := fun _ ↦ rfl)).trans
      (widePushoutDesc_point_id (X := (fun j ↦ TopCat.of (ULift.{v} (X j))))
        (fun j ↦ (ULift.up (x j) : ULift.{v} (X j))))

/-- The universe lift of a point-wide-pushout is homeomorphic to the
point-wide-pushout of its universe-lifted factors. -/
def widePushoutPointULiftHomeomorph.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j) :
    ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
      (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
        TopCat.{max u w}) ≃ₜ
      (widePushout (TopCat.of PUnit.{max v (max u w) + 1})
        (fun j ↦ TopCat.of (ULift.{v} (X j)))
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
          TopCat.{max v (max u w)}) :=
  (Homeomorph.ulift :
    ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
      (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
        TopCat.{max u w}) ≃ₜ
      (widePushout (TopCat.of PUnit.{max u w + 1}) X
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
          TopCat.{max u w})).trans
    { toFun := widePushoutPointULiftUp.{u, v, w} X x
      invFun := widePushoutPointULiftDown.{u, v, w} X x
      left_inv := fun q ↦ congrArg
        (fun k : C((widePushout (TopCat.of PUnit.{max u w + 1}) X
            (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
              TopCat.{max u w}),
          (widePushout (TopCat.of PUnit.{max u w + 1}) X
            (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
              TopCat.{max u w})) ↦ k q)
        (widePushoutPointULiftDown_comp_up.{u, v, w} X x)
      right_inv := fun q ↦ congrArg
        (fun k : C((widePushout (TopCat.of PUnit.{max v (max u w) + 1})
            (fun j ↦ TopCat.of (ULift.{v} (X j)))
            (fun j ↦ (TopCat.const (ULift.up (x j)) :
              TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
              TopCat.{max v (max u w)}),
          (widePushout (TopCat.of PUnit.{max v (max u w) + 1})
            (fun j ↦ TopCat.of (ULift.{v} (X j)))
            (fun j ↦ (TopCat.const (ULift.up (x j)) :
              TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
              TopCat.{max v (max u w)})) ↦ k q)
        (widePushoutPointULiftUp_comp_down.{u, v, w} X x)
      continuous_toFun := (widePushoutPointULiftUp.{u, v, w} X x).continuous
      continuous_invFun := (widePushoutPointULiftDown.{u, v, w} X x).continuous }

/-- The homeomorphism lowers the source lift before point-family descent. -/
theorem widePushoutPointULiftHomeomorph_apply.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (q : ULift.{v} (widePushout (TopCat.of PUnit.{max u w + 1}) X
      (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) :
        TopCat.{max u w})) :
    widePushoutPointULiftHomeomorph.{u, v, w} X x q =
      widePushoutPointULiftUp.{u, v, w} X x q.down := rfl

/-- The inverse comparison lifts the value of the lowering descent. -/
theorem widePushoutPointULiftHomeomorph_symm_apply.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (q : (widePushout (TopCat.of PUnit.{max v (max u w) + 1})
      (fun j ↦ TopCat.of (ULift.{v} (X j)))
      (fun j ↦ (TopCat.const (ULift.up (x j)) :
        TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) :
        TopCat.{max v (max u w)})) :
    (widePushoutPointULiftHomeomorph.{u, v, w} X x).symm q =
      ULift.up (widePushoutPointULiftDown.{u, v, w} X x q) := rfl

/-- The homeomorphism preserves the head, also for an empty family. -/
@[simp] theorem widePushoutPointULiftHomeomorph_head.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (q : PUnit.{max u w + 1}) :
    widePushoutPointULiftHomeomorph.{u, v, w} X x
      (ULift.up (WidePushout.head
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) q)) =
      (WidePushout.head
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) PUnit.unit) :=
  widePushoutPointULiftUp_head.{u, v, w} X x q

/-- The homeomorphism preserves the given index and lifts its factor value. -/
@[simp] theorem widePushoutPointULiftHomeomorph_ι.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (j : J) (z : X j) :
    widePushoutPointULiftHomeomorph.{u, v, w} X x
      (ULift.up (WidePushout.ι
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) j z)) =
      WidePushout.ι
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) j (ULift.up z) :=
  widePushoutPointULiftUp_ι.{u, v, w} X x j z

/-- The inverse comparison sends the higher-universe head to the lifted original head. -/
@[simp] theorem widePushoutPointULiftHomeomorph_symm_head.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (q : PUnit.{max v (max u w) + 1}) :
    (widePushoutPointULiftHomeomorph.{u, v, w} X x).symm
      (WidePushout.head
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) q) =
      ULift.up (WidePushout.head
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit) :=
  congrArg ULift.up (widePushoutPointULiftDown_head.{u, v, w} X x q)

/-- The inverse comparison preserves the given index and lowers its factor value. -/
@[simp] theorem widePushoutPointULiftHomeomorph_symm_ι.{u, v, w}
    {J : Type w} (X : J → TopCat.{max u w}) (x : ∀ j, X j)
    (j : J) (z : ULift.{v} (X j)) :
    (widePushoutPointULiftHomeomorph.{u, v, w} X x).symm
      (WidePushout.ι
        (fun j ↦ (TopCat.const (ULift.up (x j)) :
          TopCat.of PUnit.{max v (max u w) + 1} ⟶ TopCat.of (ULift.{v} (X j)))) j z) =
      ULift.up (WidePushout.ι
        (fun j ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j)) j z.down) :=
  congrArg ULift.up (widePushoutPointULiftDown_ι.{u, v, w} X x j z)

end TopCat

end
