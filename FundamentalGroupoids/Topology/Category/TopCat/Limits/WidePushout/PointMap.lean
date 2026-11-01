/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Limits.WidePushout

/-!
# Descent of maps between point-attached families

Point-preserving continuous maps between families descend through their
point-wide-pushouts, with independently sized source and target families.
The head map is constant at the target head point, including when the index
is empty. Head and factor equations characterize descent, which preserves
identities and composition.

## References

The categorical and point-collision API is due to Formal Frontier Agents and
Mathlib's colimit/quotient constructions (including Joël Riou's pushouts).
Mathlib's map API is due to Johannes Hölzl, Mario Carneiro and Patrick Massot.
Tiller and Loupe's public mathematical discussion supplied image/preimage and
empty-head observations.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u v w z

namespace TopCat

variable {I : Type v}

variable {X : I → TopCat.{max u v}} {Y : I → TopCat.{max w v}}
  (a : ∀ i, X i) (b : ∀ i, Y i)

set_option quotPrecheck false in
local notation "PX" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "PY" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "α" => (fun i ↦ (TopCat.const (a i) : PX ⟶ X i))
set_option quotPrecheck false in
local notation "β" => (fun i ↦ (TopCat.const (b i) : PY ⟶ Y i))
set_option quotPrecheck false in
local notation "WX" => (widePushout PX X α : TopCat)
set_option quotPrecheck false in
local notation "WY" => (widePushout PY Y β : TopCat)
set_option quotPrecheck false in
local notation "hx" => WidePushout.head α PUnit.unit
set_option quotPrecheck false in
local notation "hy" => WidePushout.head β PUnit.unit

/-- Point preservation is the compatibility condition for the existing descent. -/
theorem widePushoutDesc_point_condition (f : ∀ i, C(X i, Y i))
    (hf : ∀ i, f i (a i) = b i) (i : I) (q : PUnit.{max u v + 1}) :
    ((WidePushout.ι β i).hom.comp (f i)) (α i q) =
      (ContinuousMap.const PX hy) q := by
  change WidePushout.ι β i (f i (a i)) = hy
  rw [hf i]
  exact congrArg (fun k : PY ⟶ WY ↦ k PUnit.unit) (WidePushout.arrow_ι β i)

variable (f : ∀ i, C(X i, Y i)) (hf : ∀ i, f i (a i) = b i)

set_option quotPrecheck false in
local notation "F" => widePushoutDesc α (ContinuousMap.const PX hy)
  (fun i ↦ (WidePushout.ι β i).hom.comp (f i))
  (widePushoutDesc_point_condition a b f hf)

/-- The canonical point-family descent has constant head value. -/
@[simp] theorem widePushoutDesc_point_head (q : PUnit.{max u v + 1}) :
    F (WidePushout.head α q) = hy :=
  widePushoutDesc_head α (ContinuousMap.const PX hy)
    (fun i ↦ (WidePushout.ι β i).hom.comp (f i))
    (widePushoutDesc_point_condition a b f hf) q

/-- The canonical point-family descent has the prescribed factor values. -/
theorem widePushoutDesc_point_ι (i : I) (x : X i) :
    F (WidePushout.ι α i x) = WidePushout.ι β i (f i x) :=
  widePushoutDesc_ι α (ContinuousMap.const PX hy)
    (fun i ↦ (WidePushout.ι β i).hom.comp (f i))
    (widePushoutDesc_point_condition a b f hf) i x

/-- Head and factor values uniquely determine the canonical descent. -/
theorem widePushoutDesc_point_unique (k : C(WX, WY))
    (hh : k hx = hy) (hi : ∀ i x, k (WidePushout.ι α i x) = WidePushout.ι β i (f i x)) :
    k = F := by
  apply widePushoutDesc_unique α (ContinuousMap.const PX hy)
    (fun i ↦ (WidePushout.ι β i).hom.comp (f i))
    (widePushoutDesc_point_condition a b f hf) k
  · intro q
    cases q
    exact hh
  · exact hi

/-- Identity factor maps descend to the identity, including for an empty family. -/
theorem widePushoutDesc_point_id :
    widePushoutDesc α (ContinuousMap.const PX hx)
      (fun i ↦ (WidePushout.ι α i).hom.comp (ContinuousMap.id (X i)))
      (widePushoutDesc_point_condition a a (fun i ↦ ContinuousMap.id (X i))
        (fun _ ↦ rfl)) = ContinuousMap.id WX := by
  symm
  apply widePushoutDesc_point_unique a a (fun i ↦ ContinuousMap.id (X i))
    (fun _ ↦ rfl) (ContinuousMap.id WX)
  · rfl
  · intro i x
    rfl

section Composition

variable {Z : I → TopCat.{max z v}} (c : ∀ i, Z i)
  (g : ∀ i, C(Y i, Z i)) (hg : ∀ i, g i (b i) = c i)

set_option quotPrecheck false in
local notation "PZ" => TopCat.of PUnit
set_option quotPrecheck false in
local notation "γ" => (fun i ↦ (TopCat.const (c i) : PZ ⟶ Z i))
set_option quotPrecheck false in
local notation "hz" => WidePushout.head γ PUnit.unit
set_option quotPrecheck false in
local notation "G" => widePushoutDesc β (ContinuousMap.const PY hz)
  (fun i ↦ (WidePushout.ι γ i).hom.comp (g i))
  (widePushoutDesc_point_condition b c g hg)

/-- Descent respects composition into an independently sized third family. -/
theorem widePushoutDesc_point_comp :
    (widePushoutDesc β (ContinuousMap.const PY hz)
      (fun i ↦ (WidePushout.ι γ i).hom.comp (g i))
      (widePushoutDesc_point_condition b c g hg)).comp F =
    widePushoutDesc α (ContinuousMap.const PX hz)
      (fun i ↦ (WidePushout.ι γ i).hom.comp ((g i).comp (f i)))
      (widePushoutDesc_point_condition a c (fun i ↦ (g i).comp (f i))
        (fun i ↦ by
          change g i (f i (a i)) = c i
          rw [hf i, hg i])) := by
  apply widePushoutDesc_point_unique a c (fun i ↦ (g i).comp (f i))
    (fun i ↦ by
      change g i (f i (a i)) = c i
      rw [hf i, hg i])
  · change G (F hx) = hz
    exact (congrArg G (widePushoutDesc_point_head a b f hf PUnit.unit)).trans
      (widePushoutDesc_point_head b c g hg PUnit.unit)
  · intro i x
    change G (F (WidePushout.ι α i x)) = WidePushout.ι γ i (g i (f i x))
    exact (congrArg G (widePushoutDesc_point_ι a b f hf i x)).trans
      (widePushoutDesc_point_ι b c g hg i (f i x))

end Composition

end TopCat
