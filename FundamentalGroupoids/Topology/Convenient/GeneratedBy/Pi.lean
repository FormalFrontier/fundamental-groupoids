/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Convenient.GeneratedBy.Prod
public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Canonical dependent products of generated-by refinements

For any family of probes and any dependent family of original spaces, refining the
product of the refined factors is canonically homeomorphic to refining the original
product. The forward map refines the coordinate counits. The reverse map lifts the
family of refined original evaluations from its generated source.

The outer refinement is retained on both products; no generatedness of an ordinary
product, condition on the original factors, or closure property of probes is assumed.
The comparison is natural in the whole family and commutes with pair evaluations
into the binary comparison.
-/

@[expose] public section

noncomputable section

universe p u t v w

open Topology

namespace Topology.WithGeneratedByTopology

variable {J : Type p} (Φ : J → Type u) [∀ j, TopologicalSpace (Φ j)]
  {I : Type t} (X : I → Type v) [∀ i, TopologicalSpace (X i)]

/-- Refine the dependent product of the coordinate counits. -/
def piForward :
    C(WithGeneratedByTopology Φ (∀ i, WithGeneratedByTopology Φ (X i)),
      WithGeneratedByTopology Φ (∀ i, X i)) :=
  mapContinuousMap Φ (ContinuousMap.piMap (fun i => counitContinuousMap Φ (X i)))

/-- Lift the family of refined original evaluations from the generated source. -/
def piBackward :
    C(WithGeneratedByTopology Φ (∀ i, X i),
      WithGeneratedByTopology Φ (∀ i, WithGeneratedByTopology Φ (X i))) :=
  generatedSourceLift Φ (ContinuousMap.pi (fun i =>
    mapContinuousMap Φ (ContinuousMap.eval i : C((i : I) → X i, X i))))

@[simp]
theorem piForward_apply
    (x : WithGeneratedByTopology Φ (∀ i, WithGeneratedByTopology Φ (X i))) :
    piForward Φ X x = (equiv (X := Φ) (Y := ∀ i, X i)).symm
      (fun i => equiv ((equiv (X := Φ)
        (Y := ∀ i, WithGeneratedByTopology Φ (X i)) x) i)) := by
  exact mapContinuousMap_apply Φ
    (ContinuousMap.piMap (fun i => counitContinuousMap Φ (X i))) x

@[simp]
theorem piBackward_apply (x : WithGeneratedByTopology Φ (∀ i, X i)) :
    piBackward Φ X x =
      (equiv (X := Φ) (Y := ∀ i, WithGeneratedByTopology Φ (X i))).symm
        (fun i => mapContinuousMap Φ
          (ContinuousMap.eval i : C((i : I) → X i, X i)) x) := by
  exact generatedSourceLift_apply Φ (ContinuousMap.pi (fun i =>
    mapContinuousMap Φ (ContinuousMap.eval i : C((i : I) → X i, X i)))) x

/-- The forward comparison forgets the refinement in every coordinate. -/
theorem equiv_piForward_apply
    (x : WithGeneratedByTopology Φ (∀ i, WithGeneratedByTopology Φ (X i))) :
    equiv (piForward Φ X x) = fun i => equiv ((equiv x) i) := by
  rw [piForward_apply, Equiv.apply_symm_apply]

/-- The reverse comparison is the family of refined original evaluations. -/
theorem equiv_piBackward_apply (x : WithGeneratedByTopology Φ (∀ i, X i)) :
    equiv (piBackward Φ X x) = fun i => mapContinuousMap Φ
      (ContinuousMap.eval i : C((i : I) → X i, X i)) x := by
  rw [piBackward_apply, Equiv.apply_symm_apply]

/-- A coordinate of the forward comparison is the coordinate counit. -/
theorem piForward_eval_apply
    (x : WithGeneratedByTopology Φ (∀ i, WithGeneratedByTopology Φ (X i))) (i : I) :
    (equiv (piForward Φ X x)) i = equiv ((equiv x) i) := by
  rw [equiv_piForward_apply]

/-- A refined coordinate of the reverse comparison is the refined evaluation. -/
theorem piBackward_eval_apply (x : WithGeneratedByTopology Φ (∀ i, X i)) (i : I) :
    (equiv (piBackward Φ X x)) i = mapContinuousMap Φ
      (ContinuousMap.eval i : C((i : I) → X i, X i)) x := by
  rw [equiv_piBackward_apply]

/-- The reverse comparison preserves every original coordinate value. -/
theorem equiv_piBackward_eval_apply
    (x : WithGeneratedByTopology Φ (∀ i, X i)) (i : I) :
    equiv ((equiv (piBackward Φ X x)) i) = (equiv x) i := by
  simp

/-- The forward comparison commutes with the original-product counit. -/
theorem piForward_counit :
    (counitContinuousMap Φ (∀ i, X i)).comp (piForward Φ X) =
      (ContinuousMap.piMap (fun i => counitContinuousMap Φ (X i))).comp
        (counitContinuousMap Φ (∀ i, WithGeneratedByTopology Φ (X i))) := by
  exact mapContinuousMap_counit Φ
    (ContinuousMap.piMap (fun i => counitContinuousMap Φ (X i)))

/-- The reverse counit is the family of refined original evaluations. -/
theorem piBackward_counit :
    (counitContinuousMap Φ (∀ i, WithGeneratedByTopology Φ (X i))).comp
        (piBackward Φ X) =
      ContinuousMap.pi (fun i => mapContinuousMap Φ
        (ContinuousMap.eval i : C((i : I) → X i, X i))) := by
  exact generatedSourceLift_counit Φ (ContinuousMap.pi (fun i =>
    mapContinuousMap Φ (ContinuousMap.eval i : C((i : I) → X i, X i))))

/-- Refined evaluation after the forward comparison is source evaluation. -/
theorem piForward_eval (i : I) :
    (mapContinuousMap Φ (ContinuousMap.eval i : C((i : I) → X i, X i))).comp
        (piForward Φ X) =
      (ContinuousMap.eval i :
        C((i : I) → WithGeneratedByTopology Φ (X i), WithGeneratedByTopology Φ (X i))).comp
        (counitContinuousMap Φ (∀ i, WithGeneratedByTopology Φ (X i))) := by
  apply ContinuousMap.ext
  intro x
  apply (equiv (X := Φ) (Y := X i)).injective
  simp [ContinuousMap.comp_apply, counitContinuousMap_apply]

/-- Evaluation of the reverse counit is the refined original evaluation. -/
theorem piBackward_eval (i : I) :
    (ContinuousMap.eval i :
        C((i : I) → WithGeneratedByTopology Φ (X i), WithGeneratedByTopology Φ (X i))).comp
        ((counitContinuousMap Φ (∀ i, WithGeneratedByTopology Φ (X i))).comp
          (piBackward Φ X)) =
      mapContinuousMap Φ (ContinuousMap.eval i : C((i : I) → X i, X i)) := by
  apply ContinuousMap.ext
  intro x
  simp [ContinuousMap.comp_apply, counitContinuousMap_apply]

/-- The reverse comparison is a left inverse of the forward comparison. -/
theorem piBackward_comp_piForward :
    (piBackward Φ X).comp (piForward Φ X) =
      ContinuousMap.id
        (WithGeneratedByTopology Φ (∀ i, WithGeneratedByTopology Φ (X i))) := by
  apply ContinuousMap.ext
  intro x
  apply (equiv (X := Φ) (Y := ∀ i, WithGeneratedByTopology Φ (X i))).injective
  funext i
  apply (equiv (X := Φ) (Y := X i)).injective
  simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply] using
    (equiv_piBackward_eval_apply Φ X (piForward Φ X x) i).trans
      (piForward_eval_apply Φ X x i)

/-- The forward comparison is a left inverse of the reverse comparison. -/
theorem piForward_comp_piBackward :
    (piForward Φ X).comp (piBackward Φ X) =
      ContinuousMap.id (WithGeneratedByTopology Φ (∀ i, X i)) := by
  apply ContinuousMap.ext
  intro x
  apply (equiv (X := Φ) (Y := ∀ i, X i)).injective
  funext i
  simpa only [ContinuousMap.comp_apply, ContinuousMap.id_apply] using
    (piForward_eval_apply Φ X (piBackward Φ X x) i).trans
      (equiv_piBackward_eval_apply Φ X x i)

/-- The canonical homeomorphism between the two refined dependent products. -/
def piHomeomorph :
    WithGeneratedByTopology Φ (∀ i, WithGeneratedByTopology Φ (X i)) ≃ₜ
      WithGeneratedByTopology Φ (∀ i, X i) := by
  exact
    { toEquiv :=
        { toFun := piForward Φ X
          invFun := piBackward Φ X
          left_inv := fun x => DFunLike.congr_fun (piBackward_comp_piForward Φ X) x
          right_inv := fun x => DFunLike.congr_fun (piForward_comp_piBackward Φ X) x }
      continuous_toFun := (piForward Φ X).continuous
      continuous_invFun := (piBackward Φ X).continuous }

/-- The comparison homeomorphism has the prescribed forward continuous map. -/
theorem piHomeomorph_toContinuousMap :
    toContinuousMap (piHomeomorph Φ X) = piForward Φ X := by
  rfl

/-- The inverse comparison homeomorphism has the prescribed reverse continuous map. -/
theorem piHomeomorph_symm_toContinuousMap :
    toContinuousMap ((piHomeomorph Φ X).symm) = piBackward Φ X := by
  rfl

variable {Y : I → Type w} [∀ i, TopologicalSpace (Y i)]

/-- The forward comparison is natural in the entire original family. -/
theorem piForward_naturality (f : ∀ i, C(X i, Y i)) :
    (piForward Φ Y).comp
        (mapContinuousMap Φ (ContinuousMap.piMap (fun i => mapContinuousMap Φ (f i)))) =
      (mapContinuousMap Φ (ContinuousMap.piMap f)).comp (piForward Φ X) := by
  apply ContinuousMap.ext
  intro x
  apply (equiv (X := Φ) (Y := ∀ i, Y i)).injective
  funext i
  simp [ContinuousMap.comp_apply]

/-- The reverse comparison is natural in the entire original family. -/
theorem piBackward_naturality (f : ∀ i, C(X i, Y i)) :
    (piBackward Φ Y).comp (mapContinuousMap Φ (ContinuousMap.piMap f)) =
      (mapContinuousMap Φ (ContinuousMap.piMap (fun i => mapContinuousMap Φ (f i)))).comp
        (piBackward Φ X) := by
  apply ContinuousMap.ext
  intro x
  have hright : piForward Φ X (piBackward Φ X x) = x :=
    DFunLike.congr_fun (piForward_comp_piBackward Φ X) x
  have hleft (y : WithGeneratedByTopology Φ (∀ i, WithGeneratedByTopology Φ (Y i))) :
      piBackward Φ Y (piForward Φ Y y) = y :=
    DFunLike.congr_fun (piBackward_comp_piForward Φ Y) y
  have h := congrArg (piBackward Φ Y)
    (DFunLike.congr_fun (piForward_naturality Φ X f) (piBackward Φ X x))
  simpa only [ContinuousMap.comp_apply, hright, hleft] using h.symm

/-- The comparison homeomorphism is natural in the entire original family. -/
theorem piHomeomorph_naturality (f : ∀ i, C(X i, Y i)) :
    (toContinuousMap (piHomeomorph Φ Y)).comp
        (mapContinuousMap Φ (ContinuousMap.piMap (fun i => mapContinuousMap Φ (f i)))) =
      (mapContinuousMap Φ (ContinuousMap.piMap f)).comp
        (toContinuousMap (piHomeomorph Φ X)) := by
  simpa only [piHomeomorph_toContinuousMap] using piForward_naturality Φ X f

/-- The inverse comparison homeomorphism is natural in the entire original family. -/
theorem piHomeomorph_symm_naturality (f : ∀ i, C(X i, Y i)) :
    (toContinuousMap ((piHomeomorph Φ Y).symm)).comp
        (mapContinuousMap Φ (ContinuousMap.piMap f)) =
      (mapContinuousMap Φ (ContinuousMap.piMap (fun i => mapContinuousMap Φ (f i)))).comp
        (toContinuousMap ((piHomeomorph Φ X).symm)) := by
  simpa only [piHomeomorph_symm_toContinuousMap] using piBackward_naturality Φ X f

/-- Pair evaluation intertwines the forward dependent-product and binary comparisons. -/
theorem piForward_pair_eval (i j : I) :
    (prodForward Φ (X i) (X j)).comp
        (mapContinuousMap Φ
          ((ContinuousMap.eval i :
              C((k : I) → WithGeneratedByTopology Φ (X k), WithGeneratedByTopology Φ (X i))).prodMk
            (ContinuousMap.eval j :
              C((k : I) → WithGeneratedByTopology Φ (X k), WithGeneratedByTopology Φ (X j))))) =
      (mapContinuousMap Φ
        ((ContinuousMap.eval i : C((k : I) → X k, X i)).prodMk
          (ContinuousMap.eval j : C((k : I) → X k, X j)))).comp (piForward Φ X) := by
  apply ContinuousMap.ext
  intro x
  apply (equiv (X := Φ) (Y := X i × X j)).injective
  apply Prod.ext
  · simp [ContinuousMap.comp_apply, prodForward_apply, Equiv.apply_symm_apply]
  · simp [ContinuousMap.comp_apply, prodForward_apply, Equiv.apply_symm_apply]

/-- Pair evaluation intertwines the reverse dependent-product and binary comparisons. -/
theorem piBackward_pair_eval (i j : I) :
    (prodBackward Φ (X i) (X j)).comp
        (mapContinuousMap Φ
          ((ContinuousMap.eval i : C((k : I) → X k, X i)).prodMk
            (ContinuousMap.eval j : C((k : I) → X k, X j)))) =
      (mapContinuousMap Φ
        ((ContinuousMap.eval i :
            C((k : I) → WithGeneratedByTopology Φ (X k), WithGeneratedByTopology Φ (X i))).prodMk
          (ContinuousMap.eval j :
            C((k : I) → WithGeneratedByTopology Φ (X k), WithGeneratedByTopology Φ (X j))))).comp
        (piBackward Φ X) := by
  apply ContinuousMap.ext
  intro x
  have hright : piForward Φ X (piBackward Φ X x) = x :=
    DFunLike.congr_fun (piForward_comp_piBackward Φ X) x
  have hleft (y : WithGeneratedByTopology Φ
      (WithGeneratedByTopology Φ (X i) × WithGeneratedByTopology Φ (X j))) :
      prodBackward Φ (X i) (X j) (prodForward Φ (X i) (X j) y) = y :=
    DFunLike.congr_fun (prodBackward_comp_prodForward Φ (X i) (X j)) y
  have h := congrArg (prodBackward Φ (X i) (X j))
    (DFunLike.congr_fun (piForward_pair_eval Φ X i j) (piBackward Φ X x))
  simpa only [ContinuousMap.comp_apply, hright, hleft] using h.symm

end Topology.WithGeneratedByTopology
