/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Convenient.GeneratedBy.Basic

/-!
# Canonical products of generated-by refinements

For an arbitrary fixed family of probes, refining the product of the two refined
original spaces is canonically homeomorphic to refining their original product.
The comparison uses the product of the ordinary counits in the forward direction,
and the generated-source lift of the pair of refined projections in the reverse
direction. No condition on either original space or on products of probes is needed.
-/

@[expose] public section

noncomputable section

universe t u v w v' w'

open Topology

namespace Topology.WithGeneratedByTopology

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
  (A : Type v) [TopologicalSpace A] (B : Type w) [TopologicalSpace B]

/-- Refine the product of the ordinary counits. -/
def prodForward :
    C(WithGeneratedByTopology X
        (WithGeneratedByTopology X A × WithGeneratedByTopology X B),
      WithGeneratedByTopology X (A × B)) :=
  mapContinuousMap X ((counitContinuousMap X A).prodMap (counitContinuousMap X B))

/-- Lift the pair of refined projections from the generated refined product. -/
def prodBackward :
    C(WithGeneratedByTopology X (A × B),
      WithGeneratedByTopology X
        (WithGeneratedByTopology X A × WithGeneratedByTopology X B)) :=
  generatedSourceLift X
    ((mapContinuousMap X (ContinuousMap.fst : C(A × B, A))).prodMk
      (mapContinuousMap X (ContinuousMap.snd : C(A × B, B))))

@[simp]
theorem prodForward_apply
    (p : WithGeneratedByTopology X
      (WithGeneratedByTopology X A × WithGeneratedByTopology X B)) :
    prodForward X A B p = (equiv (X := X) (Y := A × B)).symm
      (equiv ((equiv (X := X)
        (Y := WithGeneratedByTopology X A × WithGeneratedByTopology X B) p).1),
       equiv ((equiv (X := X)
        (Y := WithGeneratedByTopology X A × WithGeneratedByTopology X B) p).2)) := by
  exact mapContinuousMap_apply X
    ((counitContinuousMap X A).prodMap (counitContinuousMap X B)) p

@[simp]
theorem prodBackward_apply (p : WithGeneratedByTopology X (A × B)) :
    prodBackward X A B p =
      (equiv (X := X)
        (Y := WithGeneratedByTopology X A × WithGeneratedByTopology X B)).symm
        (mapContinuousMap X (ContinuousMap.fst : C(A × B, A)) p,
         mapContinuousMap X (ContinuousMap.snd : C(A × B, B)) p) := by
  simp only [prodBackward, generatedSourceLift_apply, ContinuousMap.prod_eval]

/-- The forward map commutes with the original-product counit. -/
theorem prodForward_counit :
    (counitContinuousMap X (A × B)).comp (prodForward X A B) =
      ((counitContinuousMap X A).prodMap (counitContinuousMap X B)).comp
        (counitContinuousMap X
          (WithGeneratedByTopology X A × WithGeneratedByTopology X B)) := by
  apply ContinuousMap.ext
  intro p
  simp only [ContinuousMap.comp_apply, counitContinuousMap_apply,
    prodForward_apply, Equiv.apply_symm_apply]
  rfl

/-- The counit of the reverse map is the pair of refined projections. -/
theorem prodBackward_counit :
    (counitContinuousMap X
        (WithGeneratedByTopology X A × WithGeneratedByTopology X B)).comp
        (prodBackward X A B) =
      (mapContinuousMap X (ContinuousMap.fst : C(A × B, A))).prodMk
        (mapContinuousMap X (ContinuousMap.snd : C(A × B, B))) := by
  apply ContinuousMap.ext
  intro p
  simp only [ContinuousMap.comp_apply, counitContinuousMap_apply,
    prodBackward_apply, Equiv.apply_symm_apply, ContinuousMap.prod_eval]

/-- The first refined projection of the forward comparison is the source projection. -/
theorem prodForward_fst :
    (mapContinuousMap X (ContinuousMap.fst : C(A × B, A))).comp
        (prodForward X A B) =
      (ContinuousMap.fst :
        C(WithGeneratedByTopology X A × WithGeneratedByTopology X B,
          WithGeneratedByTopology X A)).comp
        (counitContinuousMap X
          (WithGeneratedByTopology X A × WithGeneratedByTopology X B)) := by
  apply ContinuousMap.ext
  intro p
  apply (equiv (X := X) (Y := A)).injective
  simp only [ContinuousMap.comp_apply, equiv_mapContinuousMap,
    prodForward_apply, Equiv.apply_symm_apply, counitContinuousMap_apply]
  rfl

/-- The second refined projection of the forward comparison is the source projection. -/
theorem prodForward_snd :
    (mapContinuousMap X (ContinuousMap.snd : C(A × B, B))).comp
        (prodForward X A B) =
      (ContinuousMap.snd :
        C(WithGeneratedByTopology X A × WithGeneratedByTopology X B,
          WithGeneratedByTopology X B)).comp
        (counitContinuousMap X
          (WithGeneratedByTopology X A × WithGeneratedByTopology X B)) := by
  apply ContinuousMap.ext
  intro p
  apply (equiv (X := X) (Y := B)).injective
  simp only [ContinuousMap.comp_apply, equiv_mapContinuousMap,
    prodForward_apply, Equiv.apply_symm_apply, counitContinuousMap_apply]
  rfl

/-- The first coordinate of the reverse counit is the refined first projection. -/
theorem prodBackward_fst :
    (ContinuousMap.fst :
        C(WithGeneratedByTopology X A × WithGeneratedByTopology X B,
          WithGeneratedByTopology X A)).comp
        ((counitContinuousMap X
          (WithGeneratedByTopology X A × WithGeneratedByTopology X B)).comp
            (prodBackward X A B)) =
      mapContinuousMap X (ContinuousMap.fst : C(A × B, A)) := by
  apply ContinuousMap.ext
  intro p
  simp only [ContinuousMap.comp_apply, counitContinuousMap_apply,
    prodBackward_apply, Equiv.apply_symm_apply]
  rfl

/-- The second coordinate of the reverse counit is the refined second projection. -/
theorem prodBackward_snd :
    (ContinuousMap.snd :
        C(WithGeneratedByTopology X A × WithGeneratedByTopology X B,
          WithGeneratedByTopology X B)).comp
        ((counitContinuousMap X
          (WithGeneratedByTopology X A × WithGeneratedByTopology X B)).comp
            (prodBackward X A B)) =
      mapContinuousMap X (ContinuousMap.snd : C(A × B, B)) := by
  apply ContinuousMap.ext
  intro p
  simp only [ContinuousMap.comp_apply, counitContinuousMap_apply,
    prodBackward_apply, Equiv.apply_symm_apply]
  rfl

/-- The reverse comparison is a left inverse of the forward comparison. -/
theorem prodBackward_comp_prodForward :
    (prodBackward X A B).comp (prodForward X A B) =
      ContinuousMap.id (WithGeneratedByTopology X
        (WithGeneratedByTopology X A × WithGeneratedByTopology X B)) := by
  apply ContinuousMap.ext
  intro p
  apply (equiv (X := X)
    (Y := WithGeneratedByTopology X A × WithGeneratedByTopology X B)).injective
  simp [prodForward_apply, prodBackward_apply]

/-- The forward comparison is a left inverse of the reverse comparison. -/
theorem prodForward_comp_prodBackward :
    (prodForward X A B).comp (prodBackward X A B) =
      ContinuousMap.id (WithGeneratedByTopology X (A × B)) := by
  apply ContinuousMap.ext
  intro p
  apply (equiv (X := X) (Y := A × B)).injective
  simp [prodForward_apply, prodBackward_apply]

/-- The canonical comparison between the twice-refined and original-refined products. -/
def prodHomeomorph :
    WithGeneratedByTopology X
        (WithGeneratedByTopology X A × WithGeneratedByTopology X B) ≃ₜ
      WithGeneratedByTopology X (A × B) := by
  exact
    { toEquiv :=
        { toFun := prodForward X A B
          invFun := prodBackward X A B
          left_inv := fun p =>
            DFunLike.congr_fun (prodBackward_comp_prodForward X A B) p
          right_inv := fun p =>
            DFunLike.congr_fun (prodForward_comp_prodBackward X A B) p }
      continuous_toFun := (prodForward X A B).continuous
      continuous_invFun := (prodBackward X A B).continuous }

/-- The comparison homeomorphism has the prescribed forward continuous map. -/
theorem prodHomeomorph_toContinuousMap :
    toContinuousMap (prodHomeomorph X A B) = prodForward X A B := by
  rfl

/-- The inverse comparison homeomorphism has the prescribed reverse continuous map. -/
theorem prodHomeomorph_symm_toContinuousMap :
    toContinuousMap ((prodHomeomorph X A B).symm) = prodBackward X A B := by
  rfl

variable {A' : Type v'} [TopologicalSpace A'] {B' : Type w'} [TopologicalSpace B']

/-- The forward comparison is natural in both original coordinates. -/
theorem prodForward_naturality (f : C(A, A')) (g : C(B, B')) :
    (prodForward X A' B').comp
        (mapContinuousMap X ((mapContinuousMap X f).prodMap (mapContinuousMap X g))) =
      (mapContinuousMap X (f.prodMap g)).comp (prodForward X A B) := by
  apply ContinuousMap.ext
  intro p
  apply (equiv (X := X) (Y := A' × B')).injective
  simp [prodForward_apply]

/-- The reverse comparison is natural in both original coordinates. -/
theorem prodBackward_naturality (f : C(A, A')) (g : C(B, B')) :
    (prodBackward X A' B').comp (mapContinuousMap X (f.prodMap g)) =
      (mapContinuousMap X ((mapContinuousMap X f).prodMap (mapContinuousMap X g))).comp
        (prodBackward X A B) := by
  apply ContinuousMap.ext
  intro p
  have hright : prodForward X A B (prodBackward X A B p) = p :=
    DFunLike.congr_fun (prodForward_comp_prodBackward X A B) p
  have hleft (q : WithGeneratedByTopology X
      (WithGeneratedByTopology X A' × WithGeneratedByTopology X B')) :
      prodBackward X A' B' (prodForward X A' B' q) = q :=
    DFunLike.congr_fun (prodBackward_comp_prodForward X A' B') q
  have h := congrArg (prodBackward X A' B')
    (DFunLike.congr_fun (prodForward_naturality X A B f g)
      (prodBackward X A B p))
  simpa only [ContinuousMap.comp_apply, hright, hleft] using h.symm

/-- The homeomorphism comparison is natural in both original coordinates. -/
theorem prodHomeomorph_naturality (f : C(A, A')) (g : C(B, B')) :
    (toContinuousMap (prodHomeomorph X A' B')).comp
        (mapContinuousMap X ((mapContinuousMap X f).prodMap (mapContinuousMap X g))) =
      (mapContinuousMap X (f.prodMap g)).comp
        (toContinuousMap (prodHomeomorph X A B)) := by
  simpa only [prodHomeomorph_toContinuousMap] using
    prodForward_naturality X A B f g

/-- The inverse homeomorphism comparison is natural in both original coordinates. -/
theorem prodHomeomorph_symm_naturality (f : C(A, A')) (g : C(B, B')) :
    (toContinuousMap ((prodHomeomorph X A' B').symm)).comp
        (mapContinuousMap X (f.prodMap g)) =
      (mapContinuousMap X ((mapContinuousMap X f).prodMap (mapContinuousMap X g))).comp
        (toContinuousMap ((prodHomeomorph X A B).symm)) := by
  simpa only [prodHomeomorph_symm_toContinuousMap] using
    prodBackward_naturality X A B f g

end Topology.WithGeneratedByTopology
