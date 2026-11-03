/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber.Const
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Naturality of the loop inclusion into a homotopy fiber

A point `e₀` with `f e₀ = b` determines a continuous map from loops at `b` to the
homotopy fiber of `f` over `b`. It is the composite through the homotopy fiber of
the constant map from `Unit`: a loop first acquires the source coordinate `()`,
then passes through `constHomeomorph.symm`, and finally through `HomotopyFiber.map`.
The resulting fiber point retains `e₀` and the entire forward loop.

This inclusion is natural under continuous commutative squares preserving the
separately specified source and target points. The action on loops is the
continuous based postcomposition transported through `genLoopHomeoOfUnique`.
Both sides retain the specified target source point, and their paths evaluate
to the postcomposed loop at every time. The latter assertion needs no equality
between the specified source points.

Only the ordinary compact-open and subspace topologies are used, with no
separation or local compactness assumptions on the spaces.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, §6, p. 61,
  for the homotopy-fiber construction.
* Mathlib's fixed-endpoint paths (Patrick Massot), compact-open continuous maps
  (Reid Barton), and generalized loops (Roberto Alvarez), together with the
  based-postcomposition and singleton-loop-homeomorphism APIs.
-/

@[expose] public section

open scoped Topology

namespace ContinuousMap.HomotopyFiber

universe uE uB uE' uB'

variable {E : Type uE} {B : Type uB} {E' : Type uE'} {B' : Type uB'}
variable [TopologicalSpace E] [TopologicalSpace B]
variable [TopologicalSpace E'] [TopologicalSpace B']
variable {f : C(E, B)} {f' : C(E', B')} {b : B} {b' : B'}

/-- The forward loop inclusion into the ordinary homotopy fiber at a specified
source point, retaining the loop with its original direction. -/
noncomputable def loopInclusion (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    C(Path b b, HomotopyFiber f b) :=
  (map
    (f := ContinuousMap.const Unit b) (f' := f)
    (b := b) (b' := b)
    (ContinuousMap.const Unit e₀) (ContinuousMap.id B)
    (fun _ => h) rfl).comp
      (((constHomeomorph Unit b b).symm :
          C(Unit × Path b b, HomotopyFiber (ContinuousMap.const Unit b) b)).comp
        ((ContinuousMap.const (Path b b) ()).prodMk
          (ContinuousMap.id (Path b b))))

/-- The loop inclusion retains the specified source point and the entire forward loop. -/
theorem loopInclusion_apply (e₀ : E) (h : f e₀ = b) (γ : Path b b) :
    let J : C(Path b b, HomotopyFiber f b) :=
      (map
        (f := ContinuousMap.const Unit b) (f' := f)
        (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B)
        (fun _ => h) rfl).comp
          (((constHomeomorph Unit b b).symm :
              C(Unit × Path b b,
                HomotopyFiber (ContinuousMap.const Unit b) b)).comp
            ((ContinuousMap.const (Path b b) ()).prodMk
              (ContinuousMap.id (Path b b))))
    J γ = mk (f := f) (b := b)
      e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm) :=
  rfl

/-- The loop inclusion retains its specified source point. -/
@[simp]
theorem loopInclusion_point (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (γ : Path b b) :
    point (loopInclusion f b e₀ h γ) = e₀ :=
  rfl

/-- The path coordinate of the loop inclusion is the entire original loop. -/
@[simp]
theorem loopInclusion_path (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (γ : Path b b) :
    path (loopInclusion f b e₀ h γ) = γ.toContinuousMap :=
  rfl

/-- Every time value of the loop inclusion is the original loop value. -/
theorem loopInclusion_path_apply (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (γ : Path b b) (t : unitInterval) :
    path (loopInclusion f b e₀ h γ) t = γ t :=
  rfl

/-- The constant loop gives the specified constant-path point of the homotopy fiber. -/
@[simp]
theorem loopInclusion_refl (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    loopInclusion f b e₀ h (Path.refl b) = const (f := f) (b := b) e₀ h :=
  loopInclusion_apply e₀ h (Path.refl b)

/-- Both routes around the loop-inclusion square retain the separately specified
source point of the target homotopy fiber. -/
theorem loopInclusion_naturality_point
    (α : C(E, E')) (β : C(B, B'))
    (w : ∀ e, f' (α e) = β (f e))
    (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') :
    let J : C(Path b b, HomotopyFiber f b) :=
      (map
        (f := ContinuousMap.const Unit b) (f' := f)
        (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B)
        (fun _ => h) rfl).comp
          (((constHomeomorph Unit b b).symm :
              C(Unit × Path b b,
                HomotopyFiber (ContinuousMap.const Unit b) b)).comp
            ((ContinuousMap.const (Path b b) ()).prodMk
              (ContinuousMap.id (Path b b))))
    let J' : C(Path b' b', HomotopyFiber f' b') :=
      (map
        (f := ContinuousMap.const Unit b') (f' := f')
        (b := b') (b' := b')
        (ContinuousMap.const Unit e₀') (ContinuousMap.id B')
        (fun _ => h') rfl).comp
          (((constHomeomorph Unit b' b').symm :
              C(Unit × Path b' b',
                HomotopyFiber (ContinuousMap.const Unit b') b')).comp
            ((ContinuousMap.const (Path b' b') ()).prodMk
              (ContinuousMap.id (Path b' b'))))
    let Pβ : C(Path b b, Path b' b') :=
      (genLoopHomeoOfUnique Unit b' : C(GenLoop Unit B' b', Path b' b')).comp
        ((⟨GenLoop.map β hb, GenLoop.continuous_map β hb⟩ :
            C(GenLoop Unit B b, GenLoop Unit B' b')).comp
          ((genLoopHomeoOfUnique Unit b).symm :
            C(Path b b, GenLoop Unit B b)))
    let φ : C(HomotopyFiber f b, HomotopyFiber f' b') :=
      map α β w hb
    ∀ γ : Path b b,
      point (φ (J γ)) = e₀' ∧ point (J' (Pβ γ)) = e₀' := by
  intro J J' Pβ φ γ
  constructor
  · calc
      point (φ (J γ)) = α (point (J γ)) := point_map α β w hb (J γ)
      _ = e₀' := by rw [loopInclusion_apply e₀ h γ, point_mk, he]
  · rw [loopInclusion_apply e₀' h' (Pβ γ), point_mk]

/-- At every time, both routes around the loop-inclusion square evaluate to the
postcomposed loop. No equality of the specified source points is needed. -/
theorem loopInclusion_naturality_eval
    (α : C(E, E')) (β : C(B, B'))
    (w : ∀ e, f' (α e) = β (f e))
    (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (hb : β b = b') :
    let J : C(Path b b, HomotopyFiber f b) :=
      (map
        (f := ContinuousMap.const Unit b) (f' := f)
        (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B)
        (fun _ => h) rfl).comp
          (((constHomeomorph Unit b b).symm :
              C(Unit × Path b b,
                HomotopyFiber (ContinuousMap.const Unit b) b)).comp
            ((ContinuousMap.const (Path b b) ()).prodMk
              (ContinuousMap.id (Path b b))))
    let J' : C(Path b' b', HomotopyFiber f' b') :=
      (map
        (f := ContinuousMap.const Unit b') (f' := f')
        (b := b') (b' := b')
        (ContinuousMap.const Unit e₀') (ContinuousMap.id B')
        (fun _ => h') rfl).comp
          (((constHomeomorph Unit b' b').symm :
              C(Unit × Path b' b',
                HomotopyFiber (ContinuousMap.const Unit b') b')).comp
            ((ContinuousMap.const (Path b' b') ()).prodMk
              (ContinuousMap.id (Path b' b'))))
    let Pβ : C(Path b b, Path b' b') :=
      (genLoopHomeoOfUnique Unit b' : C(GenLoop Unit B' b', Path b' b')).comp
        ((⟨GenLoop.map β hb, GenLoop.continuous_map β hb⟩ :
            C(GenLoop Unit B b, GenLoop Unit B' b')).comp
          ((genLoopHomeoOfUnique Unit b).symm :
            C(Path b b, GenLoop Unit B b)))
    let φ : C(HomotopyFiber f b, HomotopyFiber f' b') :=
      map α β w hb
    ∀ (γ : Path b b) (t : unitInterval),
      eval t (φ (J γ)) = β (γ t) ∧ eval t (J' (Pβ γ)) = β (γ t) := by
  intro J J' Pβ φ γ t
  have hPβ : Pβ γ = (γ.map β.continuous).cast hb.symm hb.symm :=
    (genLoopHomeoOfUnique_map Unit β hb
      ((genLoopHomeoOfUnique Unit b).symm γ)).trans
        (congrArg
          (fun η : Path b b => (η.map β.continuous).cast hb.symm hb.symm)
          ((genLoopHomeoOfUnique Unit b).apply_symm_apply γ))
  have hPβt : Pβ γ t = β (γ t) :=
    (congrArg (fun η : Path b' b' => η t) hPβ).trans rfl
  constructor
  · calc
      eval t (φ (J γ)) = β (eval t (J γ)) := eval_map α β w hb (J γ) t
      _ = β (γ t) := by
        rw [loopInclusion_apply e₀ h γ, eval_apply, path_mk]
        rfl
  · calc
      eval t (J' (Pβ γ)) = Pβ γ t := by
        rw [loopInclusion_apply e₀' h' (Pβ γ), eval_apply, path_mk]
        rfl
      _ = β (γ t) := hPβt

/-- The loop inclusion into the ordinary homotopy fiber is natural under a
continuous commutative square preserving the separately specified source and
target points. The loop action is continuous based postcomposition transported
through the singleton generalized-loop homeomorphisms. -/
theorem loopInclusion_naturality
    (α : C(E, E')) (β : C(B, B'))
    (w : ∀ e, f' (α e) = β (f e))
    (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') :
    let J : C(Path b b, HomotopyFiber f b) :=
      (map
        (f := ContinuousMap.const Unit b) (f' := f)
        (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B)
        (fun _ => h) rfl).comp
          (((constHomeomorph Unit b b).symm :
              C(Unit × Path b b,
                HomotopyFiber (ContinuousMap.const Unit b) b)).comp
            ((ContinuousMap.const (Path b b) ()).prodMk
              (ContinuousMap.id (Path b b))))
    let J' : C(Path b' b', HomotopyFiber f' b') :=
      (map
        (f := ContinuousMap.const Unit b') (f' := f')
        (b := b') (b' := b')
        (ContinuousMap.const Unit e₀') (ContinuousMap.id B')
        (fun _ => h') rfl).comp
          (((constHomeomorph Unit b' b').symm :
              C(Unit × Path b' b',
                HomotopyFiber (ContinuousMap.const Unit b') b')).comp
            ((ContinuousMap.const (Path b' b') ()).prodMk
              (ContinuousMap.id (Path b' b'))))
    let Pβ : C(Path b b, Path b' b') :=
      (genLoopHomeoOfUnique Unit b' : C(GenLoop Unit B' b', Path b' b')).comp
        ((⟨GenLoop.map β hb, GenLoop.continuous_map β hb⟩ :
            C(GenLoop Unit B b, GenLoop Unit B' b')).comp
          ((genLoopHomeoOfUnique Unit b).symm :
            C(Path b b, GenLoop Unit B b)))
    let φ : C(HomotopyFiber f b, HomotopyFiber f' b') :=
      map α β w hb
    φ.comp J = J'.comp Pβ := by
  intro J J' Pβ φ
  apply ContinuousMap.ext
  intro γ
  apply ext
  · have hp := loopInclusion_naturality_point α β w e₀ e₀' h h' he hb γ
    exact hp.1.trans hp.2.symm
  · apply ContinuousMap.ext
    intro t
    have hγ := loopInclusion_naturality_eval α β w e₀ e₀' h h' hb γ t
    exact hγ.1.trans hγ.2.symm

end ContinuousMap.HomotopyFiber
