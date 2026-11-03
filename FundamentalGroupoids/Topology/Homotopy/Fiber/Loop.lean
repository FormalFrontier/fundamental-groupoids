/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber.Const
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Contractible
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Homotopy
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

The retained-point projection of the loop inclusion is constant. The loop
inclusion after the original map on loops contracts by shortening the source
loop, relative to the constant loop. This is obtained from `idContraction` by
precomposition and the induced map of homotopy fibers. The retained-path
homotopy also nullhomotopes the original map after the retained-point projection,
relative to each specified constant-path point.

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

/-- The retained-path homotopy fixes the constant-path point throughout. -/
def pathHomotopyRel (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    (ContinuousMap.const (HomotopyFiber f b) b).HomotopyRel
      (f.comp (point (f := f) (b := b))) {const e₀ h} where
  toHomotopy := pathHomotopy f b
  prop' t z hz := by
    have hz' : z = const e₀ h := Set.mem_singleton_iff.mp hz
    subst z
    rfl

/-- The relative homotopy evaluates the whole retained path at its time parameter. -/
theorem pathHomotopyRel_apply (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (t : unitInterval) (z : HomotopyFiber f b) :
    pathHomotopyRel f b e₀ h (t, z) = path z t :=
  rfl

/-- The composite of the retained-point projection with the original map is
nullhomotopic relative to the specified constant-path point. -/
theorem homotopicRel_comp_point_const (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) :
    (f.comp (point (f := f) (b := b))).HomotopicRel
      (ContinuousMap.const (HomotopyFiber f b) b) {const e₀ h} :=
  ⟨(pathHomotopyRel f b e₀ h).symm⟩

/-- Projecting the loop inclusion to its retained point is the constant map. -/
theorem point_comp_loopInclusion (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    (point (f := f) (b := b)).comp (loopInclusion f b e₀ h) =
      ContinuousMap.const (Path b b) e₀ := by
  ext γ
  rfl

/-- Contract the loop inclusion of the mapped loop by shortening the source loop,
fixing the constant loop throughout. -/
noncomputable def loopInclusionCompLoopMapHomotopy
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    ((loopInclusion f b e₀ h).comp (f.loopMap e₀ b h)).HomotopyRel
      (ContinuousMap.const (Path e₀ e₀) (const (f := f) e₀ h))
      {Path.refl e₀} := by
  let F : C(HomotopyFiber (ContinuousMap.id E) e₀, HomotopyFiber f b) :=
    map (ContinuousMap.id E) f (fun _ => rfl) h
  let L := loopInclusion (ContinuousMap.id E) e₀ e₀ rfl
  have hL : Set.MapsTo L {Path.refl e₀}
      {const (f := ContinuousMap.id E) e₀ rfl} := by
    intro γ hγ
    have hγ' : γ = Path.refl e₀ := Set.mem_singleton_iff.mp hγ
    subst γ
    exact Set.mem_singleton_iff.mpr
      (loopInclusion_refl (ContinuousMap.id E) e₀ e₀ rfl)
  let H := ((idContraction e₀).precomp L hL).compContinuousMap F
  refine H.cast ?_ ?_
  · apply ContinuousMap.ext
    intro γ
    apply ext
    · rfl
    · apply ContinuousMap.ext
      intro s
      rfl
  · apply ContinuousMap.ext
    intro γ
    change F (const (f := ContinuousMap.id E) e₀ rfl) = const e₀ h
    exact map_const_of_point_eq (ContinuousMap.id E) f (fun _ => rfl) h
      e₀ e₀ rfl h rfl

/-- The point coordinate of the contraction follows the source loop backwards. -/
theorem point_loopInclusionCompLoopMapHomotopy
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (t : unitInterval) (γ : Path e₀ e₀) :
    point (loopInclusionCompLoopMapHomotopy f b e₀ h (t, γ)) =
      γ (unitInterval.symm t) := by
  change point
    (map (f := ContinuousMap.id E) (f' := f) (b := e₀) (b' := b)
      (ContinuousMap.id E) f (fun _ => rfl) h
      (idContraction e₀ (t, loopInclusion (ContinuousMap.id E) e₀ e₀ rfl γ))) = _
  simp only [point_map, ContinuousMap.id_apply]
  exact (point_idContraction e₀ t
    (loopInclusion (ContinuousMap.id E) e₀ e₀ rfl γ)).trans
      ((eval_apply (unitInterval.symm t)
        (loopInclusion (ContinuousMap.id E) e₀ e₀ rfl γ)).trans
          (loopInclusion_path_apply (ContinuousMap.id E) e₀ e₀ rfl γ
            (unitInterval.symm t)))

/-- Every time value of the contracted path is the mapped source-loop prefix. -/
theorem path_loopInclusionCompLoopMapHomotopy_apply
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (t : unitInterval) (γ : Path e₀ e₀) (s : unitInterval) :
    path (loopInclusionCompLoopMapHomotopy f b e₀ h (t, γ)) s =
      f (γ (unitInterval.symm t * s)) := by
  change f (path
    (idContraction e₀ (t, loopInclusion (ContinuousMap.id E) e₀ e₀ rfl γ)) s) = _
  rw [path_idContraction_apply]
  rfl

/-- The loop inclusion after the loop map is nullhomotopic relative to the
constant source loop. -/
theorem homotopicRel_loopInclusion_comp_loopMap_const
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    ((loopInclusion f b e₀ h).comp (f.loopMap e₀ b h)).HomotopicRel
      (ContinuousMap.const (Path e₀ e₀) (const (f := f) e₀ h))
      {Path.refl e₀} :=
  ⟨loopInclusionCompLoopMapHomotopy f b e₀ h⟩

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
