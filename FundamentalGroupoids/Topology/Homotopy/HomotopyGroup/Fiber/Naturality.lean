/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber.Loop
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Iteration.Basic

/-!
# Naturality of higher homotopy-fiber connecting maps

The connecting function is the composite of inverse loop iteration in the order
`I ⊕ Unit`, based postcomposition by the singleton-loop homeomorphism to
`Path b b`, and based postcomposition by the forward loop inclusion into the
homotopy fiber. The fiber basepoint is the constant-path point associated to a
separately specified point `e₀` with `f e₀ = b`.

`HomotopyGroup.mapFun_homotopyFiber_loop_naturality` states that this composite
commutes with the maps induced by a continuous commutative square preserving the
specified source and target points. It is an equality of functions on all
homotopy classes. The cube index and the four spaces have independent universes;
no instance on the cube index is required, including when it is empty or infinite.

For `hb : β b = b'`, the singleton-loop homeomorphism identifies based
postcomposition with `γ ↦ (γ.map β.continuous).cast hb.symm hb.symm`.
Both endpoint casts retain the forward path, which evaluates to `β (γ t)` at
every time `t`. The loop inclusion retains the specified source point and this
entire path.

## Limitations

Only ordinary product, subspace and compact-open topologies are used. No group
structure on path components, sphere-based comparison, or long exact sequence is
asserted.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, §6, p. 61,
  for the homotopy-fiber construction and its loop inclusion.
* Mathlib's generalized loops and sum-flattening homeomorphism (Roberto Alvarez),
  fixed-endpoint paths (Patrick Massot), and compact-open continuous maps
  (Reid Barton), together with the based-postcomposition, singleton-loop and
  loop-inclusion naturality APIs.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace HomotopyGroup

universe uI uE uE' uB uB'

variable {E : Type uE} {E' : Type uE'} {B : Type uB} {B' : Type uB'}
variable [TopologicalSpace E] [TopologicalSpace E']
variable [TopologicalSpace B] [TopologicalSpace B']
variable {f : C(E, B)} {f' : C(E', B')} {b : B} {b' : B'}

/-- The higher connecting functions commute with a continuous commutative square
preserving the specified points. Each connecting function uses inverse ordered
`I, Unit` iteration, the singleton-loop homeomorphism, and the forward loop
inclusion into the homotopy fiber, based at its specified constant-path point.
The equality is on all classes and requires no instance on `I`. -/
theorem mapFun_homotopyFiber_loop_naturality
    (I : Type uI) (α : C(E, E')) (β : C(B, B'))
    (w : ∀ e, f' (α e) = β (f e))
    (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') :
    let z₀ : ContinuousMap.HomotopyFiber f b :=
      ContinuousMap.HomotopyFiber.const e₀ h
    let z₀' : ContinuousMap.HomotopyFiber f' b' :=
      ContinuousMap.HomotopyFiber.const e₀' h'
    let J : C(Path b b, ContinuousMap.HomotopyFiber f b) :=
      (ContinuousMap.HomotopyFiber.map
        (f := ContinuousMap.const Unit b) (f' := f)
        (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B)
        (fun _ => h) rfl).comp
          (((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm :
              C(Unit × Path b b,
                ContinuousMap.HomotopyFiber (ContinuousMap.const Unit b) b)).comp
            ((ContinuousMap.const (Path b b) ()).prodMk
              (ContinuousMap.id (Path b b))))
    let J' : C(Path b' b', ContinuousMap.HomotopyFiber f' b') :=
      (ContinuousMap.HomotopyFiber.map
        (f := ContinuousMap.const Unit b') (f' := f')
        (b := b') (b' := b')
        (ContinuousMap.const Unit e₀') (ContinuousMap.id B')
        (fun _ => h') rfl).comp
          (((ContinuousMap.HomotopyFiber.constHomeomorph Unit b' b').symm :
              C(Unit × Path b' b',
                ContinuousMap.HomotopyFiber (ContinuousMap.const Unit b') b')).comp
            ((ContinuousMap.const (Path b' b') ()).prodMk
              (ContinuousMap.id (Path b' b'))))
    let L : C(GenLoop Unit B b, Path b b) := genLoopHomeoOfUnique Unit b
    let L' : C(GenLoop Unit B' b', Path b' b') := genLoopHomeoOfUnique Unit b'
    let hJ : J (Path.refl b) = z₀ :=
      ContinuousMap.HomotopyFiber.loopInclusion_apply e₀ h (Path.refl b)
    let hJ' : J' (Path.refl b') = z₀' :=
      ContinuousMap.HomotopyFiber.loopInclusion_apply e₀' h' (Path.refl b')
    let hL : L (GenLoop.const : GenLoop Unit B b) = Path.refl b :=
      genLoopHomeoOfUnique_const Unit b
    let hL' : L' (GenLoop.const : GenLoop Unit B' b') = Path.refl b' :=
      genLoopHomeoOfUnique_const Unit b'
    let φ : C(ContinuousMap.HomotopyFiber f b, ContinuousMap.HomotopyFiber f' b') :=
      ContinuousMap.HomotopyFiber.map α β w hb
    let hφ : φ z₀ = z₀' :=
      ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he
    let D : HomotopyGroup (I ⊕ Unit) B b →
        HomotopyGroup I (ContinuousMap.HomotopyFiber f b) z₀ :=
      (mapFun I J hJ) ∘ (mapFun I L hL) ∘ (genLoopEquiv I Unit b).symm
    let D' : HomotopyGroup (I ⊕ Unit) B' b' →
        HomotopyGroup I (ContinuousMap.HomotopyFiber f' b') z₀' :=
      (mapFun I J' hJ') ∘ (mapFun I L' hL') ∘ (genLoopEquiv I Unit b').symm
    (mapFun I φ hφ) ∘ D = D' ∘ (mapFun (I ⊕ Unit) β hb) := by
  intro z₀ z₀' J J' L L' hJ hJ' hL hL' φ hφ D D'
  let βΩ : C(GenLoop Unit B b, GenLoop Unit B' b') :=
    ⟨GenLoop.map β hb, GenLoop.continuous_map β hb⟩
  have hβΩ : βΩ GenLoop.const = GenLoop.const := GenLoop.map_const β hb
  let Pβ : C(Path b b, Path b' b') :=
    L'.comp (βΩ.comp ((genLoopHomeoOfUnique Unit b).symm :
      C(Path b b, GenLoop Unit B b)))
  have hJnat : φ.comp J = J'.comp Pβ :=
    ContinuousMap.HomotopyFiber.loopInclusion_naturality α β w e₀ e₀' h h' he hb
  -- Compose the whole inclusion square with the singleton-loop homeomorphism.
  have hJL : φ.comp (J.comp L) = (J'.comp L').comp βΩ := by
    calc
      φ.comp (J.comp L) = (φ.comp J).comp L :=
        (ContinuousMap.comp_assoc φ J L).symm
      _ = (J'.comp Pβ).comp L := congrArg (fun g => ContinuousMap.comp g L) hJnat
      _ = (J'.comp L').comp βΩ := by
        simp only [Pβ, L, ContinuousMap.comp_assoc,
          Homeomorph.symm_comp_toContinuousMap, ContinuousMap.comp_id]
  have hC : (J.comp L) GenLoop.const = z₀ := (congrArg J hL).trans hJ
  have hC' : (J'.comp L') GenLoop.const = z₀' := (congrArg J' hL').trans hJ'
  have hmaps := mapFun_congr I hJL
    ((congrArg φ hC).trans hφ)
    ((congrArg (J'.comp L') hβΩ).trans hC')
  rw [mapFun_comp I φ hφ (J.comp L) hC, mapFun_comp I J hJ L hL,
    mapFun_comp I (J'.comp L') hC' βΩ hβΩ, mapFun_comp I J' hJ' L' hL'] at hmaps
  -- Recover inverse-iteration naturality from the forward comparison.
  have hiter (a : HomotopyGroup (I ⊕ Unit) B b) :
      mapFun I βΩ hβΩ ((genLoopEquiv I Unit b).symm a) =
        (genLoopEquiv I Unit b').symm (mapFun (I ⊕ Unit) β hb a) := by
    apply (genLoopEquiv I Unit b').injective
    rw [(genLoopEquiv I Unit b').apply_symm_apply]
    exact (genLoopEquiv_mapFun I Unit β hb
      ((genLoopEquiv I Unit b).symm a)).trans
        (congrArg (mapFun (I ⊕ Unit) β hb)
          ((genLoopEquiv I Unit b).apply_symm_apply a))
  funext a
  change mapFun I φ hφ
      (mapFun I J hJ (mapFun I L hL ((genLoopEquiv I Unit b).symm a))) =
    mapFun I J' hJ'
      (mapFun I L' hL'
        ((genLoopEquiv I Unit b').symm (mapFun (I ⊕ Unit) β hb a)))
  calc
    _ = (mapFun I J' hJ' ∘ mapFun I L' hL')
        (mapFun I βΩ hβΩ ((genLoopEquiv I Unit b).symm a)) :=
      congrFun hmaps ((genLoopEquiv I Unit b).symm a)
    _ = _ := congrArg (mapFun I J' hJ' ∘ mapFun I L' hL') (hiter a)

end HomotopyGroup
