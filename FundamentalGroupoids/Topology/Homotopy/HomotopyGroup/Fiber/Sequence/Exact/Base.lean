/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence
import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber
import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence.Exact.Transport
import Mathlib.CategoryTheory.Types.Basic

/-!
# Exactness at the positive base-space terms

The image of the total-space differential is the point fiber of the connecting
differential at every positive base-space term of the homotopy-fiber sequence.
The comparison uses ordered finite coordinates: the last coordinate is the
forward path parameter, and all other coordinates are retained in their order.
There is no assertion of surjectivity onto the degree-zero base-space term.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology

namespace HomotopyGroup

section Coordinates

universe uE uB

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]

private def baseCoordinateEquiv (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit :=
  (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin n)) finOneEquiv)

private theorem baseCoordinateEquiv_snoc (n : ℕ)
    (a : Fin n → unitInterval) (t : unitInterval) :
    (fun i => Sum.elim a (fun _ : Unit => t) (baseCoordinateEquiv n i)) =
      Fin.snoc a t := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [baseCoordinateEquiv]
  · simp [baseCoordinateEquiv]

private def baseLoopInclusion (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    C(Path b b, ContinuousMap.HomotopyFiber f b) :=
  (ContinuousMap.HomotopyFiber.map
    (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
    (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl).comp
      (((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm :
          C(Unit × Path b b,
            ContinuousMap.HomotopyFiber (ContinuousMap.const Unit b) b)).comp
        ((ContinuousMap.const (Path b b) ()).prodMk
          (ContinuousMap.id (Path b b))))

private theorem baseLoopInclusion_refl
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    baseLoopInclusion f b e₀ h (Path.refl b) =
      ContinuousMap.HomotopyFiber.const e₀ h :=
  ContinuousMap.HomotopyFiber.loopInclusion_apply e₀ h (Path.refl b)

private def baseConnecting (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    HomotopyGroup (Fin n ⊕ Unit) B b →
      HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h) :=
  mapFun (Fin n) (baseLoopInclusion f b e₀ h) (baseLoopInclusion_refl f b e₀ h) ∘
    mapFun (Fin n) (genLoopHomeoOfUnique Unit b : C(GenLoop Unit B b, Path b b))
      (genLoopHomeoOfUnique_const Unit b) ∘
        (HomotopyGroup.genLoopEquiv (Fin n) Unit b).symm

private theorem baseConnecting_congr_class (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (p : GenLoop (Fin (n + 1)) B b) :
    baseConnecting n f b e₀ h
        (HomotopyGroup.congr b (baseCoordinateEquiv n)
          (⟦p⟧ : HomotopyGroup (Fin (n + 1)) B b)) =
      (⟦GenLoop.homotopyFiberConnecting n f b e₀ h p⟧ :
        HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
          (ContinuousMap.HomotopyFiber.const e₀ h)) := by
  change mapFun (Fin n) (baseLoopInclusion f b e₀ h)
      (baseLoopInclusion_refl f b e₀ h)
      (mapFun (Fin n) (genLoopHomeoOfUnique Unit b : C(GenLoop Unit B b, Path b b))
        (genLoopHomeoOfUnique_const Unit b)
        ((HomotopyGroup.genLoopEquiv (Fin n) Unit b).symm
          (HomotopyGroup.congr b (baseCoordinateEquiv n)
            (⟦p⟧ : HomotopyGroup (Fin (n + 1)) B b)))) = _
  simp only [HomotopyGroup.congr_class,
    HomotopyGroup.genLoopEquiv_symm_class, HomotopyGroup.mapFun_class]
  apply congrArg (fun q : GenLoop (Fin n) (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h) =>
    (⟦q⟧ : HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h)))
  apply GenLoop.ext
  intro a
  let γ : Path b b := genLoopHomeoOfUnique Unit b
    (((GenLoop.genLoopGenLoopEquiv b (M := Fin n) (N := Unit)).symm
      (GenLoop.congr b (baseCoordinateEquiv n) p)) a)
  have hJ : baseLoopInclusion f b e₀ h γ =
      ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
        e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm) :=
    ContinuousMap.HomotopyFiber.loopInclusion_apply e₀ h γ
  apply ContinuousMap.HomotopyFiber.ext
  · change ContinuousMap.HomotopyFiber.point (baseLoopInclusion f b e₀ h γ) = _
    rw [hJ, ContinuousMap.HomotopyFiber.point_mk,
      GenLoop.homotopyFiberConnecting_point]
  · apply ContinuousMap.ext
    intro t
    change ContinuousMap.HomotopyFiber.path (baseLoopInclusion f b e₀ h γ) t = _
    rw [hJ, ContinuousMap.HomotopyFiber.path_mk,
      GenLoop.homotopyFiberConnecting_path_apply]
    change genLoopHomeoOfUnique Unit b
        (((GenLoop.genLoopGenLoopEquiv b (M := Fin n) (N := Unit)).symm
          (GenLoop.congr b (baseCoordinateEquiv n) p)) a) t = p (Fin.snoc a t)
    rw [genLoopHomeoOfUnique_apply]
    change (GenLoop.congr b (baseCoordinateEquiv n) p)
        (Sum.elim a (fun _ : Unit => t)) = p (Fin.snoc a t)
    rw [GenLoop.congr_apply, baseCoordinateEquiv_snoc]

end Coordinates

/-- The homotopy-fiber sequence is exact at every positive base-space term.
The incoming map is induced by `f`, and the outgoing map retains the entire
forward last-coordinate path in the ordinary homotopy fiber. -/
theorem homotopyFiberSequence_exact_base.{v, uE, uB}
    {E : Type uE} {B : Type uB} [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (n : ℕ) :
    let S := homotopyFiberSequence.{v} f b e₀ h
    Set.range (S.d (3 * n + 4) (3 * n + 3)).toFun =
      (S.d (3 * n + 3) (3 * n + 2)).toFun ⁻¹' {(S.X (3 * n + 2)).point} := by
  classical
  let S := homotopyFiberSequence.{v} f b e₀ h
  change Set.range (S.d (3 * n + 4) (3 * n + 3)).toFun =
    (S.d (3 * n + 3) (3 * n + 2)).toFun ⁻¹' {(S.X (3 * n + 2)).point}
  let aIso := ((forget Pointed).mapIso
    (homotopyFiberSequenceTotalIso.{v} f b e₀ h (n + 1))).toEquiv
  let bIso := ((forget Pointed).mapIso
    (homotopyFiberSequenceBaseIso.{v} f b e₀ h (n + 1))).toEquiv
  let cIso := ((forget Pointed).mapIso
    (homotopyFiberSequenceFiberIso.{v} f b e₀ h n)).toEquiv
  let aCoord := (aIso.trans Equiv.ulift).trans
    (HomotopyGroup.congr e₀ (baseCoordinateEquiv n))
  let bCoord := (bIso.trans Equiv.ulift).trans
    (HomotopyGroup.congr b (baseCoordinateEquiv n))
  let cCoord := cIso.trans Equiv.ulift
  have hf (x : S.X (3 * (n + 1) + 1)) :
      bCoord ((S.d (3 * (n + 1) + 1) (3 * (n + 1))).toFun x) =
        mapFun (Fin n ⊕ Unit) f h (aCoord x) := by
    have hd : bIso ((S.d (3 * (n + 1) + 1) (3 * (n + 1))).toFun
          (aIso.symm (aIso x))) =
        ULift.up (mapFun (Fin (n + 1)) f h (aIso x).down) :=
      homotopyFiberSequence_d_base_apply.{v} f b e₀ h (n + 1) (aIso x)
    rw [aIso.symm_apply_apply] at hd
    change HomotopyGroup.congr b (baseCoordinateEquiv n)
        (bIso ((S.d (3 * (n + 1) + 1) (3 * (n + 1))).toFun x)).down = _
    exact (congrArg (fun q : ULift.{max v uE uB}
        (HomotopyGroup (Fin (n + 1)) B b) =>
      HomotopyGroup.congr b (baseCoordinateEquiv n) q.down) hd).trans
        (HomotopyGroup.congr_mapFun (baseCoordinateEquiv n) f h (aIso x).down)
  have hg (y : S.X (3 * (n + 1))) :
      cCoord ((S.d (3 * (n + 1)) (3 * n + 2)).toFun y) =
        baseConnecting n f b e₀ h (bCoord y) := by
    obtain ⟨z, rfl⟩ := bIso.symm.surjective y
    rcases z with ⟨q⟩
    refine Quotient.inductionOn q ?_
    intro p
    have hd : cIso ((S.d (3 * (n + 1)) (3 * n + 2)).toFun
          (bIso.symm (ULift.up (⟦p⟧ : HomotopyGroup (Fin (n + 1)) B b)))) =
        ULift.up (⟦GenLoop.homotopyFiberConnecting n f b e₀ h p⟧ :
          HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
            (ContinuousMap.HomotopyFiber.const e₀ h)) :=
      homotopyFiberSequence_d_fiber_class.{v} f b e₀ h n p
    change (cIso ((S.d (3 * (n + 1)) (3 * n + 2)).toFun
        (bIso.symm (ULift.up (⟦p⟧ : HomotopyGroup (Fin (n + 1)) B b))))).down =
      baseConnecting n f b e₀ h
        (HomotopyGroup.congr b (baseCoordinateEquiv n)
          (bIso (bIso.symm (ULift.up (⟦p⟧ : HomotopyGroup (Fin (n + 1)) B b)))).down)
    rw [bIso.apply_symm_apply]
    exact (congrArg ULift.down hd).trans (baseConnecting_congr_class n f b e₀ h p).symm
  have hpoint : cCoord (S.X (3 * n + 2)).point =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h)) := by
    change ((homotopyFiberSequenceFiberIso.{v} f b e₀ h n).hom.toFun
      (S.X (3 * n + 2)).point).down = _
    exact congrArg ULift.down (homotopyFiberSequenceFiberIso.{v} f b e₀ h n).hom.map_point
  have hex : Set.range (mapFun (Fin n ⊕ Unit) f h) =
      (baseConnecting n f b e₀ h) ⁻¹' {cCoord (S.X (3 * n + 2)).point} := by
    rw [hpoint]
    exact HomotopyGroup.range_mapFun_eq_preimage_homotopyFiber_loop (Fin n) f b e₀ h
  have hex' := Function.range_eq_preimage_singleton_of_coordinates
    (f := mapFun (Fin n ⊕ Unit) f h) (g := baseConnecting n f b e₀ h)
    (f' := (S.d (3 * (n + 1) + 1) (3 * (n + 1))).toFun)
    (g' := (S.d (3 * (n + 1)) (3 * n + 2)).toFun)
    aCoord bCoord cCoord aCoord.surjective bCoord.injective cCoord.injective
    hf hg (S.X (3 * n + 2)).point hex
  have hsrc : 3 * (n + 1) + 1 = 3 * n + 4 := by omega
  have hmid : 3 * (n + 1) = 3 * n + 3 := by omega
  rw [hsrc, hmid] at hex'
  exact hex'

end HomotopyGroup
