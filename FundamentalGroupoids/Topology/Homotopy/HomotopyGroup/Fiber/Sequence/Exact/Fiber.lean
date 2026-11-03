/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Sequence.Exact.Transport
public import Mathlib.CategoryTheory.Types.Basic
import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Iteration.Fin

/-!
# Exactness at the homotopy-fiber terms

The incoming connecting differential and outgoing fiber projection in the
pointed homotopy-fiber sequence are exact at every fiber term, including
its term of path components. The proof transports the ordinary homotopy-fiber
loop-image theorem through ordered finite loop iteration and the public term
isomorphisms. The connecting representative retains the specified total-space
point and the entire forward path obtained from the last cube coordinate.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology

section

universe uE uB

namespace HomotopyGroup

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]

private def loopInclusion (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    C(Path b b, ContinuousMap.HomotopyFiber f b) :=
  (ContinuousMap.HomotopyFiber.map
    (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
    (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl).comp
      (((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm :
          C(Unit × Path b b,
            ContinuousMap.HomotopyFiber (ContinuousMap.const Unit b) b)).comp
        ((ContinuousMap.const (Path b b) ()).prodMk
          (ContinuousMap.id (Path b b))))

private theorem loopInclusion_refl
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    loopInclusion f b e₀ h (Path.refl b) =
      ContinuousMap.HomotopyFiber.const e₀ h :=
  ContinuousMap.HomotopyFiber.loopInclusion_apply e₀ h (Path.refl b)

private theorem loopInclusion_point
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (γ : Path b b) :
    ContinuousMap.HomotopyFiber.point (loopInclusion f b e₀ h γ) = e₀ :=
  congrArg ContinuousMap.HomotopyFiber.point
    (ContinuousMap.HomotopyFiber.loopInclusion_apply e₀ h γ)

private theorem loopInclusion_path_apply
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (γ : Path b b)
    (t : unitInterval) :
    ContinuousMap.HomotopyFiber.path (loopInclusion f b e₀ h γ) t = γ t :=
  congrArg (fun z => ContinuousMap.HomotopyFiber.path z t)
    (ContinuousMap.HomotopyFiber.loopInclusion_apply e₀ h γ)

private theorem connecting_ordered_cube (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (r : GenLoop (Fin n) (GenLoop (Fin 1) B b) GenLoop.const) :
    GenLoop.homotopyFiberConnecting n f b e₀ h
        (GenLoop.congr b (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
          (GenLoop.genLoopGenLoopEquiv b r)) =
      GenLoop.map (loopInclusion f b e₀ h) (loopInclusion_refl f b e₀ h)
        (GenLoop.map
          (genLoopHomeoOfUnique (Fin 1) b : C(GenLoop (Fin 1) B b, Path b b))
          (genLoopHomeoOfUnique_const (Fin 1) b) r) := by
  apply GenLoop.ext
  intro a
  apply ContinuousMap.HomotopyFiber.ext
  · simp only [GenLoop.homotopyFiberConnecting_point, GenLoop.map_apply,
      loopInclusion_point]
  · apply ContinuousMap.ext
    intro t
    let u : Fin (n + 1) → unitInterval := Fin.snoc a t
    have houter : (fun i : Fin n => u (Fin.castAdd 1 i)) = a := by
      funext i
      change Fin.snoc (α := fun _ => unitInterval) a t i.castSucc = a i
      simp only [Fin.snoc_castSucc]
    have hinner : (fun j : Fin 1 => u (Fin.natAdd n j)) =
        (fun _ : Fin 1 => t) := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change Fin.snoc (α := fun _ => unitInterval) a t (Fin.last n) = t
      simp only [Fin.snoc_last]
    have hsingleton :
        (genLoopHomeoOfUnique (Fin 1) b :
          C(GenLoop (Fin 1) B b, Path b b)) (r a) t =
          r a (fun _ : Fin 1 => t) :=
      (congrArg (fun γ : Path b b => γ t)
        (ContinuousMap.coe_apply (genLoopHomeoOfUnique (Fin 1) b) (r a))).trans
          (genLoopHomeoOfUnique_apply (Fin 1) b (r a) t)
    rw [GenLoop.homotopyFiberConnecting_path_apply]
    simp only [GenLoop.map_apply, loopInclusion_path_apply]
    simpa only [hsingleton, houter, hinner] using
      (GenLoop.genLoopGenLoopEquiv_fin_apply n 1 b r u)

private theorem singleton_loop_map_surjective (n : ℕ) (b : B) :
    Function.Surjective
      (mapFun (Fin n)
        (genLoopHomeoOfUnique (Fin 1) b : C(GenLoop (Fin 1) B b, Path b b))
        (genLoopHomeoOfUnique_const (Fin 1) b)) := by
  let L := genLoopHomeoOfUnique (Fin 1) b
  intro q
  refine ⟨mapFun (Fin n) (L.symm : C(Path b b, GenLoop (Fin 1) B b))
    (genLoopHomeoOfUnique_symm_refl (Fin 1) b) q, ?_⟩
  have hid : (L : C(GenLoop (Fin 1) B b, Path b b)).comp
      (L.symm : C(Path b b, GenLoop (Fin 1) B b)) = ContinuousMap.id (Path b b) := by
    apply ContinuousMap.ext
    intro γ
    exact L.apply_symm_apply γ
  calc
    _ = mapFun (Fin n)
        ((L : C(GenLoop (Fin 1) B b, Path b b)).comp
          (L.symm : C(Path b b, GenLoop (Fin 1) B b)))
        ((congrArg L (genLoopHomeoOfUnique_symm_refl (Fin 1) b)).trans
          (genLoopHomeoOfUnique_const (Fin 1) b)) q :=
      (congrFun (mapFun_comp (Fin n)
        (L : C(GenLoop (Fin 1) B b, Path b b))
        (genLoopHomeoOfUnique_const (Fin 1) b)
        (L.symm : C(Path b b, GenLoop (Fin 1) B b))
        (genLoopHomeoOfUnique_symm_refl (Fin 1) b)) q).symm
    _ = q :=
      congrFun ((mapFun_congr (Fin n) hid _ rfl).trans (mapFun_id (Fin n))) q

end HomotopyGroup

end

namespace HomotopyGroup

/-- At every fiber term, the image of the connecting differential is exactly
    the inverse image of the distinguished point under fiber projection. -/
theorem homotopyFiberSequence_exact_fiber.{v, uE, uB}
    {E : Type uE} {B : Type uB} [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (n : ℕ) :
    Set.range ((homotopyFiberSequence.{v} f b e₀ h).d
      (3 * n + 3) (3 * n + 2)).toFun =
    ((homotopyFiberSequence.{v} f b e₀ h).d
      (3 * n + 2) (3 * n + 1)).toFun ⁻¹'
        {((homotopyFiberSequence.{v} f b e₀ h).X (3 * n + 1)).point} := by
  let S := homotopyFiberSequence.{v} f b e₀ h
  change Set.range (S.d (3 * n + 3) (3 * n + 2)).toFun =
    (S.d (3 * n + 2) (3 * n + 1)).toFun ⁻¹' {(S.X (3 * n + 1)).point}
  let iB := homotopyFiberSequenceBaseIso.{v} f b e₀ h (n + 1)
  let iF := homotopyFiberSequenceFiberIso.{v} f b e₀ h n
  let iE := homotopyFiberSequenceTotalIso.{v} f b e₀ h n
  let kB : S.X (3 * (n + 1)) ≃ HomotopyGroup (Fin (n + 1)) B b :=
    (((forget Pointed).mapIso iB).toEquiv).trans Equiv.ulift
  let kF : S.X (3 * n + 2) ≃ HomotopyGroup (Fin n)
      (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h) :=
    (((forget Pointed).mapIso iF).toEquiv).trans Equiv.ulift
  let kE : S.X (3 * n + 1) ≃ HomotopyGroup (Fin n) E e₀ :=
    (((forget Pointed).mapIso iE).toEquiv).trans Equiv.ulift
  let T := genLoopFinEquiv n 1 b
  let L := genLoopHomeoOfUnique (Fin 1) b
  let F := mapFun (Fin n) (loopInclusion f b e₀ h) (loopInclusion_refl f b e₀ h)
  let G := mapFun (Fin n) (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
    (ContinuousMap.HomotopyFiber.point_const e₀ h)
  let a : S.X (3 * (n + 1)) → HomotopyGroup (Fin n) (Path b b) (Path.refl b) :=
    fun x => mapFun (Fin n) (L : C(GenLoop (Fin 1) B b, Path b b))
      (genLoopHomeoOfUnique_const (Fin 1) b) (T.symm (kB x))
  have ha : Function.Surjective a :=
    (singleton_loop_map_surjective n b).comp (T.symm.surjective.comp kB.surjective)
  have hf : ∀ x, kF (S.d (3 * (n + 1)) (3 * n + 2) x) = F (a x) := by
    intro x
    obtain ⟨q, rfl⟩ := kB.symm.surjective x
    obtain ⟨q, rfl⟩ := T.surjective q
    change kF (S.d (3 * (n + 1)) (3 * n + 2) (kB.symm (T q))) =
      F (mapFun (Fin n) (L : C(GenLoop (Fin 1) B b, Path b b))
        (genLoopHomeoOfUnique_const (Fin 1) b)
        (T.symm (kB (kB.symm (T q)))))
    rw [kB.apply_symm_apply, T.symm_apply_apply]
    refine Quotient.inductionOn
      (motive := fun q : HomotopyGroup (Fin n) (GenLoop (Fin 1) B b) GenLoop.const =>
        kF (S.d (3 * (n + 1)) (3 * n + 2) (kB.symm (T q))) =
          F (mapFun (Fin n) (L : C(GenLoop (Fin 1) B b, Path b b))
            (genLoopHomeoOfUnique_const (Fin 1) b) q)) q ?_
    intro r
    change (iF.hom.toFun
      (S.d (3 * (n + 1)) (3 * n + 2)
        (iB.inv.toFun (ULift.up
          (T (⟦r⟧ : HomotopyGroup (Fin n) (GenLoop (Fin 1) B b) GenLoop.const)))))).down =
      mapFun (Fin n) (loopInclusion f b e₀ h) (loopInclusion_refl f b e₀ h)
        (mapFun (Fin n) (L : C(GenLoop (Fin 1) B b, Path b b))
          (genLoopHomeoOfUnique_const (Fin 1) b)
          (⟦r⟧ : HomotopyGroup (Fin n) (GenLoop (Fin 1) B b) GenLoop.const))
    rw [show T (⟦r⟧ : HomotopyGroup (Fin n) (GenLoop (Fin 1) B b) GenLoop.const) =
        (⟦GenLoop.congr b (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
          (GenLoop.genLoopGenLoopEquiv b r)⟧ : HomotopyGroup (Fin (n + 1)) B b) from
      genLoopFinEquiv_class n 1 b r]
    have hd := congrArg ULift.down
      (homotopyFiberSequence_d_fiber_class.{v} f b e₀ h n
        (GenLoop.congr b (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
          (GenLoop.genLoopGenLoopEquiv b r)))
    refine hd.trans ?_
    rw [connecting_ordered_cube, mapFun_class, mapFun_class]
  have hg : ∀ y, kE (S.d (3 * n + 2) (3 * n + 1) y) = G (kF y) := by
    intro y
    have hy : iF.inv.toFun (iF.hom.toFun y) = y :=
      (((forget Pointed).mapIso iF).toEquiv).symm_apply_apply y
    have hd := homotopyFiberSequence_d_total_apply.{v} f b e₀ h n (iF.hom.toFun y)
    rw [hy] at hd
    exact congrArg ULift.down hd
  have hp : kE (S.X (3 * n + 1)).point =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) E e₀) :=
    congrArg ULift.down (homotopyFiberSequenceTotalIso.{v} f b e₀ h n).hom.map_point
  have hex : Set.range F = G ⁻¹' {kE (S.X (3 * n + 1)).point} := by
    rw [hp]
    exact range_mapFun_homotopyFiber_loop (Fin n) f b e₀ h
  have he := Function.range_eq_preimage_singleton_of_coordinates
    (f := F) (g := G)
    (f' := (S.d (3 * (n + 1)) (3 * n + 2)).toFun)
    (g' := (S.d (3 * n + 2) (3 * n + 1)).toFun)
    a kF kE ha kF.injective kE.injective hf hg (S.X (3 * n + 1)).point hex
  have hn : 3 * (n + 1) = 3 * n + 3 := by omega
  rw [hn] at he
  exact he

end HomotopyGroup
