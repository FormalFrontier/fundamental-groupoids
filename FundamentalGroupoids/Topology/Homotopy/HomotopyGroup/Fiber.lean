/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber.Exact
public import FundamentalGroupoids.Topology.Homotopy.Fiber.GenLoop
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Loop
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Iteration.Group
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Homotopy-group exactness at the base of a homotopy fiber

For every cube index `I`, the image of based postcomposition by `f` on
`HomotopyGroup (I ⊕ Unit)` is the preimage of the constant class under inverse
loop iteration, the singleton-loop homeomorphism to `Path b b`, and the loop
inclusion into the ordinary homotopy fiber. The fiber is based at
`ContinuousMap.HomotopyFiber.const e₀ h`, for the supplied equality `h : f e₀ = b`.

The loop inclusion sends `γ : Path b b` to the fiber point retaining `e₀` and
`γ.toContinuousMap`, with endpoint equation `γ.target.trans h.symm`. Thus, on a
representative `p : GenLoop (I ⊕ Unit) B b`, the composite retains point `e₀`
and, at every outer cube coordinate `a` and time `t`, the path value
`p (Sum.elim a (fun _ : Unit ↦ t))`. The sum order is outer coordinates followed
by the singleton time coordinate, with no path reversal.

No index instances are needed for the set equality. For a nonempty index with
decidable equality, the same function is a composite of the existing induced
homomorphisms and multiplicative loop-iteration equivalence, giving a subgroup
range–kernel equality with the existing homotopy-group structures. At an empty
index the assertion remains pointed-set exactness from fundamental-group
classes to path components of the homotopy fiber.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, §6,
  printed pp. 61–62, for the fiber-sequence context. For finite indices the
  results here are ordinary cubical counterparts, using product, subspace and
  compact-open topologies. They do not identify these models or their path and
  ordered-coordinate conventions with May's kified mapping-space models and
  connecting maps. The arbitrary-index statements are cubical extensions.
* Mathlib's generalized loops and homotopy groups, due to Roberto Alvarez,
  and its paths and path components, due to Patrick Massot and contributors.
-/

@[expose] public section

noncomputable section

universe uI uE uB

open scoped Topology

namespace HomotopyGroup

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]

private def fundamentalGroupGenLoopEquiv (I : Type uI) (e₀ : E) :
    HomotopyGroup (I ⊕ Unit) E e₀ ≃
      FundamentalGroup (GenLoop I E e₀) GenLoop.const :=
  ((congr e₀ (Equiv.sumComm I Unit)).trans (genLoopEquiv Unit I e₀).symm).trans
    (homotopyGroupEquivFundamentalGroupOfUnique
      (X := GenLoop I E e₀) (x := GenLoop.const) Unit)

private theorem fundamentalGroupGenLoopEquiv_class (I : Type uI) (e₀ : E)
    (p : GenLoop (I ⊕ Unit) E e₀) :
    let γ : Path (GenLoop.const : GenLoop I E e₀) GenLoop.const :=
      genLoopHomeoOfUnique Unit (GenLoop.const : GenLoop I E e₀)
        ((GenLoop.genLoopGenLoopEquiv e₀ (M := Unit) (N := I)).symm
          (GenLoop.congr e₀ (Equiv.sumComm I Unit) p))
    fundamentalGroupGenLoopEquiv I e₀ (⟦p⟧ : HomotopyGroup (I ⊕ Unit) E e₀) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∧
      ∀ (t : unitInterval) (a : I → unitInterval),
        γ t a = p (Sum.elim a (fun _ : Unit ↦ t)) := by
  intro γ
  constructor
  · change homotopyGroupEquivFundamentalGroupOfUnique Unit
        ((genLoopEquiv Unit I e₀).symm
          (congr e₀ (Equiv.sumComm I Unit) (⟦p⟧ : HomotopyGroup (I ⊕ Unit) E e₀))) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
    rw [congr_class, genLoopEquiv_symm_class]
    rfl
  · intro t a
    change p (fun j ↦ Sum.elim (fun _ : Unit ↦ t) a ((Equiv.sumComm I Unit) j)) =
      p (Sum.elim a (fun _ : Unit ↦ t))
    apply congrArg p
    funext j
    cases j <;> rfl

private theorem fundamentalGroupOfUnit_mapFun (f : C(E, B)) {e₀ : E} {b : B}
    (h : f e₀ = b) (a : HomotopyGroup Unit E e₀) :
    homotopyGroupEquivFundamentalGroupOfUnique Unit (mapFun Unit f h a) =
      FundamentalGroup.mapOfEq f h
        (homotopyGroupEquivFundamentalGroupOfUnique Unit a) := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [mapFun_class, FundamentalGroup.mapOfEq_apply]
  change Path.Homotopic.Quotient.mk
      (genLoopHomeoOfUnique Unit b (GenLoop.map f h p)) =
    ((Path.Homotopic.Quotient.mk (genLoopHomeoOfUnique Unit e₀ p)).map f).cast
      h.symm h.symm
  rw [genLoopHomeoOfUnique_map, Path.Homotopic.Quotient.mk_cast,
    Path.Homotopic.Quotient.mk_map]

private theorem fundamentalGroupGenLoopEquiv_mapFun (I : Type uI) (f : C(E, B))
    {e₀ : E} {b : B} (h : f e₀ = b) (a : HomotopyGroup (I ⊕ Unit) E e₀) :
    let g : C(GenLoop I E e₀, GenLoop I B b) :=
      ⟨GenLoop.map f h, GenLoop.continuous_map f h⟩
    let hg : g GenLoop.const = GenLoop.const := GenLoop.map_const (N := I) f h
    fundamentalGroupGenLoopEquiv I b (mapFun (I ⊕ Unit) f h a) =
      FundamentalGroup.mapOfEq g hg (fundamentalGroupGenLoopEquiv I e₀ a) := by
  intro g hg
  have hiter :
      (genLoopEquiv Unit I b).symm
          (mapFun (Unit ⊕ I) f h (congr e₀ (Equiv.sumComm I Unit) a)) =
        mapFun Unit g hg
          ((genLoopEquiv Unit I e₀).symm (congr e₀ (Equiv.sumComm I Unit) a)) := by
    apply (genLoopEquiv Unit I b).injective
    simpa only [Equiv.apply_symm_apply] using
      (genLoopEquiv_mapFun Unit I f h
        ((genLoopEquiv Unit I e₀).symm (congr e₀ (Equiv.sumComm I Unit) a))).symm
  change homotopyGroupEquivFundamentalGroupOfUnique Unit
      ((genLoopEquiv Unit I b).symm
        (congr b (Equiv.sumComm I Unit) (mapFun (I ⊕ Unit) f h a))) =
    FundamentalGroup.mapOfEq g hg
      (homotopyGroupEquivFundamentalGroupOfUnique Unit
        ((genLoopEquiv Unit I e₀).symm (congr e₀ (Equiv.sumComm I Unit) a)))
  rw [congr_mapFun, hiter]
  exact fundamentalGroupOfUnit_mapFun g hg _

private theorem mem_range_mapFun_iff_fundamentalGroupGenLoopEquiv (I : Type uI)
    (f : C(E, B)) {e₀ : E} {b : B} (h : f e₀ = b)
    (a : HomotopyGroup (I ⊕ Unit) B b) :
    a ∈ Set.range (mapFun (I ⊕ Unit) f h) ↔
      fundamentalGroupGenLoopEquiv I b a ∈ Set.range
        (FundamentalGroup.mapOfEq
          (⟨GenLoop.map f h, GenLoop.continuous_map f h⟩ :
            C(GenLoop I E e₀, GenLoop I B b))
          (GenLoop.map_const (N := I) f h)) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨fundamentalGroupGenLoopEquiv I e₀ q,
      (fundamentalGroupGenLoopEquiv_mapFun I f h q).symm⟩
  · rintro ⟨q, hq⟩
    obtain ⟨r, rfl⟩ := (fundamentalGroupGenLoopEquiv I e₀).surjective q
    refine ⟨r, (fundamentalGroupGenLoopEquiv I b).injective ?_⟩
    exact (fundamentalGroupGenLoopEquiv_mapFun I f h r).trans hq

private theorem homotopyFiber_loop_point_path (f : C(E, B)) (b : B)
    (e₀ : E) (h : f e₀ = b) :
    let J : C(Path b b, ContinuousMap.HomotopyFiber f b) :=
      (ContinuousMap.HomotopyFiber.map
        (f := ContinuousMap.const Unit b) (f' := f)
        (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B)
        (fun _ => h) rfl).comp
          (((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm :
              C(Unit × Path b b,
                ContinuousMap.HomotopyFiber
                  (ContinuousMap.const Unit b) b)).comp
            ((ContinuousMap.const (Path b b) ()).prodMk
              (ContinuousMap.id (Path b b))))
    ∀ γ : Path b b,
      ContinuousMap.HomotopyFiber.point (J γ) = e₀ ∧
        ContinuousMap.HomotopyFiber.path (J γ) = γ.toContinuousMap := by
  intro J γ
  have hJ : J γ = ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
      e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm) :=
    ContinuousMap.HomotopyFiber.loopInclusion_apply e₀ h γ
  constructor
  · simpa only [ContinuousMap.HomotopyFiber.point_mk] using
      congrArg ContinuousMap.HomotopyFiber.point hJ
  · simpa only [ContinuousMap.HomotopyFiber.path_mk] using
      congrArg ContinuousMap.HomotopyFiber.path hJ

/-- For every cube index, the image of based postcomposition by `f` is the
preimage of the constant class under inverse loop iteration followed by the
singleton-loop homeomorphism and the homotopy-fiber loop inclusion. The
inclusion retains `e₀` and the whole forward path. No index instances or
geometric hypotheses on the spaces are required.

For finite indices this is an ordinary cubical counterpart of the base-space
position of fiber-sequence exactness in J. P. May, *A Concise Course in Algebraic
Topology*, Chapter 8, §6, printed pp. 61–62. Identification with May's kified
mapping spaces and ordered-coordinate conventions is not asserted. -/
theorem range_mapFun_eq_preimage_homotopyFiber_loop (I : Type uI)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    let H := ContinuousMap.HomotopyFiber f b
    let z₀ : H := ContinuousMap.HomotopyFiber.const (f := f) (b := b) e₀ h
    let L : C(GenLoop Unit B b, Path b b) :=
      (genLoopHomeoOfUnique Unit b : C(GenLoop Unit B b, Path b b))
    let L_const : L GenLoop.const = Path.refl b :=
      genLoopHomeoOfUnique_const Unit b
    let J : C(Path b b, H) :=
      (ContinuousMap.HomotopyFiber.map
        (f := ContinuousMap.const Unit b) (f' := f)
        (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B)
        (fun _ => h) rfl).comp
          (((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm :
              C(Unit × Path b b,
                ContinuousMap.HomotopyFiber
                  (ContinuousMap.const Unit b) b)).comp
            ((ContinuousMap.const (Path b b) ()).prodMk
              (ContinuousMap.id (Path b b))))
    let J_refl : J (Path.refl b) = z₀ := by
      apply ContinuousMap.HomotopyFiber.ext
      · exact (ContinuousMap.HomotopyFiber.point_map
          (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
          (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl
          ((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm
            ((), Path.refl b))).trans
          (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h).symm
      · apply ContinuousMap.ext
        intro t
        exact (DFunLike.congr_fun
          (ContinuousMap.HomotopyFiber.path_map
            (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
            (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl
            ((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm
              ((), Path.refl b))) t).trans
          ((ContinuousMap.HomotopyFiber.constHomeomorph_symm_path_apply
            ((), Path.refl b) t).trans
            ((Path.refl_apply b t).trans
              (DFunLike.congr_fun
                (ContinuousMap.HomotopyFiber.path_const (f := f) (b := b) e₀ h) t).symm))
    let D : HomotopyGroup (I ⊕ Unit) B b → HomotopyGroup I H z₀ :=
      mapFun I J J_refl ∘ mapFun I L L_const ∘ (genLoopEquiv I Unit b).symm
    Set.range (mapFun (I ⊕ Unit) f h) =
      D ⁻¹' {(⟦GenLoop.const⟧ : HomotopyGroup I H z₀)} := by
  intro H z₀ L L_const J J_refl D
  let c₀ : HomotopyGroup I H z₀ := ⟦GenLoop.const⟧
  ext a
  change a ∈ Set.range (mapFun (I ⊕ Unit) f h) ↔ D a = c₀
  obtain ⟨p, hp⟩ := Quotient.exists_rep a
  have hJ := homotopyFiber_loop_point_path f b e₀ h
  let Ψ : GenLoop I H z₀ :=
    GenLoop.map J J_refl
      (GenLoop.map L L_const
        ((GenLoop.genLoopGenLoopEquiv b (M := I) (N := Unit)).symm p))
  have Ψ_point (x : I → unitInterval) :
      ContinuousMap.HomotopyFiber.point (Ψ x) = e₀ := by
    change ContinuousMap.HomotopyFiber.point (J _) = e₀
    exact (hJ _).1
  have Ψ_path (x : I → unitInterval) :
      ContinuousMap.HomotopyFiber.path (Ψ x) =
        (L
          (((GenLoop.genLoopGenLoopEquiv b (M := I) (N := Unit)).symm p) x)).toContinuousMap := by
    change ContinuousMap.HomotopyFiber.path (J _) = _
    exact (hJ _).2
  have Ψ_path_apply (x : I → unitInterval) (t : unitInterval) :
      ContinuousMap.HomotopyFiber.path (Ψ x) t =
        p (Sum.elim x (fun _ : Unit ↦ t)) := by
    rw [Ψ_path]
    rfl
  have hD : D a = (⟦Ψ⟧ : HomotopyGroup I H z₀) := by
    exact (congrArg D hp.symm).trans
      ((congrArg (mapFun I J J_refl)
        ((congrArg (mapFun I L L_const)
          (genLoopEquiv_symm_class I Unit b p)).trans
            (mapFun_class I L L_const _))).trans
              (mapFun_class I J J_refl _))
  have hreflect :
      Joined Ψ (GenLoop.const : GenLoop I H z₀) ↔ D a = c₀ := by
    constructor
    · intro hjoined
      exact hD.trans
        (Quotient.sound ((GenLoop.homotopic_iff_joined Ψ GenLoop.const).mpr hjoined))
    · intro heq
      exact (GenLoop.homotopic_iff_joined Ψ GenLoop.const).mp
        (Quotient.exact (hD.symm.trans heq))
  let g : C(GenLoop I E e₀, GenLoop I B b) :=
    ⟨GenLoop.map f h, GenLoop.continuous_map f h⟩
  let hg : g GenLoop.const = GenLoop.const := GenLoop.map_const (N := I) f h
  let γ : Path (GenLoop.const : GenLoop I B b) GenLoop.const :=
    genLoopHomeoOfUnique Unit (GenLoop.const : GenLoop I B b)
      ((GenLoop.genLoopGenLoopEquiv b (M := Unit) (N := I)).symm
        (GenLoop.congr b (Equiv.sumComm I Unit) p))
  have hγ (t : unitInterval) (x : I → unitInterval) :
      γ t x = p (Sum.elim x (fun _ : Unit ↦ t)) :=
    (fundamentalGroupGenLoopEquiv_class I b p).2 t x
  let zγ : ContinuousMap.HomotopyFiber g GenLoop.const :=
    ContinuousMap.HomotopyFiber.mk GenLoop.const γ.toContinuousMap
      γ.source (γ.target.trans hg.symm)
  let Γ : ContinuousMap.HomotopyFiber g GenLoop.const ≃ₜ GenLoop I H z₀ :=
    ContinuousMap.HomotopyFiber.genLoopHomeomorph (N := I) f h
  -- The transposition square retains the point and every time value of the original path.
  have hΓzγ : Γ zγ = Ψ := by
    have hΓapply : Γ zγ = ContinuousMap.HomotopyFiber.genLoopForward f h zγ :=
      ContinuousMap.HomotopyFiber.genLoopHomeomorph_apply f h zγ
    rw [hΓapply]
    apply GenLoop.ext
    intro x
    apply ContinuousMap.HomotopyFiber.ext
    · simpa only [ContinuousMap.HomotopyFiber.point_genLoopForward, zγ,
        ContinuousMap.HomotopyFiber.point_mk, GenLoop.const_apply] using (Ψ_point x).symm
    · apply ContinuousMap.ext
      intro t
      rw [ContinuousMap.HomotopyFiber.path_genLoopForward_apply, Ψ_path_apply]
      simp only [zγ, ContinuousMap.HomotopyFiber.path_mk]
      rw [Path.coe_toContinuousMap]
      exact hγ t x
  have hΓconst :
      Γ (ContinuousMap.HomotopyFiber.const (GenLoop.const : GenLoop I E e₀) hg) =
        (GenLoop.const : GenLoop I H z₀) :=
    ContinuousMap.HomotopyFiber.genLoopHomeomorph_const (N := I) f h
  have hclass :=
    (congrArg (fundamentalGroupGenLoopEquiv I b)
      (show (⟦p⟧ : HomotopyGroup (I ⊕ Unit) B b) = a from hp)).symm.trans
      (fundamentalGroupGenLoopEquiv_class I b p).1
  rw [mem_range_mapFun_iff_fundamentalGroupGenLoopEquiv I f h a, hclass,
    FundamentalGroup.mem_range_mapOfEq_iff_joined_homotopyFiber]
  change Joined zγ
    (ContinuousMap.HomotopyFiber.const (GenLoop.const : GenLoop I E e₀) hg) ↔ D a = c₀
  rw [← hreflect]
  constructor
  · intro hjoined
    simpa only [hΓzγ, hΓconst] using hjoined.map Γ.continuous
  · intro hjoined
    have hΓjoined : Joined (Γ zγ)
        (Γ (ContinuousMap.HomotopyFiber.const (GenLoop.const : GenLoop I E e₀) hg)) := by
      simpa only [hΓzγ, hΓconst] using hjoined
    simpa only [Homeomorph.symm_apply_apply] using hΓjoined.map Γ.symm.continuous

/-- For a nonempty cube index with decidable equality, the image of the
homomorphism induced by `f` is the kernel of inverse loop iteration followed by
the singleton-loop homeomorphism and the homotopy-fiber loop inclusion. All
homomorphisms use the existing homotopy-group structures, and the inclusion
retains `e₀` and the whole forward path.

For finite indices this is an ordinary cubical counterpart of the base-space
position of fiber-sequence exactness in J. P. May, *A Concise Course in Algebraic
Topology*, Chapter 8, §6, printed pp. 61–62. Identification with May's kified
mapping spaces and ordered-coordinate conventions is not asserted. -/
theorem range_map_eq_ker_homotopyFiber_loop (I : Type uI)
    [DecidableEq I] [Nonempty I]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    let H := ContinuousMap.HomotopyFiber f b
    let z₀ : H := ContinuousMap.HomotopyFiber.const (f := f) (b := b) e₀ h
    let L : C(GenLoop Unit B b, Path b b) :=
      (genLoopHomeoOfUnique Unit b : C(GenLoop Unit B b, Path b b))
    let L_const : L GenLoop.const = Path.refl b :=
      genLoopHomeoOfUnique_const Unit b
    let J : C(Path b b, H) :=
      (ContinuousMap.HomotopyFiber.map
        (f := ContinuousMap.const Unit b) (f' := f)
        (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B)
        (fun _ => h) rfl).comp
          (((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm :
              C(Unit × Path b b,
                ContinuousMap.HomotopyFiber
                  (ContinuousMap.const Unit b) b)).comp
            ((ContinuousMap.const (Path b b) ()).prodMk
              (ContinuousMap.id (Path b b))))
    let J_refl : J (Path.refl b) = z₀ := by
      apply ContinuousMap.HomotopyFiber.ext
      · exact (ContinuousMap.HomotopyFiber.point_map
          (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
          (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl
          ((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm
            ((), Path.refl b))).trans
          (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h).symm
      · apply ContinuousMap.ext
        intro t
        exact (DFunLike.congr_fun
          (ContinuousMap.HomotopyFiber.path_map
            (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
            (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl
            ((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm
              ((), Path.refl b))) t).trans
          ((ContinuousMap.HomotopyFiber.constHomeomorph_symm_path_apply
            ((), Path.refl b) t).trans
            ((Path.refl_apply b t).trans
              (DFunLike.congr_fun
                (ContinuousMap.HomotopyFiber.path_const (f := f) (b := b) e₀ h) t).symm))
    let D_hom : HomotopyGroup (I ⊕ Unit) B b →* HomotopyGroup I H z₀ :=
      (map I J J_refl).comp
        ((map I L L_const).comp (genLoopMulEquiv I Unit b).symm.toMonoidHom)
    (map (I ⊕ Unit) f h).range = D_hom.ker := by
  intro H z₀ L L_const J J_refl D_hom
  apply Subgroup.ext
  intro a
  have hset := range_mapFun_eq_preimage_homotopyFiber_loop I f b e₀ h
  exact Set.ext_iff.mp hset a

end HomotopyGroup
