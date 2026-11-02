/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber.Const
public import FundamentalGroupoids.Topology.Homotopy.Fiber.PathComponent
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace
import FundamentalGroupoids.Topology.Homotopy.Fiber.Contractible

/-!
# Image exactness for homotopy fibers

For a commutative square over the identity of a fixed base, the image on path
components of the induced map of ordinary homotopy fibers is the retained-point
preimage of the source map's component image. The source spaces and the base
have independent universes and arbitrary topologies; the source may be empty.

For a specified point over the basepoint, the loop classes represented in the
homotopy fiber are exactly the components whose retained points belong to the
specified point's component. The parameterization uses the existing fundamental
group, generalized-loop class comparison and continuous maps of homotopy fibers.
The ordinary fiber retains the whole forward path from the basepoint to the
image of the source point.

The preimage of the constant-loop image under the loop-class map is the image
of the induced fundamental-group homomorphism. May's preceding arrow on p. 62
is `−Ωf`; reversing loops does not change that group image. The loop-class map
here retains the whole forward loop.

For every cube index `N`, the image of the based point projection on
`HomotopyGroup` classes is the preimage of the constant class under
`HomotopyGroup.mapFun N f h`, with no index instances. The fiber is based at
`ContinuousMap.HomotopyFiber.const e₀ h`. With `[DecidableEq N] [Nonempty N]`,
this is range–kernel exactness for the existing `HomotopyGroup.map`
homomorphisms. These instances supply operation data, not conditions on the
spaces. This position is exact at `HomotopyGroup N E e₀`, distinct from the
positions at the fundamental group of the base and the path components of the
fiber above. No group structure on those components or full long exact sequence
is supplied. Index and space universes are independent. Empty-index classes
retain all path components; the zeroth projection theorem also applies without
`e₀` or `h`, even for an empty source. Infinite-index quotients are already
subsingletons.

The loop-image statements and finite-dimensional projection case adapt the
fiber-sequence exactness theorem in May, Chapter 8, Section 6, printed pp. 61–62
(PDF pp. 69–70), especially printed p. 62. The arbitrary-index projection
formula is a cubical extension; the fixed-base component-image statements are
structural extensions, not statements quoted from that section. Here products,
subspaces and compact-open mapping spaces carry their ordinary, non-kified
topologies; no sphere-domain comparison or identification with May's
weak-Hausdorff, compactly generated category `U` is asserted.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, Section 6,
  "Fiber sequences", printed pp. 61–62 (PDF pp. 69–70), especially printed p. 62:
  the homotopy fiber, loop inclusion and projection positions of exactness.
* Mathlib's paths and path components, due to Patrick Massot and contributors,
  and generalized loops and homotopy groups, due to Roberto Alvarez.
* Mathlib's `Path.Homotopic.map_trans_evalAt`, due to Praneeth Kolichala and
  Yury Kudryashov, for naturality of endpoint tracks.
* `ContinuousMap.HomotopyFiber.map` and
  `ContinuousMap.HomotopyFiber.constHomeomorph`, for maps of ordinary fibers and
  the constant-map fiber comparison.
* `HomotopyGroup.equivZerothHomotopy`, for the identity-on-representatives
  comparison between generalized-loop classes and path components.
-/

@[expose] public section

universe uE uB uE'

open scoped Topology

variable {E : Type uE} {B : Type uB} {E' : Type uE'}
variable [tE : TopologicalSpace E] [tB : TopologicalSpace B]
variable [tE' : TopologicalSpace E']

namespace ContinuousMap.HomotopyFiber

private theorem exists_joined_map_id
    (f : C(E, B)) (g : C(E', B)) (u : C(E', E))
    (w : ∀ x, f (u x) = g x) (b : B)
    (z : HomotopyFiber f b) (e' : E') (η : Path (point z) (u e')) :
    ∃ z' : HomotopyFiber g b,
      Joined z (map (f := g) (f' := f) (b := b) (b' := b)
        u (ContinuousMap.id B) w rfl z') := by
  let γ : Path b (f (point z)) :=
    Path.mk (path z) (path_zero z) (path_one z)
  -- Append successively longer prefixes of the retained-point path.
  let q : ∀ t : unitInterval, Path (point z) (η t) := fun t =>
    (η.truncateOfLE (t₀ := 0) (t₁ := (t : ℝ)) t.property.1).cast
      η.extend_zero.symm (η.extend_extends' t).symm
  have hq : Continuous (fun p : unitInterval × unitInterval => q p.1 p.2) :=
    (η.truncate_const_continuous_family 0).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let r : ∀ t : unitInterval, Path b (f (η t)) := fun t =>
    γ.trans ((q t).map f.continuous)
  have hr : Continuous (fun p : unitInterval × unitInterval => r p.1 p.2) :=
    Path.trans_continuous_family (fun _ : unitInterval => γ)
      (γ.continuous.comp continuous_snd)
      (fun t => (q t).map f.continuous) (f.continuous.comp hq)
  let v : unitInterval → HomotopyFiber f b := fun t =>
    mk (η t) (r t).toContinuousMap (r t).source (r t).target
  have hv : Continuous v := continuous_iff.2
    ⟨η.continuous, ContinuousMap.continuous_of_continuous_uncurry _ hr⟩
  have hqzero : q 0 = (Path.refl (point z)).cast rfl η.source := by
    apply Path.ext
    funext s
    change η.extend (min (max (s : ℝ) 0) 0) = point z
    rw [min_eq_right (le_max_right _ _), η.extend_zero]
  have hrzero : (r 0).toContinuousMap =
      (γ.trans (Path.refl (f (point z)))).toContinuousMap := by
    apply ContinuousMap.ext
    intro s
    change (γ.trans ((q 0).map f.continuous)) s =
      (γ.trans (Path.refl (f (point z)))) s
    simp only [Path.trans_apply, Path.map_coe, Function.comp_apply, hqzero,
      Path.cast_coe, Path.refl_apply]
  -- The initial appended prefix is constant; remove its extra pause by the
  -- existing right-unit path homotopy, with the retained point fixed.
  let H := (Path.Homotopy.transRefl γ).symm
  have hz0 : Joined z (v 0) := by
    refine ⟨{
      toFun := fun t => mk (point z) (H.toHomotopy.curry t) (H.source t) (H.target t)
      continuous_toFun := continuous_iff.2
        ⟨continuous_const, H.toHomotopy.curry.continuous⟩
      source' := ?_
      target' := ?_ }⟩
    · apply ext
      · rfl
      · exact H.toHomotopy.curry_zero
    · apply ext
      · exact η.source.symm
      · exact H.toHomotopy.curry_one.trans hrzero.symm
  let z' : HomotopyFiber g b :=
    mk e' (r 1).toContinuousMap (r 1).source
      ((r 1).target.trans ((congrArg f η.target).trans (w e')))
  have hv1 : v 1 =
      map (f := g) (f' := f) (b := b) (b' := b)
        u (ContinuousMap.id B) w rfl z' := by
    apply ext
    · exact η.target
    · exact (ContinuousMap.id_comp (r 1).toContinuousMap).symm
  exact ⟨z', hz0.trans ⟨Path.mk ⟨v, hv⟩ rfl hv1⟩⟩

end ContinuousMap.HomotopyFiber

namespace ZerothHomotopy

/-- A component is reached by a map of homotopy fibers over the identity base
map exactly when its retained-point component is reached by the source map.
This fixed-base component-image statement extends the loop-image case of May's
fiber-sequence exactness (Chapter 8, Section 6, pp. 61–62), using ordinary
topologies rather than asserting a comparison with his ambient category. -/
theorem mem_range_map_homotopyFiber_map_id_iff
    (f : C(E, B)) (g : C(E', B)) (u : C(E', E))
    (w : ∀ x, f (u x) = g x) (b : B)
    (c : ZerothHomotopy (ContinuousMap.HomotopyFiber f b)) :
    c ∈ Set.range
        (ZerothHomotopy.map
          (ContinuousMap.HomotopyFiber.map
            (f := g) (f' := f) (b := b) (b' := b)
            u (ContinuousMap.id B) w rfl)) ↔
      ZerothHomotopy.map
          (ContinuousMap.HomotopyFiber.point (f := f) (b := b)) c ∈
        Set.range (ZerothHomotopy.map u) := by
  obtain ⟨z, rfl⟩ := mk_surjective c
  rw [map_mk, mem_range_map_iff, mem_range_map_iff]
  constructor
  · rintro ⟨z', hz'⟩
    refine ⟨ContinuousMap.HomotopyFiber.point z', ?_⟩
    have hpoint := ContinuousMap.HomotopyFiber.point_map
      (f := g) (f' := f) (b := b) (b' := b)
      u (ContinuousMap.id B) w rfl z'
    exact hpoint ▸
      hz'.map (ContinuousMap.HomotopyFiber.point (f := f) (b := b)).continuous
  · rintro ⟨e', ⟨η⟩⟩
    exact ContinuousMap.HomotopyFiber.exists_joined_map_id f g u w b z e' η

/-- The image on path components of a map of homotopy fibers over the identity
base map is the retained-point preimage of the source component image.
This is the fixed-base structural extension of the loop-image exactness in May,
Chapter 8, Section 6 (pp. 61–62), formulated with ordinary topologies. -/
theorem range_map_homotopyFiber_map_id
    (f : C(E, B)) (g : C(E', B)) (u : C(E', E))
    (w : ∀ x, f (u x) = g x) (b : B) :
    Set.range
        (ZerothHomotopy.map
          (ContinuousMap.HomotopyFiber.map
            (f := g) (f' := f) (b := b) (b' := b)
            u (ContinuousMap.id B) w rfl)) =
      (ZerothHomotopy.map
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))) ⁻¹'
          (Set.range (ZerothHomotopy.map u)) := by
  ext c
  exact mem_range_map_homotopyFiber_map_id_iff f g u w b c

/-- The loop classes in the ordinary homotopy fiber are exactly the components
whose retained points belong to the component of the specified source point.
This is the ordinary-topology version of the loop-image part of May's
fiber-sequence exactness, Chapter 8, Section 6 (pp. 61–62); no identification with
his compactly generated model is asserted. The class parameterization uses
Mathlib's unique-index comparison with the fundamental group and
`HomotopyGroup.equivZerothHomotopy`. -/
theorem range_homotopyFiber_loop_classes
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    let S : Type := {j : Unit // j ≠ ()}
    let c : GenLoop S B b := GenLoop.const
    let e : GenLoop S B b ≃ₜ B :=
      @genLoopHomeoOfIsEmpty (N := S) (X := B) (x := b) tB
        (⟨fun j => j.property (Subsingleton.elim j.val ())⟩ : IsEmpty S)
    let L : GenLoop Unit B b ≃ₜ Path c c :=
      GenLoop.loopHomeo (N := Unit) (X := B) (x := b) ()
    let P : C(Path c c, Path b b) :=
      { toFun := fun q => q.map e.continuous
        continuous_toFun :=
          Path.continuous_uncurry_iff.mp
            (e.continuous.comp
              (continuous_eval :
                Continuous
                  (fun z : Path c c × unitInterval => z.1 z.2))) }
    let R : C(GenLoop Unit B b, Path b b) :=
      P.comp (L : C(GenLoop Unit B b, Path c c))
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
    let A : HomotopyGroup Unit B b ≃ FundamentalGroup B b :=
      homotopyGroupEquivFundamentalGroupOfUnique (X := B) (x := b) Unit
    Set.range
        (fun q : FundamentalGroup B b =>
          ZerothHomotopy.map (J.comp R)
            (HomotopyGroup.equivZerothHomotopy Unit b (A.symm q))) =
      (ZerothHomotopy.map
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))) ⁻¹'
          {ZerothHomotopy.mk e₀} := by
  intro S c e L P R J A
  let K := ContinuousMap.HomotopyFiber.map
    (f := ContinuousMap.const Unit b) (f' := f)
    (b := b) (b' := b)
    (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl
  let T : C(Path b b,
      ContinuousMap.HomotopyFiber (ContinuousMap.const Unit b) b) :=
    ((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm :
      C(Unit × Path b b,
        ContinuousMap.HomotopyFiber (ContinuousMap.const Unit b) b)).comp
      ((ContinuousMap.const (Path b b) ()).prodMk
        (ContinuousMap.id (Path b b)))
  -- The selected coordinate recovers the entire forward path.
  have hR : Function.Surjective R := by
    intro γ
    refine ⟨(genLoopEquivOfUnique (X := B) (x := b) Unit).symm γ, ?_⟩
    apply Path.ext
    funext t
    change γ ((Cube.insertAt () (t, (0 : S → unitInterval))) ()) = γ t
    rfl
  have hT : Function.Surjective T := by
    intro z
    obtain ⟨⟨a, γ⟩, rfl⟩ :=
      (ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm.surjective z
    cases a
    exact ⟨γ, rfl⟩
  have hparam : Function.Surjective
      (fun q : FundamentalGroup B b =>
        ZerothHomotopy.map (T.comp R)
          (HomotopyGroup.equivZerothHomotopy Unit b (A.symm q))) :=
    (show Function.Surjective (ZerothHomotopy.map (T.comp R)) from
      Quotient.map_surjective _ (hT.comp hR)).comp
        ((HomotopyGroup.equivZerothHomotopy Unit b).surjective.comp A.symm.surjective)
  have hconst : Set.range (ZerothHomotopy.map (ContinuousMap.const Unit e₀)) =
      {ZerothHomotopy.mk e₀} := by
    have hmap : ZerothHomotopy.map (ContinuousMap.const Unit e₀) =
        fun _ => ZerothHomotopy.mk e₀ := by
      funext q
      obtain ⟨a, rfl⟩ := ZerothHomotopy.mk_surjective q
      rfl
    rw [hmap, Set.range_const]
  calc
    Set.range (fun q : FundamentalGroup B b =>
        ZerothHomotopy.map (J.comp R)
          (HomotopyGroup.equivZerothHomotopy Unit b (A.symm q))) =
        Set.range (fun q : FundamentalGroup B b =>
          ZerothHomotopy.map K
            (ZerothHomotopy.map (T.comp R)
              (HomotopyGroup.equivZerothHomotopy Unit b (A.symm q)))) := by
      congr 1
      funext q
      exact ZerothHomotopy.map_comp K (T.comp R)
        (HomotopyGroup.equivZerothHomotopy Unit b (A.symm q))
    _ = Set.range (ZerothHomotopy.map K) :=
      hparam.range_comp (ZerothHomotopy.map K)
    _ = (ZerothHomotopy.map
          (ContinuousMap.HomotopyFiber.point (f := f) (b := b))) ⁻¹'
            {ZerothHomotopy.mk e₀} := by
      simpa only [hconst] using
        (range_map_homotopyFiber_map_id f
          (ContinuousMap.const Unit b) (ContinuousMap.const Unit e₀)
          (fun _ => h) b)

end ZerothHomotopy

namespace FundamentalGroup

private theorem mem_range_of_joined_homotopyFiber
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (γ : Path b b)
    (hjoined : Joined
      (ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
        e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm))
      (ContinuousMap.HomotopyFiber.const e₀ h)) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∈
      Set.range (FundamentalGroup.mapOfEq (x := e₀) (y := b) f h) := by
  obtain ⟨ζ⟩ := hjoined
  let η : Path e₀ e₀ :=
    ζ.map (ContinuousMap.HomotopyFiber.point (f := f) (b := b)).continuous
  let q : Path b b := Path.refl b
  let H : ContinuousMap.Homotopy γ.toContinuousMap q.toContinuousMap :=
    { toContinuousMap :=
        ((ContinuousMap.HomotopyFiber.path (f := f) (b := b)).comp
          ζ.toContinuousMap).uncurry
      map_zero_left := by
        intro s
        change ContinuousMap.HomotopyFiber.path (ζ 0) s = γ s
        exact congrArg
          (fun z : ContinuousMap.HomotopyFiber f b =>
            ContinuousMap.HomotopyFiber.path z s) ζ.source
      map_one_left := by
        intro s
        change ContinuousMap.HomotopyFiber.path (ζ 1) s = b
        exact congrArg
          (fun z : ContinuousMap.HomotopyFiber f b =>
            ContinuousMap.HomotopyFiber.path z s) ζ.target }
  have hp : (Path.id.map γ.continuous).cast γ.source.symm γ.target.symm = γ := by
    apply Path.ext
    funext s
    rfl
  have hq : (Path.id.map q.continuous).cast q.source.symm q.target.symm = q := by
    apply Path.ext
    funext s
    rfl
  have h0 : (H.evalAt 0).cast γ.source.symm q.source.symm = Path.refl b := by
    apply Path.ext
    funext t
    change ContinuousMap.HomotopyFiber.path (ζ t) 0 = b
    exact ContinuousMap.HomotopyFiber.path_zero (ζ t)
  have h1 : (H.evalAt 1).cast γ.target.symm q.target.symm =
      (η.map f.continuous).cast h.symm h.symm := by
    apply Path.ext
    funext t
    change ContinuousMap.HomotopyFiber.path (ζ t) 1 =
      f (ContinuousMap.HomotopyFiber.point (ζ t))
    exact ContinuousMap.HomotopyFiber.path_one (ζ t)
  -- The moving endpoint traces the mapped point loop; the starting endpoint is fixed.
  have hsquare := (Path.Homotopic.map_trans_evalAt H Path.id).pathCast
    γ.source.symm q.target.symm
  rw [Path.cast_trans _ _ γ.source.symm γ.target.symm q.target.symm,
    Path.cast_trans _ _ γ.source.symm q.source.symm q.target.symm,
    hp, hq, h0, h1] at hsquare
  have hclass :
      (Path.Homotopic.Quotient.mk γ).trans
          (Path.Homotopic.Quotient.mk ((η.map f.continuous).cast h.symm h.symm)) =
        Path.Homotopic.Quotient.refl b := by
    simpa only [q, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans] using
        (Path.Homotopic.Quotient.eq.mpr hsquare)
  have hγ := congrArg
    (fun p : Path.Homotopic.Quotient b b =>
      p.trans
        (Path.Homotopic.Quotient.mk ((η.map f.continuous).cast h.symm h.symm)).symm)
    hclass
  rw [Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.refl_trans] at hγ
  -- Thus γ is the class of the reversed point loop's image, not the point loop's image.
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk η.symm), ?_⟩
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  change Path.Homotopic.Quotient.mk ((η.symm.map f.continuous).cast h.symm h.symm) =
    Path.Homotopic.Quotient.mk γ
  rw [← Path.map_symm, Path.cast_symm, Path.Homotopic.Quotient.mk_symm]
  exact hγ.symm

private theorem joined_homotopyFiber_of_mem_range
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (γ : Path b b)
    (hmem : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∈
      Set.range (FundamentalGroup.mapOfEq (x := e₀) (y := b) f h)) :
    Joined
      (ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
        e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm))
      (ContinuousMap.HomotopyFiber.const e₀ h) := by
  obtain ⟨q, hq⟩ := hmem
  obtain ⟨α, hα⟩ := Path.Homotopic.Quotient.mk_surjective
    (FundamentalGroup.toPath q)
  have hrep : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk α) = q :=
    congrArg FundamentalGroup.fromPath hα
  rw [← hrep, FundamentalGroup.mapOfEq_apply] at hq
  have hγ : γ.Homotopic ((α.map f.continuous).cast h.symm h.symm) := by
    apply Path.Homotopic.Quotient.exact
    simpa only [← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast] using
      congrArg FundamentalGroup.toPath hq.symm
  obtain ⟨H⟩ := hγ
  let zα : ContinuousMap.HomotopyFiber (ContinuousMap.id E) e₀ :=
    ContinuousMap.HomotopyFiber.mk e₀ α.toContinuousMap α.source α.target
  let F : C(ContinuousMap.HomotopyFiber (ContinuousMap.id E) e₀,
      ContinuousMap.HomotopyFiber f b) :=
    ContinuousMap.HomotopyFiber.map
      (f := ContinuousMap.id E) (f' := f) (b := e₀) (b' := b)
      (ContinuousMap.id E) f (fun _ => rfl) h
  -- The change of representative fixes the retained source point.
  have hγmap : Joined
      (ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
        e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm))
      (F zα) := by
    refine ⟨{
      toFun := fun t => ContinuousMap.HomotopyFiber.mk e₀
        (H.toHomotopy.curry t) (H.source t) ((H.target t).trans h.symm)
      continuous_toFun := ContinuousMap.HomotopyFiber.continuous_iff.2
        ⟨continuous_const, H.toHomotopy.curry.continuous⟩
      source' := ?_
      target' := ?_ }⟩
    · apply ContinuousMap.HomotopyFiber.ext
      · rfl
      · exact H.toHomotopy.curry_zero
    · apply ContinuousMap.HomotopyFiber.ext
      · rfl
      · exact H.toHomotopy.curry_one
  -- Contract in the identity fiber, then map the entire joining through the square.
  have hαconst : Joined zα
      (ContinuousMap.HomotopyFiber.const (f := ContinuousMap.id E) e₀ rfl) :=
    ⟨(ContinuousMap.HomotopyFiber.idContraction e₀).toHomotopy.evalAt zα⟩
  have hmapped := hαconst.map F.continuous
  have hFconst :
      F (ContinuousMap.HomotopyFiber.const (f := ContinuousMap.id E) e₀ rfl) =
        ContinuousMap.HomotopyFiber.const (f := f) e₀ h := by
    exact ContinuousMap.HomotopyFiber.map_const
      (f := ContinuousMap.id E) (f' := f) (b := e₀) (b' := b)
      (ContinuousMap.id E) f (fun _ => rfl) h e₀ rfl
  exact hγmap.trans (hFconst ▸ hmapped)

/-- A loop class lies in the image of the induced fundamental-group map exactly
when the homotopy-fiber point retaining that forward loop is joined to the
constant-path point. This is the fundamental-group position of May's
fiber-sequence exactness, Chapter 8, Section 6 (p. 62), with ordinary topologies. -/
theorem mem_range_mapOfEq_iff_joined_homotopyFiber
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (γ : Path b b) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) ∈
        Set.range (FundamentalGroup.mapOfEq (x := e₀) (y := b) f h) ↔
      Joined
        (ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
          e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm))
        (ContinuousMap.HomotopyFiber.const e₀ h) := by
  exact ⟨joined_homotopyFiber_of_mem_range f b e₀ h γ,
    mem_range_of_joined_homotopyFiber f b e₀ h γ⟩

end FundamentalGroup

namespace ZerothHomotopy

/-- The loop-class map of `range_homotopyFiber_loop_classes` sends each based
loop class to the component of the homotopy-fiber point retaining that same
forward loop at the specified source point. This describes the loop inclusion
in May, Chapter 8, Section 6 (pp. 61–62), for ordinary topologies. -/
theorem homotopyFiber_loop_classes_fromPath
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (γ : Path b b) :
    let S : Type := {j : Unit // j ≠ ()}
    let c : GenLoop S B b := GenLoop.const
    let e : GenLoop S B b ≃ₜ B :=
      @genLoopHomeoOfIsEmpty (N := S) (X := B) (x := b) tB
        (⟨fun j => j.property (Subsingleton.elim j.val ())⟩ : IsEmpty S)
    let L : GenLoop Unit B b ≃ₜ Path c c :=
      GenLoop.loopHomeo (N := Unit) (X := B) (x := b) ()
    let P : C(Path c c, Path b b) :=
      { toFun := fun q => q.map e.continuous
        continuous_toFun :=
          Path.continuous_uncurry_iff.mp
            (e.continuous.comp
              (continuous_eval :
                Continuous
                  (fun z : Path c c × unitInterval => z.1 z.2))) }
    let R : C(GenLoop Unit B b, Path b b) :=
      P.comp (L : C(GenLoop Unit B b, Path c c))
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
    let A : HomotopyGroup Unit B b ≃ FundamentalGroup B b :=
      homotopyGroupEquivFundamentalGroupOfUnique (X := B) (x := b) Unit
    (fun q : FundamentalGroup B b =>
      ZerothHomotopy.map (J.comp R)
        (HomotopyGroup.equivZerothHomotopy Unit b (A.symm q)))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      ZerothHomotopy.mk
        (ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
          e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm)) := by
  intro S c e L P R J A
  let U := genLoopEquivOfUnique (X := B) (x := b) Unit
  let p : GenLoop Unit B b := U.symm γ
  have hA : A.symm (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      (⟦p⟧ : HomotopyGroup Unit B b) := by
    have hquot : A (⟦p⟧ : HomotopyGroup Unit B b) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (U p)) :=
      Quotient.congr_mk
        (ra := GenLoop.Homotopic.setoid Unit b)
        (rb := Path.Homotopic.setoid b b) U _ p
    apply A.symm_apply_eq.mpr
    exact (congrArg (fun q : Path b b =>
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q))
        (U.apply_symm_apply γ).symm).trans hquot.symm
  -- The original parameterization recovers this entire forward loop.
  have hR : R p = γ := by
    apply Path.ext
    funext t
    change γ ((Cube.insertAt () (t, (0 : S → unitInterval))) ()) = γ t
    rfl
  have hJ : J γ =
      ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
        e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm) := by
    apply ContinuousMap.HomotopyFiber.ext
    · exact ContinuousMap.HomotopyFiber.point_map
        (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl
        ((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm ((), γ))
    · apply ContinuousMap.ext
      intro t
      exact (DFunLike.congr_fun
        (ContinuousMap.HomotopyFiber.path_map
          (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
          (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl
          ((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm ((), γ)))
        t).trans
          (ContinuousMap.HomotopyFiber.constHomeomorph_symm_path_apply ((), γ) t)
  change ZerothHomotopy.map (J.comp R)
      (HomotopyGroup.equivZerothHomotopy Unit b
        (A.symm (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) = _
  rw [hA, HomotopyGroup.equivZerothHomotopy_class, ZerothHomotopy.map_mk,
    ContinuousMap.comp_apply, hR, hJ]

/-- The preimage of the constant-loop image under the loop-class map is the
image of the induced fundamental-group homomorphism. This is pointed-set
exactness at the fundamental group in May, Chapter 8, Section 6 (p. 62), with
ordinary topologies. May writes the preceding arrow as `−Ωf`; its group image
agrees with that of `FundamentalGroup.mapOfEq f h`, while the forward-loop
convention of the loop-class map is unchanged. -/
theorem preimage_homotopyFiber_loop_classes_one
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    let S : Type := {j : Unit // j ≠ ()}
    let c : GenLoop S B b := GenLoop.const
    let e : GenLoop S B b ≃ₜ B :=
      @genLoopHomeoOfIsEmpty (N := S) (X := B) (x := b) tB
        (⟨fun j => j.property (Subsingleton.elim j.val ())⟩ : IsEmpty S)
    let L : GenLoop Unit B b ≃ₜ Path c c :=
      GenLoop.loopHomeo (N := Unit) (X := B) (x := b) ()
    let P : C(Path c c, Path b b) :=
      { toFun := fun q => q.map e.continuous
        continuous_toFun :=
          Path.continuous_uncurry_iff.mp
            (e.continuous.comp
              (continuous_eval :
                Continuous
                  (fun z : Path c c × unitInterval => z.1 z.2))) }
    let R : C(GenLoop Unit B b, Path b b) :=
      P.comp (L : C(GenLoop Unit B b, Path c c))
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
    let A : HomotopyGroup Unit B b ≃ FundamentalGroup B b :=
      homotopyGroupEquivFundamentalGroupOfUnique (X := B) (x := b) Unit
    let delta : FundamentalGroup B b → ZerothHomotopy (ContinuousMap.HomotopyFiber f b) :=
      fun q => ZerothHomotopy.map (J.comp R)
        (HomotopyGroup.equivZerothHomotopy Unit b (A.symm q))
    delta ⁻¹' {delta 1} =
      Set.range (FundamentalGroup.mapOfEq (x := e₀) (y := b) f h) := by
  intro S c e L P R J A delta
  have hdelta (γ : Path b b) :
      delta (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
        ZerothHomotopy.mk
          (ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
            e₀ γ.toContinuousMap γ.source (γ.target.trans h.symm)) :=
    homotopyFiber_loop_classes_fromPath f b e₀ h γ
  have hdelta_one :
      delta 1 = ZerothHomotopy.mk (ContinuousMap.HomotopyFiber.const e₀ h) := by
    have hone :
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl b)) =
          (1 : FundamentalGroup B b) := by
      calc
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl b)) =
            FundamentalGroup.fromPath (Path.Homotopic.Quotient.refl b) :=
          congrArg (FundamentalGroup.fromPath :
            Path.Homotopic.Quotient b b → FundamentalGroup B b)
              (Path.Homotopic.Quotient.mk_refl b)
        _ = 1 := (FundamentalGroup.one_def (x := b)).symm
    have hconst :
        ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
            e₀ (Path.refl b).toContinuousMap (Path.refl b).source
              ((Path.refl b).target.trans h.symm) =
          ContinuousMap.HomotopyFiber.const e₀ h := by
      apply ContinuousMap.HomotopyFiber.ext
      · exact (ContinuousMap.HomotopyFiber.point_mk (f := f) (b := b)
          e₀ _ _ _).trans
            (ContinuousMap.HomotopyFiber.point_const (f := f) e₀ h).symm
      · apply ContinuousMap.ext
        intro t
        exact (DFunLike.congr_fun
          (ContinuousMap.HomotopyFiber.path_mk (f := f) (b := b)
            e₀ (Path.refl b).toContinuousMap (Path.refl b).source
              ((Path.refl b).target.trans h.symm)) t).trans
          ((Path.refl_apply b t).trans
            (DFunLike.congr_fun
              (ContinuousMap.HomotopyFiber.path_const (f := f) e₀ h) t).symm)
    calc
      delta 1 = delta
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl b))) :=
        congrArg delta hone.symm
      _ = ZerothHomotopy.mk
          (ContinuousMap.HomotopyFiber.mk (f := f) (b := b)
            e₀ (Path.refl b).toContinuousMap (Path.refl b).source
              ((Path.refl b).target.trans h.symm)) := hdelta (Path.refl b)
      _ = ZerothHomotopy.mk (ContinuousMap.HomotopyFiber.const e₀ h) :=
        congrArg (ZerothHomotopy.mk :
          ContinuousMap.HomotopyFiber f b →
            ZerothHomotopy (ContinuousMap.HomotopyFiber f b)) hconst
  ext q
  change delta q = delta 1 ↔
    q ∈ Set.range (FundamentalGroup.mapOfEq (x := e₀) (y := b) f h)
  induction q using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rw [hdelta γ, hdelta_one]
    exact Quotient.eq.trans
      (FundamentalGroup.mem_range_mapOfEq_iff_joined_homotopyFiber f b e₀ h γ).symm

end ZerothHomotopy

namespace HomotopyGroup

universe uI

private theorem exists_genLoop_homotopyFiber_point (N : Type uI)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (α : GenLoop N E e₀)
    (H : (GenLoop.const : GenLoop N B b).val.HomotopyRel
      (GenLoop.map f h α).val (Cube.boundary N)) :
    ∃ β : GenLoop N (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h),
      GenLoop.map (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) β = α := by
  let γ : C((N → unitInterval), C(unitInterval, B)) :=
    (⟨fun p : (N → unitInterval) × unitInterval => H (p.2, p.1),
      H.continuous.comp continuous_swap⟩ : C((N → unitInterval) × unitInterval, B)).curry
  have hγ (x : N → unitInterval) (t : unitInterval) : γ x t = H (t, x) := rfl
  have hγ₀ (x : N → unitInterval) : γ x 0 = b := by
    calc
      γ x 0 = H (0, x) := hγ x 0
      _ = (GenLoop.const : GenLoop N B b).val x :=
        ContinuousMap.HomotopyWith.apply_zero H x
      _ = (GenLoop.const : GenLoop N B b) x :=
        congrFun (GenLoop.coe_coe (GenLoop.const : GenLoop N B b)) x
      _ = b := GenLoop.const_apply
  have hγ₁ (x : N → unitInterval) : γ x 1 = f (α x) := by
    rw [hγ]
    simpa only [GenLoop.coe_coe, GenLoop.map_apply] using H.apply_one x
  let k : (N → unitInterval) → ContinuousMap.HomotopyFiber f b := fun x =>
    ContinuousMap.HomotopyFiber.mk (α x) (γ x) (hγ₀ x) (hγ₁ x)
  have hk : Continuous k := by
    apply ContinuousMap.HomotopyFiber.continuous_iff.2
    constructor
    · simpa only [k, ContinuousMap.HomotopyFiber.point_mk, GenLoop.coe_coe] using
        α.val.continuous
    · simpa only [k, ContinuousMap.HomotopyFiber.path_mk] using γ.continuous
  have hk_boundary (x : N → unitInterval) (hx : x ∈ Cube.boundary N) :
      k x = ContinuousMap.HomotopyFiber.const e₀ h := by
    apply ContinuousMap.HomotopyFiber.ext
    · simpa only [k, ContinuousMap.HomotopyFiber.point_mk,
        ContinuousMap.HomotopyFiber.point_const] using GenLoop.boundary α x hx
    · apply ContinuousMap.ext
      intro t
      simpa only [k, ContinuousMap.HomotopyFiber.path_mk,
        ContinuousMap.HomotopyFiber.path_const, ContinuousMap.const_apply, hγ,
        GenLoop.coe_coe, GenLoop.const_apply] using
        H.eq_fst t hx
  refine ⟨⟨⟨k, hk⟩, hk_boundary⟩, ?_⟩
  apply GenLoop.ext
  intro x
  exact ContinuousMap.HomotopyFiber.point_mk (α x) (γ x) (hγ₀ x) (hγ₁ x)

private theorem homotopic_const_map_homotopyFiber_point (N : Type uI)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (β : GenLoop N (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h)) :
    GenLoop.Homotopic (GenLoop.const : GenLoop N B b)
      (GenLoop.map f h
        (GenLoop.map (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
          (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) β)) := by
  refine ⟨{
    toFun := fun z => ContinuousMap.HomotopyFiber.path (β z.2) z.1
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩
  · exact (continuous_eval :
        Continuous (fun z : C(unitInterval, B) × unitInterval => z.1 z.2)).comp
      (((ContinuousMap.HomotopyFiber.path (f := f) (b := b)).continuous.comp
        (β.val.continuous.comp continuous_snd)).prodMk continuous_fst)
  · intro x
    simpa only [GenLoop.coe_coe, GenLoop.const_apply] using
      (ContinuousMap.HomotopyFiber.path_zero (β x))
  · intro x
    simpa only [GenLoop.coe_coe, GenLoop.map_apply] using
      (ContinuousMap.HomotopyFiber.path_one (β x))
  · intro t x hx
    change ContinuousMap.HomotopyFiber.path (β x) t = b
    rw [GenLoop.boundary β x hx, ContinuousMap.HomotopyFiber.path_const]
    rfl

/-- For every cube index, the image of the based homotopy-fiber point projection
consists exactly of the generalized-loop classes sent by `f` to the constant
class. The fiber retains paths from `b` to `f e` and is based at
`ContinuousMap.HomotopyFiber.const e₀ h`. No index instances are required.

The finite-dimensional case adapts the projection position of fiber-sequence
exactness in J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, §6,
printed pp. 61–62 (PDF pp. 69–70), especially printed p. 62, using ordinary
topologies. Empty indices retain all path components; infinite-index quotients
are already subsingletons. -/
theorem range_mapFun_homotopyFiber_point (N : Type uI)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    Set.range
        (HomotopyGroup.mapFun N
          (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
          (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h)) =
      (HomotopyGroup.mapFun N f h) ⁻¹' {(⟦GenLoop.const⟧ : HomotopyGroup N B b)} := by
  ext c
  change (∃ q, HomotopyGroup.mapFun N
      (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
      (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) q = c) ↔
    HomotopyGroup.mapFun N f h c = (⟦GenLoop.const⟧ : HomotopyGroup N B b)
  constructor
  · rintro ⟨q, rfl⟩
    refine Quotient.inductionOn
      (motive := fun q : HomotopyGroup N (ContinuousMap.HomotopyFiber f b)
          (ContinuousMap.HomotopyFiber.const e₀ h) =>
        HomotopyGroup.mapFun N f h
          (HomotopyGroup.mapFun N
            (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
            (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) q) =
          (⟦GenLoop.const⟧ : HomotopyGroup N B b)) q ?_
    intro β
    simp only [mapFun_class]
    exact Quotient.sound
      (GenLoop.Homotopic.symm
        (homotopic_const_map_homotopyFiber_point N f b e₀ h β))
  · refine Quotient.inductionOn
      (motive := fun c : HomotopyGroup N E e₀ =>
        HomotopyGroup.mapFun N f h c = (⟦GenLoop.const⟧ : HomotopyGroup N B b) →
          ∃ q, HomotopyGroup.mapFun N
            (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
            (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) q = c)
      c ?_
    intro α hα
    rw [mapFun_class] at hα
    have hhom : GenLoop.Homotopic (GenLoop.map f h α)
        (GenLoop.const : GenLoop N B b) := Quotient.exact hα
    rcases hhom with ⟨H⟩
    obtain ⟨β, hβ⟩ := exists_genLoop_homotopyFiber_point N f b e₀ h α H.symm
    refine ⟨(⟦β⟧ : HomotopyGroup N (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h)), ?_⟩
    rw [mapFun_class, hβ]

/-- For a nonempty cube index with decidable equality, the image of the based
homotopy-fiber point projection is the kernel of the homomorphism induced by
`f`. The fiber is based at `ContinuousMap.HomotopyFiber.const e₀ h`. The supplied
`[DecidableEq N] [Nonempty N]` provide the existing group structures and induced
homomorphisms, not geometric hypotheses on the spaces.

The finite-dimensional case adapts the projection position in J. P. May,
*A Concise Course in Algebraic Topology*, Chapter 8, §6, printed pp. 61–62
(PDF pp. 69–70), especially printed p. 62, using ordinary topologies. -/
theorem range_map_homotopyFiber_point (N : Type uI) [DecidableEq N] [Nonempty N]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    (HomotopyGroup.map N
      (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
      (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h)).range =
      (HomotopyGroup.map N f h).ker := by
  apply SetLike.coe_injective
  change Set.range
      (HomotopyGroup.map N
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) :
        HomotopyGroup N (ContinuousMap.HomotopyFiber f b)
          (ContinuousMap.HomotopyFiber.const e₀ h) → HomotopyGroup N E e₀) =
    {c : HomotopyGroup N E e₀ | HomotopyGroup.map N f h c = 1}
  rw [HomotopyGroup.coe_map_eq_mapFun, range_mapFun_homotopyFiber_point]
  ext c
  change HomotopyGroup.mapFun N f h c =
      (⟦GenLoop.const⟧ : HomotopyGroup N B b) ↔
    HomotopyGroup.map N f h c = 1
  rw [← HomotopyGroup.one_def (N := N) (X := B) (x := b)]
  rfl

end HomotopyGroup

namespace HomotopyGroup

universe uN

-- The right-unit correction is independent of the projected nullhomotopy.
-- Its witness is kept abstract in the prefix-family argument below.
private theorem exists_genLoop_homotopic_homotopyFiber_rightUnit (N : Type uN)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (α : GenLoop N (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h)) :
    ∃ αunit : GenLoop N (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h),
      GenLoop.Homotopic α αunit ∧
      (∀ x, ContinuousMap.HomotopyFiber.point (αunit x) =
        ContinuousMap.HomotopyFiber.point (α x)) ∧
      (∀ x t, ContinuousMap.HomotopyFiber.path (αunit x) t =
        ContinuousMap.HomotopyFiber.path (α x) ((Path.id.trans (Path.refl 1)) t)) := by
  let a : ∀ x : N → unitInterval,
      Path b (f (ContinuousMap.HomotopyFiber.point (α x))) := fun x =>
    Path.mk (ContinuousMap.HomotopyFiber.path (α x))
      (ContinuousMap.HomotopyFiber.path_zero (α x))
      (ContinuousMap.HomotopyFiber.path_one (α x))
  have ha : Continuous (fun z : (N → unitInterval) × unitInterval => a z.1 z.2) :=
    (continuous_eval : Continuous (fun z : C(unitInterval, B) × unitInterval =>
      z.1 z.2)).comp
        (((ContinuousMap.HomotopyFiber.path (f := f) (b := b)).continuous.comp
          (α.val.continuous.comp continuous_fst)).prodMk continuous_snd)
  let U := (Path.Homotopy.transRefl Path.id).symm
  let W : unitInterval × (N → unitInterval) → ContinuousMap.HomotopyFiber f b := fun z =>
    ContinuousMap.HomotopyFiber.mk (ContinuousMap.HomotopyFiber.point (α z.2))
      ((a z.2).toContinuousMap.comp (U.toHomotopy.curry z.1))
      (by
        change a z.2 (U (z.1, 0)) = b
        rw [U.source]
        exact (a z.2).source)
      (by
        change a z.2 (U (z.1, 1)) = f (ContinuousMap.HomotopyFiber.point (α z.2))
        rw [U.target]
        exact (a z.2).target)
  have hW : Continuous W := by
    apply ContinuousMap.HomotopyFiber.continuous_iff.2
    constructor
    · change Continuous (fun z : unitInterval × (N → unitInterval) =>
        ContinuousMap.HomotopyFiber.point (α z.2))
      exact (ContinuousMap.HomotopyFiber.point (f := f) (b := b)).continuous.comp
        (α.val.continuous.comp continuous_snd)
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (unitInterval × (N → unitInterval)) × unitInterval =>
        a z.1.2 (U (z.1.1, z.2)))
      exact ha.comp ((continuous_snd.comp continuous_fst).prodMk
        (U.continuous.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)))
  have hW₀ (x : N → unitInterval) : W (0, x) = α x := by
    apply ContinuousMap.HomotopyFiber.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      change a x (U (0, t)) = ContinuousMap.HomotopyFiber.path (α x) t
      rw [U.apply_zero]
      rfl
  have hW_boundary (s : unitInterval) (x : N → unitInterval)
      (hx : x ∈ Cube.boundary N) : W (s, x) = α x := by
    apply ContinuousMap.HomotopyFiber.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      change ContinuousMap.HomotopyFiber.path (α x) (U (s, t)) =
        ContinuousMap.HomotopyFiber.path (α x) t
      rw [GenLoop.boundary α x hx, ContinuousMap.HomotopyFiber.path_const]
      rfl
  let αunit : GenLoop N (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h) :=
    ⟨⟨fun x => W (1, x), hW.comp (continuous_const.prodMk continuous_id)⟩,
      fun x hx => (hW_boundary 1 x hx).trans (GenLoop.boundary α x hx)⟩
  have hunit : GenLoop.Homotopic α αunit :=
    ⟨{ toFun := W
       continuous_toFun := hW
       map_zero_left := hW₀
       map_one_left := fun _ => rfl
       prop' := hW_boundary }⟩
  refine ⟨αunit, hunit, ?_, ?_⟩
  · intro x
    rfl
  · intro x t
    change a x (U (1, t)) = a x ((Path.id.trans (Path.refl 1)) t)
    rw [U.apply_one]
    rfl

-- Build the joint prefix family separately from either homotopy packaging.
-- Only its endpoint coordinates and relative boundary law escape this proof.
private theorem exists_homotopyFiber_prefix_family (N : Type uN)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (α : GenLoop N (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h))
    (H : (GenLoop.map (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) α).val.HomotopyRel
      (GenLoop.const : GenLoop N E e₀).val (Cube.boundary N)) :
    ∃ v : C(unitInterval × (N → unitInterval), ContinuousMap.HomotopyFiber f b),
      (∀ x, ContinuousMap.HomotopyFiber.point (v (0, x)) =
        ContinuousMap.HomotopyFiber.point (α x)) ∧
      (∀ x t, ContinuousMap.HomotopyFiber.path (v (0, x)) t =
        ContinuousMap.HomotopyFiber.path (α x) ((Path.id.trans (Path.refl 1)) t)) ∧
      (∀ x, ContinuousMap.HomotopyFiber.point (v (1, x)) = e₀) ∧
      (∀ s x, x ∈ Cube.boundary N →
        v (s, x) = ContinuousMap.HomotopyFiber.const e₀ h) := by
  have hH₀ (x : N → unitInterval) :
      H (0, x) = ContinuousMap.HomotopyFiber.point (α x) := by
    exact Eq.trans (α := E) (H.apply_zero x)
      (GenLoop.map_apply
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) α x)
  have hH₁ (x : N → unitInterval) : H (1, x) = e₀ := by
    exact Eq.trans (α := E) (H.apply_one x)
      (GenLoop.const_apply (N := N) (X := E) (x := e₀) (t := x))
  have hH_boundary (s : unitInterval) (x : N → unitInterval)
      (hx : x ∈ Cube.boundary N) : H (s, x) = e₀ := by
    exact Eq.trans (α := E) (H.eq_snd s hx)
      (GenLoop.const_apply (N := N) (X := E) (x := e₀) (t := x))
  let a : ∀ x : N → unitInterval,
      Path b (f (ContinuousMap.HomotopyFiber.point (α x))) := fun x =>
    Path.mk (ContinuousMap.HomotopyFiber.path (α x))
      (ContinuousMap.HomotopyFiber.path_zero (α x))
      (ContinuousMap.HomotopyFiber.path_one (α x))
  have ha : Continuous (fun z : (N → unitInterval) × unitInterval => a z.1 z.2) :=
    (continuous_eval : Continuous (fun z : C(unitInterval, B) × unitInterval =>
      z.1 z.2)).comp
        (((ContinuousMap.HomotopyFiber.path (f := f) (b := b)).continuous.comp
          (α.val.continuous.comp continuous_fst)).prodMk continuous_snd)
  have hscale : Continuous
      (fun z : (unitInterval × (N → unitInterval)) × unitInterval =>
        (z.1.1 * z.2, z.1.2)) :=
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _).prodMk
        (continuous_snd.comp continuous_fst)
  let q : ∀ z : unitInterval × (N → unitInterval),
      Path (ContinuousMap.HomotopyFiber.point (α z.2)) (H z) := fun z =>
    { toFun := fun t => H (z.1 * t, z.2)
      continuous_toFun := (H.continuous.comp hscale).comp
        (continuous_const.prodMk continuous_id)
      source' := by simpa only [mul_zero] using hH₀ z.2
      target' := by simp only [mul_one] }
  have hq : Continuous
      (fun z : (unitInterval × (N → unitInterval)) × unitInterval => q z.1 z.2) :=
    H.continuous.comp hscale
  let r : ∀ z : unitInterval × (N → unitInterval), Path b (f (H z)) := fun z =>
    (a z.2).trans ((q z).map f.continuous)
  have hr : Continuous
      (fun z : (unitInterval × (N → unitInterval)) × unitInterval => r z.1 z.2) :=
    Path.trans_continuous_family (fun z => a z.2)
      (ha.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      (fun z => (q z).map f.continuous) (f.continuous.comp hq)
  have hr_boundary (s : unitInterval) (x : N → unitInterval)
      (hx : x ∈ Cube.boundary N) (t : unitInterval) : r (s, x) t = b := by
    change ((a x).trans ((q (s, x)).map f.continuous)) t = b
    rw [Path.trans_apply]
    split_ifs
    · change ContinuousMap.HomotopyFiber.path (α x) _ = b
      rw [GenLoop.boundary α x hx, ContinuousMap.HomotopyFiber.path_const]
      rfl
    · change f (H (s * _, x)) = b
      rw [hH_boundary _ x hx, h]
  let v : unitInterval × (N → unitInterval) → ContinuousMap.HomotopyFiber f b := fun z =>
    ContinuousMap.HomotopyFiber.mk (H z) (r z).toContinuousMap (r z).source (r z).target
  have hv : Continuous v := ContinuousMap.HomotopyFiber.continuous_iff.2
    ⟨H.continuous, ContinuousMap.continuous_of_continuous_uncurry _ hr⟩
  refine ⟨⟨v, hv⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    exact hH₀ x
  · intro x t
    change ((a x).trans ((q (0, x)).map f.continuous)) t =
      a x ((Path.id.trans (Path.refl 1)) t)
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs
    · rfl
    · change f (H (0 * _, x)) = a x 1
      rw [zero_mul, hH₀]
      exact (a x).target.symm
  · intro x
    exact hH₁ x
  · intro s x hx
    apply ContinuousMap.HomotopyFiber.ext
    · exact hH_boundary s x hx
    · apply ContinuousMap.ext
      intro t
      exact hr_boundary s x hx t

-- Here v is a variable, not a reducible prefix-family constructor. Loop-space
-- currying and the endpoint homotopy therefore use just the characteristic laws.
private theorem exists_genLoop_homotopic_homotopyFiber_family (N : Type uN)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (J : C(Path b b, ContinuousMap.HomotopyFiber f b))
    (J_refl : J (Path.refl b) = ContinuousMap.HomotopyFiber.const e₀ h)
    (J_point : ∀ γ, ContinuousMap.HomotopyFiber.point (J γ) = e₀)
    (J_path : ∀ γ t, ContinuousMap.HomotopyFiber.path (J γ) t = γ t)
    (αunit : GenLoop N (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h))
    (v : C(unitInterval × (N → unitInterval), ContinuousMap.HomotopyFiber f b))
    (hv₀ : ∀ x, v (0, x) = αunit x)
    (hv₁ : ∀ x, ContinuousMap.HomotopyFiber.point (v (1, x)) = e₀)
    (hv_boundary : ∀ s x, x ∈ Cube.boundary N →
      v (s, x) = ContinuousMap.HomotopyFiber.const e₀ h) :
    ∃ β : GenLoop N (Path b b) (Path.refl b),
      GenLoop.Homotopic αunit (GenLoop.map J J_refl β) := by
  let ℓ : (N → unitInterval) → Path b b := fun x =>
    Path.mk (ContinuousMap.HomotopyFiber.path (v (1, x)))
      (ContinuousMap.HomotopyFiber.path_zero (v (1, x)))
      ((ContinuousMap.HomotopyFiber.path_one (v (1, x))).trans
        ((congrArg f (hv₁ x)).trans h))
  have hpath : Continuous (fun z : (N → unitInterval) × unitInterval =>
      ContinuousMap.HomotopyFiber.path (v (1, z.1)) z.2) :=
    (continuous_eval : Continuous (fun z : C(unitInterval, B) × unitInterval =>
      z.1 z.2)).comp
        (((ContinuousMap.HomotopyFiber.path (f := f) (b := b)).continuous.comp
          (v.continuous.comp (continuous_const.prodMk continuous_fst))).prodMk continuous_snd)
  have hℓ : Continuous ℓ := Path.continuous_uncurry_iff.mp hpath
  have hℓ_boundary (x : N → unitInterval) (hx : x ∈ Cube.boundary N) :
      ℓ x = Path.refl b := by
    apply Path.ext
    funext t
    change ContinuousMap.HomotopyFiber.path (v (1, x)) t = b
    rw [hv_boundary 1 x hx, ContinuousMap.HomotopyFiber.path_const]
    rfl
  let β : GenLoop N (Path b b) (Path.refl b) := ⟨⟨ℓ, hℓ⟩, hℓ_boundary⟩
  have hvJ (x : N → unitInterval) : v (1, x) = J (β x) := by
    apply ContinuousMap.HomotopyFiber.ext
    · exact (hv₁ x).trans (J_point (β x)).symm
    · apply ContinuousMap.ext
      intro t
      exact (J_path (β x) t).symm
  refine ⟨β, ⟨{
    toFun := v
    continuous_toFun := v.continuous
    map_zero_left := hv₀
    map_one_left := hvJ
    prop' := ?_ }⟩⟩
  intro s x hx
  exact (hv_boundary s x hx).trans (GenLoop.boundary αunit x hx).symm

private theorem exists_genLoop_homotopic_homotopyFiber_loop (N : Type uN)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (J : C(Path b b, ContinuousMap.HomotopyFiber f b))
    (J_refl : J (Path.refl b) = ContinuousMap.HomotopyFiber.const e₀ h)
    (J_point : ∀ γ, ContinuousMap.HomotopyFiber.point (J γ) = e₀)
    (J_path : ∀ γ t, ContinuousMap.HomotopyFiber.path (J γ) t = γ t)
    (α : GenLoop N (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h))
    (H : (GenLoop.map (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) α).val.HomotopyRel
      (GenLoop.const : GenLoop N E e₀).val (Cube.boundary N)) :
    ∃ β : GenLoop N (Path b b) (Path.refl b),
      GenLoop.Homotopic (GenLoop.map J J_refl β) α := by
  obtain ⟨αunit, hunit, hunit_point, hunit_path⟩ :=
    exists_genLoop_homotopic_homotopyFiber_rightUnit N f b e₀ h α
  obtain ⟨v, hv_point, hv_path, hv₁, hv_boundary⟩ :=
    exists_homotopyFiber_prefix_family N f b e₀ h α H
  have hv₀ (x : N → unitInterval) : v (0, x) = αunit x := by
    apply ContinuousMap.HomotopyFiber.ext
    · exact (hv_point x).trans (hunit_point x).symm
    · apply ContinuousMap.ext
      intro t
      exact (hv_path x t).trans (hunit_path x t).symm
  obtain ⟨β, hβ⟩ := exists_genLoop_homotopic_homotopyFiber_family
    N f b e₀ h J J_refl J_point J_path αunit v hv₀ hv₁ hv_boundary
  exact ⟨β, (hunit.trans hβ).symm⟩

/-- For every cube index, the image of the loop inclusion into the ordinary homotopy
fiber consists exactly of the classes whose retained-point classes are constant.
The loop space is `Path b b`, based at `Path.refl b`; the inclusion retains the
whole forward loop at `e₀`. No index instances are required.

The finite-dimensional case adapts the homotopy-fiber position of fiber-sequence
exactness in J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, §6,
printed pp. 61–62 (PDF pp. 69–70), especially printed p. 62, using ordinary
topologies. The arbitrary-index formula is a cubical extension. -/
theorem range_mapFun_homotopyFiber_loop (N : Type uN)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
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
    let J_refl : J (Path.refl b) =
        ContinuousMap.HomotopyFiber.const (f := f) (b := b) e₀ h := by
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
    Set.range (HomotopyGroup.mapFun N J J_refl) =
      (HomotopyGroup.mapFun N
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h)) ⁻¹'
          {(⟦GenLoop.const⟧ : HomotopyGroup N E e₀)} := by
  intro J J_refl
  have J_point (γ : Path b b) :
      ContinuousMap.HomotopyFiber.point (J γ) = e₀ := by
    exact ContinuousMap.HomotopyFiber.point_map
      (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
      (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl
      ((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm ((), γ))
  have J_path (γ : Path b b) (t : unitInterval) :
      ContinuousMap.HomotopyFiber.path (J γ) t = γ t := by
    exact (DFunLike.congr_fun
      (ContinuousMap.HomotopyFiber.path_map
        (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
        (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl
        ((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm ((), γ)))
      t).trans
        (ContinuousMap.HomotopyFiber.constHomeomorph_symm_path_apply ((), γ) t)
  have hpoint :
      (ContinuousMap.HomotopyFiber.point (f := f) (b := b)).comp J =
        ContinuousMap.const (Path b b) e₀ := by
    apply ContinuousMap.ext
    intro γ
    exact J_point γ
  have hcomm :
      (HomotopyGroup.mapFun N
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h)) ∘
          (HomotopyGroup.mapFun N J J_refl) =
        fun _ : HomotopyGroup N (Path b b) (Path.refl b) =>
          (⟦GenLoop.const⟧ : HomotopyGroup N E e₀) := by
    funext q
    refine Eq.trans (α := HomotopyGroup N E e₀)
      (congrFun (HomotopyGroup.mapFun_comp N
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h)
        J J_refl).symm q) ?_
    refine Eq.trans (α := HomotopyGroup N E e₀)
      (congrFun (HomotopyGroup.mapFun_congr N hpoint
        ((congrArg
          (ContinuousMap.HomotopyFiber.point (f := f) (b := b)) J_refl).trans
            (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h))
        (by simp only [ContinuousMap.const_apply])) q) ?_
    exact congrFun (HomotopyGroup.mapFun_const_map N
      (X := Path b b) (Y := E) (x := Path.refl b) (y := e₀)) q
  ext c
  change (∃ q, HomotopyGroup.mapFun N J J_refl q = c) ↔
    HomotopyGroup.mapFun N
      (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
      (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) c =
        (⟦GenLoop.const⟧ : HomotopyGroup N E e₀)
  constructor
  · rintro ⟨q, rfl⟩
    exact congrFun hcomm q
  · refine Quotient.inductionOn
      (motive := fun c : HomotopyGroup N (ContinuousMap.HomotopyFiber f b)
          (ContinuousMap.HomotopyFiber.const e₀ h) =>
        HomotopyGroup.mapFun N
          (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
          (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) c =
            (⟦GenLoop.const⟧ : HomotopyGroup N E e₀) →
          ∃ q, HomotopyGroup.mapFun N J J_refl q = c)
      c ?_
    intro α hα
    rw [HomotopyGroup.mapFun_class] at hα
    have hhom : GenLoop.Homotopic
        (GenLoop.map (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
          (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) α)
        (GenLoop.const : GenLoop N E e₀) := Quotient.eq.mp hα
    rcases hhom with ⟨H⟩
    obtain ⟨β, hβ⟩ := exists_genLoop_homotopic_homotopyFiber_loop
      N f b e₀ h J J_refl J_point J_path α H
    refine ⟨(⟦β⟧ : HomotopyGroup N (Path b b) (Path.refl b)), ?_⟩
    rw [HomotopyGroup.mapFun_class]
    exact Quotient.sound hβ

/-- For a nonempty cube index with decidable equality, the image of the loop inclusion
is the kernel of the homotopy-fiber point projection. The supplied
`[DecidableEq N] [Nonempty N]` give the existing group structures and homomorphisms;
no geometric hypotheses on the spaces are imposed. The inclusion retains the
whole forward loop, and the fiber is based at `ContinuousMap.HomotopyFiber.const e₀ h`.

The finite-dimensional case adapts the homotopy-fiber position in J. P. May,
*A Concise Course in Algebraic Topology*, Chapter 8, §6, printed pp. 61–62
(PDF pp. 69–70), especially printed p. 62, using ordinary topologies. -/
theorem range_map_homotopyFiber_loop (N : Type uN) [DecidableEq N] [Nonempty N]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
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
    let J_refl : J (Path.refl b) =
        ContinuousMap.HomotopyFiber.const (f := f) (b := b) e₀ h := by
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
    (HomotopyGroup.map N J J_refl).range =
      (HomotopyGroup.map N
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h)).ker := by
  intro J J_refl
  apply SetLike.coe_injective
  rw [MonoidHom.coe_range, MonoidHom.coe_ker]
  simp only [HomotopyGroup.coe_map_eq_mapFun, HomotopyGroup.one_def]
  dsimp only [J]
  exact range_mapFun_homotopyFiber_loop N f b e₀ h

end HomotopyGroup

namespace ZerothHomotopy

/-- On all path components of the based loop space, the loop inclusion has image
exactly the components of the ordinary homotopy fiber whose retained points lie
in the component of `e₀`. This is the empty-index consequence of
`HomotopyGroup.range_mapFun_homotopyFiber_loop`, with the same whole forward loop
and ordinary topologies. It gives the loop-image position of May's fiber-sequence
exactness, Chapter 8, Section 6 (pp. 61–62), without choosing a source component. -/
theorem range_map_homotopyFiber_loop
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
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
    Set.range (ZerothHomotopy.map J) =
      (ZerothHomotopy.map
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))) ⁻¹'
          {ZerothHomotopy.mk e₀} := by
  intro J
  have J_refl : J (Path.refl b) =
      ContinuousMap.HomotopyFiber.const (f := f) (b := b) e₀ h := by
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
  let U := homotopyGroupEquivZerothHomotopyOfIsEmpty Empty (Path.refl b)
  let V := homotopyGroupEquivZerothHomotopyOfIsEmpty Empty
    (ContinuousMap.HomotopyFiber.const (f := f) (b := b) e₀ h)
  let W := homotopyGroupEquivZerothHomotopyOfIsEmpty Empty e₀
  -- Evaluation commutes with these very maps, including arbitrary representatives.
  have hJ (a : HomotopyGroup Empty (Path b b) (Path.refl b)) :
      V (HomotopyGroup.mapFun Empty J J_refl a) = ZerothHomotopy.map J (U a) := by
    obtain ⟨q, rfl⟩ := U.symm.surjective a
    rw [U.apply_symm_apply]
    obtain ⟨γ, rfl⟩ := ZerothHomotopy.mk_surjective q
    rw [← HomotopyGroup.equivZerothHomotopy_empty Empty
      (ContinuousMap.HomotopyFiber.const (f := f) (b := b) e₀ h),
      HomotopyGroup.equivZerothHomotopy_mapFun,
      HomotopyGroup.equivZerothHomotopy_empty_symm_mk]; rfl
  have hpoint (a : HomotopyGroup Empty (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h)) :
      W (HomotopyGroup.mapFun Empty
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) a) =
      ZerothHomotopy.map
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b)) (V a) := by
    obtain ⟨q, rfl⟩ := V.symm.surjective a
    rw [V.apply_symm_apply]
    obtain ⟨z, rfl⟩ := ZerothHomotopy.mk_surjective q
    rw [← HomotopyGroup.equivZerothHomotopy_empty Empty e₀,
      HomotopyGroup.equivZerothHomotopy_mapFun,
      HomotopyGroup.equivZerothHomotopy_empty_symm_mk]; rfl
  let c₀ : HomotopyGroup Empty E e₀ :=
    (⟦GenLoop.const⟧ : HomotopyGroup Empty E e₀)
  have hc₀ : W c₀ = ZerothHomotopy.mk e₀ := by
    refine Eq.trans (α := ZerothHomotopy E)
      (HomotopyGroup.equivZerothHomotopy_empty Empty e₀ c₀).symm ?_
    refine Eq.trans (α := ZerothHomotopy E)
      (congrArg (fun q : ZerothHomotopy (GenLoop Empty E e₀) =>
        ZerothHomotopy.map
          (⟨genLoopHomeoOfIsEmpty Empty e₀, (genLoopHomeoOfIsEmpty Empty e₀).continuous⟩ :
            C(GenLoop Empty E e₀, E)) q)
        (HomotopyGroup.equivZerothHomotopy_const Empty e₀)) ?_
    exact ZerothHomotopy.map_mk
      (⟨genLoopHomeoOfIsEmpty Empty e₀, (genLoopHomeoOfIsEmpty Empty e₀).continuous⟩ :
        C(GenLoop Empty E e₀, E)) (GenLoop.const : GenLoop Empty E e₀)
  have hRange : Set.range (HomotopyGroup.mapFun Empty J J_refl) =
      (HomotopyGroup.mapFun Empty
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h)) ⁻¹'
          {c₀} := by
    dsimp only [J, c₀]
    exact HomotopyGroup.range_mapFun_homotopyFiber_loop Empty f b e₀ h
  ext c
  obtain ⟨a, rfl⟩ := V.surjective c
  change (∃ q, ZerothHomotopy.map J q = V a) ↔
    ZerothHomotopy.map
      (ContinuousMap.HomotopyFiber.point (f := f) (b := b)) (V a) =
        ZerothHomotopy.mk e₀
  constructor
  · rintro ⟨q, hq⟩
    have ha : a ∈ Set.range (HomotopyGroup.mapFun Empty J J_refl) := by
      refine ⟨U.symm q, V.injective ?_⟩
      exact (hJ (U.symm q)).trans
        ((congrArg (ZerothHomotopy.map J) (U.apply_symm_apply q)).trans hq)
    have hproj : HomotopyGroup.mapFun Empty
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) a = c₀ :=
      (Set.ext_iff.mp hRange a).mp ha
    exact (hpoint a).symm.trans ((congrArg W hproj).trans hc₀)
  · intro ha
    have hproj : HomotopyGroup.mapFun Empty
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const (f := f) (b := b) e₀ h) a = c₀ := by
      apply W.injective
      exact (hpoint a).trans (ha.trans hc₀.symm)
    have haRange : a ∈ Set.range (HomotopyGroup.mapFun Empty J J_refl) :=
      (Set.ext_iff.mp hRange a).mpr hproj
    rcases haRange with ⟨q, hq⟩
    exact ⟨U q, (hJ q).symm.trans (congrArg V hq)⟩

end ZerothHomotopy
