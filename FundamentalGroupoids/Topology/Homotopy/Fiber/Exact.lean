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
