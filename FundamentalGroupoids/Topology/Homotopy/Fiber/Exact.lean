/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber.Const
public import FundamentalGroupoids.Topology.Homotopy.Fiber.PathComponent
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace

/-!
# Images on components of maps of homotopy fibers

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

The loop-image statement is the ordinary-topology version of the fiber-sequence
exactness theorem in May, Chapter 8, Section 6 (pp. 61–62). The fixed-base
component-image statements are a structural extension of this loop-source case,
not statements quoted from that section. Here products, subspaces and compact-open
mapping spaces carry their ordinary topologies; no comparison with May's
weak-Hausdorff, compactly generated category is asserted.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, Section 6,
  "Fiber sequences", pp. 61–62: the homotopy fiber, loop inclusion and exactness
  of the associated sequence of pointed homotopy sets.
* Mathlib's paths and path components, due to Patrick Massot and contributors,
  and generalized loops and homotopy groups, due to Roberto Alvarez.
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
