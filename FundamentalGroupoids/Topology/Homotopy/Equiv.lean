/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import FundamentalGroupoids.Topology.Path

/-!
# Adjointification of homotopy equivalences

An arbitrary pair of inverse homotopies can be adjusted on the left to satisfy
one triangle, through a homotopy relative to both ends of the path parameter.
The triangle is continuous jointly in the point, path time and deformation time.

The construction uses Mathlib's continuous-map and path homotopies and the
varying-endpoint family operations in `FundamentalGroupoids.Topology.Path`.
The proof compares the two boundary routes of a square, then uses genuine path
associators, cancellation homotopies and unit homotopies.
-/

@[expose] public section

universe uD uE uX uY uZ

open scoped unitInterval

namespace ContinuousMap.Homotopy

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A continuously parametrized family of endpoint-relative path homotopies.
There is no topology on the type of path homotopies in this definition. -/
private def Joint {a b : X → Y} (p q : ∀ x, Path (a x) (b x)) : Prop :=
  ∃ F : ∀ x, (p x).Homotopy (q x),
    Continuous (fun v : X × (I × I) => F v.1 v.2)

private theorem joint_refl {a b : X → Y} (p : ∀ x, Path (a x) (b x))
    (hp : Continuous (fun v : X × I => p v.1 v.2)) : Joint p p := by
  refine ⟨fun x => Path.Homotopy.refl (p x), ?_⟩
  change Continuous (fun v : X × (I × I) => p v.1 v.2.2)
  exact hp.comp (show Continuous (fun v : X × (I × I) => (v.1, v.2.2)) by fun_prop)

private theorem joint_symm {a b : X → Y} {p q : ∀ x, Path (a x) (b x)}
    (H : Joint p q) : Joint q p := by
  obtain ⟨F, hF⟩ := H
  refine ⟨fun x => (F x).symm, ?_⟩
  change Continuous (fun v : X × (I × I) =>
    F v.1 (unitInterval.symm v.2.1, v.2.2))
  exact hF.comp (show Continuous (fun v : X × (I × I) =>
    (v.1, (unitInterval.symm v.2.1, v.2.2))) by fun_prop)

private theorem joint_trans {a b : X → Y} {p q r : ∀ x, Path (a x) (b x)}
    (H : Joint p q) (K : Joint q r) : Joint p r := by
  obtain ⟨F, hF⟩ := H
  obtain ⟨G, hG⟩ := K
  refine ⟨fun x => (F x).trans (G x), ?_⟩
  exact ContinuousMap.Homotopy.trans_continuous_family
    (fun x => (F x).toHomotopy) (fun x => (G x).toHomotopy) hF hG

private theorem joint_hcomp {a b c : X → Y}
    {p p' : ∀ x, Path (a x) (b x)} {q q' : ∀ x, Path (b x) (c x)}
    (H : Joint p p') (K : Joint q q') :
    Joint (fun x => (p x).trans (q x)) (fun x => (p' x).trans (q' x)) := by
  obtain ⟨F, hF⟩ := H
  obtain ⟨G, hG⟩ := K
  exact ⟨fun x => (F x).hcomp (G x),
    Path.Homotopy.hcomp_continuous_family F G hF hG⟩

private theorem joint_map {a b : X → Y} {p q : ∀ x, Path (a x) (b x)}
    (H : Joint p q) (f : C(Y, Z)) :
    Joint (fun x => (p x).map f.continuous) (fun x => (q x).map f.continuous) := by
  obtain ⟨F, hF⟩ := H
  exact ⟨fun x => (F x).map f, f.continuous.comp hF⟩

private theorem joint_assoc {a b c d : X → Y}
    (p : ∀ x, Path (a x) (b x)) (q : ∀ x, Path (b x) (c x))
    (r : ∀ x, Path (c x) (d x))
    (hp : Continuous (fun v : X × I => p v.1 v.2))
    (hq : Continuous (fun v : X × I => q v.1 v.2))
    (hr : Continuous (fun v : X × I => r v.1 v.2)) :
    Joint (fun x => ((p x).trans (q x)).trans (r x))
      (fun x => (p x).trans ((q x).trans (r x))) :=
  ⟨fun x => Path.Homotopy.transAssoc (p x) (q x) (r x),
    Path.Homotopy.transAssoc_continuous_family p q r hp hq hr⟩

private theorem joint_right_unit {a b : X → Y} (p : ∀ x, Path (a x) (b x))
    (hp : Continuous (fun v : X × I => p v.1 v.2)) :
    Joint (fun x => (p x).trans (Path.refl (b x))) p :=
  ⟨fun x => Path.Homotopy.transRefl (p x),
    Path.Homotopy.transRefl_continuous_family p hp⟩

private theorem joint_left_unit {a b : X → Y} (p : ∀ x, Path (a x) (b x))
    (hp : Continuous (fun v : X × I => p v.1 v.2)) :
    Joint (fun x => (Path.refl (a x)).trans (p x)) p := by
  refine ⟨fun x => Path.Homotopy.reflTrans (p x), ?_⟩
  have hs := Path.symm_continuous_family p hp
  have h := Path.Homotopy.transRefl_continuous_family (fun x => (p x).symm) hs
  change Continuous (fun v : X × (I × I) =>
    Path.Homotopy.transRefl (p v.1).symm (v.2.1, unitInterval.symm v.2.2))
  exact h.comp (show Continuous (fun v : X × (I × I) =>
    (v.1, (v.2.1, unitInterval.symm v.2.2))) by fun_prop)

private theorem joint_loop {a b : X → Y} (p : ∀ x, Path (a x) (b x))
    (hp : Continuous (fun v : X × I => p v.1 v.2)) :
    Joint (fun x => Path.refl (a x)) (fun x => (p x).trans (p x).symm) :=
  ⟨fun x => Path.Homotopy.reflTransSymm (p x),
    Path.Homotopy.reflTransSymm_continuous_family p hp⟩

/-- Right cancellation is performed by appending the reverse path and then
removing the resulting loop; no strict cancellation law is used. -/
private theorem joint_cancel_right {a b c : X → Y}
    (p q : ∀ x, Path (a x) (b x)) (r : ∀ x, Path (b x) (c x))
    (hp : Continuous (fun v : X × I => p v.1 v.2))
    (hq : Continuous (fun v : X × I => q v.1 v.2))
    (hr : Continuous (fun v : X × I => r v.1 v.2))
    (H : Joint (fun x => (p x).trans (r x)) (fun x => (q x).trans (r x))) :
    Joint p q := by
  have hrs := Path.symm_continuous_family r hr
  have H₁ := joint_symm (joint_right_unit p hp)
  have H₂ := joint_hcomp (joint_refl p hp) (joint_loop r hr)
  have H₃ := joint_symm (joint_assoc p r (fun x => (r x).symm) hp hr hrs)
  have H₄ := joint_hcomp H (joint_refl (fun x => (r x).symm) hrs)
  have H₅ := joint_assoc q r (fun x => (r x).symm) hq hr hrs
  have H₆ := joint_hcomp (joint_refl q hq) (joint_symm (joint_loop r hr))
  exact joint_trans H₁ (joint_trans H₂ (joint_trans H₃
    (joint_trans H₄ (joint_trans H₅ (joint_trans H₆ (joint_right_unit q hq))))))

/-- Affine interpolation inside the ordinary unit interval. -/
private noncomputable def mix (r s t : I) : I :=
  ⟨(1 - (r : ℝ)) * s + r * t, by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr r.2.2) s.2.1)
        (mul_nonneg r.2.1 t.2.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr r.2.2) (sub_nonneg.mpr s.2.2),
        mul_nonneg r.2.1 (sub_nonneg.mpr t.2.2)]⟩

private theorem mix_continuous : Continuous (fun v : I × (I × I) =>
    mix v.1 v.2.1 v.2.2) := by
  unfold mix
  fun_prop

private theorem mix_zero (s t : I) : mix 0 s t = s := by
  apply Subtype.ext
  simp [mix]

private theorem mix_one (s t : I) : mix 1 s t = t := by
  apply Subtype.ext
  simp [mix]

private theorem mix_same (r s : I) : mix r s s = s := by
  apply Subtype.ext
  dsimp [mix]
  ring

private noncomputable def lowerRoute : Path ((0 : I), (0 : I)) (1, 1) :=
  ((Path.refl 0).prod Path.id).trans (Path.id.prod (Path.refl 1))

private noncomputable def upperRoute : Path ((0 : I), (0 : I)) (1, 1) :=
  (Path.id.prod (Path.refl 0)).trans ((Path.refl 1).prod Path.id)

/-- The two edge routes in a square are deformed into each other inside the square. -/
private noncomputable def squareRoutes : lowerRoute.Homotopy upperRoute where
  toFun v := (mix v.1 (lowerRoute v.2).1 (upperRoute v.2).1,
    mix v.1 (lowerRoute v.2).2 (upperRoute v.2).2)
  continuous_toFun := by
    exact (mix_continuous.comp
      (show Continuous (fun v : I × I =>
        (v.1, ((lowerRoute v.2).1, (upperRoute v.2).1))) by fun_prop)).prodMk
      (mix_continuous.comp
        (show Continuous (fun v : I × I =>
          (v.1, ((lowerRoute v.2).2, (upperRoute v.2).2))) by fun_prop))
  map_zero_left t := by
    change (mix 0 (lowerRoute t).1 (upperRoute t).1,
      mix 0 (lowerRoute t).2 (upperRoute t).2) = lowerRoute.toContinuousMap t
    rw [Path.coe_toContinuousMap]
    exact Prod.ext (mix_zero _ _) (mix_zero _ _)
  map_one_left t := by
    change (mix 1 (lowerRoute t).1 (upperRoute t).1,
      mix 1 (lowerRoute t).2 (upperRoute t).2) = upperRoute.toContinuousMap t
    rw [Path.coe_toContinuousMap]
    exact Prod.ext (mix_one _ _) (mix_one _ _)
  prop' r t ht := by
    rcases ht with ht | ht
    · subst t
      change (mix r (lowerRoute 0).1 (upperRoute 0).1,
        mix r (lowerRoute 0).2 (upperRoute 0).2) = lowerRoute.toContinuousMap 0
      simp only [Path.coe_toContinuousMap, Path.source]
      exact Prod.ext (mix_same r 0) (mix_same r 0)
    · rw [Set.mem_singleton_iff] at ht
      subst t
      change (mix r (lowerRoute 1).1 (upperRoute 1).1,
        mix r (lowerRoute 1).2 (upperRoute 1).2) = lowerRoute.toContinuousMap 1
      simp only [Path.coe_toContinuousMap, Path.target]
      exact Prod.ext (mix_same r 1) (mix_same r 1)

private theorem joint_square {a b c d : X → Y}
    (Φ : C((I × I) × X, Y))
    (p : ∀ x, Path (a x) (b x)) (q : ∀ x, Path (b x) (d x))
    (r : ∀ x, Path (a x) (c x)) (s : ∀ x, Path (c x) (d x))
    (hp : ∀ x t, Φ ((0, t), x) = p x t)
    (hq : ∀ x t, Φ ((t, 1), x) = q x t)
    (hr : ∀ x t, Φ ((t, 0), x) = r x t)
    (hs : ∀ x t, Φ ((1, t), x) = s x t) :
    Joint (fun x => (p x).trans (q x)) (fun x => (r x).trans (s x)) := by
  let F : ∀ x, ((p x).trans (q x)).Homotopy ((r x).trans (s x)) := fun x =>
    { toFun := fun v => Φ (squareRoutes v, x)
      continuous_toFun := Φ.continuous.comp (squareRoutes.continuous.prodMk continuous_const)
      map_zero_left := by
        intro t
        rw [squareRoutes.apply_zero]
        simp only [Path.coe_toContinuousMap, lowerRoute, Path.trans_apply,
          Path.prod_coe, Path.refl_apply, Path.id_apply]
        split_ifs with ht
        · exact hp x _
        · exact hq x _
      map_one_left := by
        intro t
        rw [squareRoutes.apply_one]
        simp only [Path.coe_toContinuousMap, upperRoute, Path.trans_apply,
          Path.prod_coe, Path.refl_apply, Path.id_apply]
        split_ifs with ht
        · exact hr x _
        · exact hs x _
      prop' := by
        intro v t ht
        rcases ht with ht | ht
        · subst t
          change Φ (squareRoutes (v, 0), x) = ((p x).trans (q x)) 0
          rw [squareRoutes.source, Path.source]
          exact (hp x 0).trans (p x).source
        · rw [Set.mem_singleton_iff] at ht
          subst t
          change Φ (squareRoutes (v, 1), x) = ((p x).trans (q x)) 1
          rw [squareRoutes.target, Path.target]
          exact (hq x 1).trans (q x).target }
  refine ⟨F, ?_⟩
  exact Φ.continuous.comp ((squareRoutes.continuous.comp continuous_snd).prodMk
    continuous_fst)

variable {D : Type uD} {E : Type uE} [TopologicalSpace D] [TopologicalSpace E]
variable {h : C(D, E)} {g : C(E, D)}

/-- Adjust the left inverse homotopy by a reverse left trace, the right trace
mapped through the inverse, and the original left trace, in that order. -/
noncomputable def adjointifyLeft
    (η : (g.comp h).Homotopy (ContinuousMap.id D))
    (ε : (h.comp g).Homotopy (ContinuousMap.id E)) :
    (g.comp h).Homotopy (ContinuousMap.id D) :=
  let α : ((g.comp h).comp (g.comp h)).Homotopy (g.comp h) :=
    (η.compContinuousMap (g.comp h)).cast rfl (ContinuousMap.id_comp _)
  let β : ((g.comp h).comp (g.comp h)).Homotopy (g.comp h) :=
    ((refl g).comp (ε.compContinuousMap h)).cast
      (by ext x; rfl) (by ext x; rfl)
  (α.symm.trans β).trans η

/-- The complete path of the adjusted left inverse, with its binary concatenation clocks. -/
theorem adjointifyLeft_evalAt
    (η : (g.comp h).Homotopy (ContinuousMap.id D))
    (ε : (h.comp g).Homotopy (ContinuousMap.id E)) (x : D) :
    (adjointifyLeft η ε).evalAt x =
      ((η.evalAt (g (h x))).symm.trans
        ((ε.evalAt (h x)).map g.continuous)).trans (η.evalAt x) := by
  apply Path.ext
  funext t
  rfl

/-- Evaluation of the adjusted left inverse on the entire concatenated path. -/
theorem adjointifyLeft_apply
    (η : (g.comp h).Homotopy (ContinuousMap.id D))
    (ε : (h.comp g).Homotopy (ContinuousMap.id E)) (x : D) (s : I) :
    adjointifyLeft η ε (s, x) =
      (((η.evalAt (g (h x))).symm.trans
        ((ε.evalAt (h x)).map g.continuous)).trans (η.evalAt x)) s := by
  exact congrArg (fun p : Path (g (h x)) x => p s)
    (adjointifyLeft_evalAt η ε x)

private theorem adjointifyLeftTriangle_nonempty
    (η : (g.comp h).Homotopy (ContinuousMap.id D))
    (ε : (h.comp g).Homotopy (ContinuousMap.id E)) :
    Nonempty ((h.comp (adjointifyLeft η ε).toContinuousMap).HomotopyRel
      (ε.compContinuousMap h).toContinuousMap
      {p : I × D | p.1 = 0 ∨ p.1 = 1}) := by
  let a := fun x : D => η.evalAt x
  let c := fun x : D => η.evalAt (g (h x))
  let b := fun x : D => ε.evalAt (h x)
  let A := fun x : D => (a x).map h.continuous
  let C := fun x : D => (c x).map h.continuous
  let B := fun x : D => (b x).map (h.comp g).continuous
  let U := fun x : D => ((a x).map (g.comp h).continuous).map h.continuous
  let d := fun x : D => ε.evalAt (h (g (h x)))
  have ha : Continuous (fun v : D × I => a v.1 v.2) :=
    η.continuous.comp (by fun_prop)
  have hc : Continuous (fun v : D × I => c v.1 v.2) :=
    η.continuous.comp (by fun_prop)
  have hb : Continuous (fun v : D × I => b v.1 v.2) :=
    ε.continuous.comp (by fun_prop)
  have hA : Continuous (fun v : D × I => A v.1 v.2) := h.continuous.comp ha
  have hC : Continuous (fun v : D × I => C v.1 v.2) := h.continuous.comp hc
  have hB : Continuous (fun v : D × I => B v.1 v.2) := (h.comp g).continuous.comp hb
  have hU : Continuous (fun v : D × I => U v.1 v.2) :=
    h.continuous.comp ((g.comp h).continuous.comp ha)
  have hd : Continuous (fun v : D × I => d v.1 v.2) :=
    ε.continuous.comp (by fun_prop)
  have hCs := Path.symm_continuous_family C hC
  -- The self-square of the left homotopy, followed by genuine right cancellation.
  have Hη : Joint (fun x => (a x).map (g.comp h).continuous) c := by
    apply joint_cancel_right _ _ a ((g.comp h).continuous.comp ha) hc ha
    exact joint_square
      ⟨fun v => η (v.1.1, η (v.1.2, v.2)), by fun_prop⟩
      (fun x => (a x).map (g.comp h).continuous) a c a
      (by intro x t; exact η.apply_zero _)
      (by
        intro x t
        change η (t, η (1, x)) = η (t, x)
        exact congrArg (fun y => η (t, y)) (η.apply_one x))
      (by
        intro x t
        change η (t, η (0, x)) = η (t, g (h x))
        exact congrArg (fun y => η (t, y)) (η.apply_zero x))
      (by intro x t; exact η.apply_one _)
  have Hηh : Joint C U := joint_map (joint_symm Hη) h
  -- The right self-square supplies the second naturality comparison independently.
  have Hε : Joint B d := by
    apply joint_cancel_right B d b hB hd hb
    exact joint_square
      ⟨fun v => ε (v.1.1, ε (v.1.2, h v.2)), by fun_prop⟩ B b d b
      (by intro x t; exact ε.apply_zero _)
      (by
        intro x t
        change ε (t, ε (1, h x)) = ε (t, h x)
        exact congrArg (fun y => ε (t, y)) (ε.apply_one (h x)))
      (by
        intro x t
        change ε (t, ε (0, h x)) = ε (t, h (g (h x)))
        exact congrArg (fun y => ε (t, y)) (ε.apply_zero (h x)))
      (by intro x t; exact ε.apply_one _)
  -- The mixed square has the two different boundary routes needed in the triangle.
  have Hmix : Joint (fun x => (U x).trans (b x))
      (fun x => (d x).trans (A x)) :=
    joint_square ⟨fun v => ε (v.1.1, h (η (v.1.2, v.2))), by fun_prop⟩ U b d A
      (by intro x t; exact ε.apply_zero _)
      (by
        intro x t
        change ε (t, h (η (1, x))) = ε (t, h x)
        exact congrArg (fun y => ε (t, h y)) (η.apply_one x))
      (by
        intro x t
        change ε (t, h (η (0, x))) = ε (t, h (g (h x)))
        exact congrArg (fun y => ε (t, h y)) (η.apply_zero x))
      (by intro x t; exact ε.apply_one _)
  have H₁ := joint_hcomp
    (joint_hcomp (joint_refl (fun x => (C x).symm) hCs) Hε) (joint_refl A hA)
  have H₂ := joint_assoc (fun x => (C x).symm) d A hCs hd hA
  have H₃ := joint_hcomp (joint_refl (fun x => (C x).symm) hCs) (joint_symm Hmix)
  have H₄ := joint_hcomp (joint_refl (fun x => (C x).symm) hCs)
    (joint_hcomp (joint_symm Hηh) (joint_refl b hb))
  have H₅ := joint_symm (joint_assoc (fun x => (C x).symm) C b hCs hC hb)
  have Hcancel : Joint (fun x => (C x).symm.trans (C x))
      (fun x => Path.refl (h (g (h x)))) := by
    have Hloop := joint_symm (joint_loop (fun x => (C x).symm) hCs)
    have hpaths : (fun x : D => (C x).symm.trans (C x).symm.symm) =
        (fun x : D => (C x).symm.trans (C x)) := by
      funext x
      exact congrArg (fun p => (C x).symm.trans p) (Path.symm_symm (C x))
    rw [hpaths] at Hloop
    exact Hloop
  have H₆ := joint_hcomp Hcancel (joint_refl b hb)
  have H := joint_trans H₁ (joint_trans H₂ (joint_trans H₃
    (joint_trans H₄ (joint_trans H₅ (joint_trans H₆ (joint_left_unit b hb))))))
  have hBpath (x : D) : ((b x).map g.continuous).map h.continuous = B x :=
    Path.map_map (b x) g.continuous h.continuous
  have hpath (x : D) : ((adjointifyLeft η ε).evalAt x).map h.continuous =
      ((C x).symm.trans (B x)).trans (A x) := by
    -- Normalize endpoints before applying the whole-path map laws as terms.
    let cN : Path (g (h (g (h x)))) (g (h x)) := η.evalAt (g (h x))
    let qN : Path (g (h (g (h x)))) (g (h x)) := (ε.evalAt (h x)).map g.continuous
    let aN : Path (g (h x)) x := η.evalAt x
    have hinner : (cN.symm.trans qN).map h.continuous =
        (C x).symm.trans (B x) := by
      exact Eq.trans (Path.map_trans cN.symm qN h.continuous)
        (congrArg₂
          (fun (p : Path (h (g (h x))) (h (g (h (g (h x))))))
            (q : Path (h (g (h (g (h x))))) (h (g (h x)))) => p.trans q)
          (Path.map_symm cN h.continuous).symm (hBpath x))
    exact Eq.trans
      (congrArg (fun p : Path (g (h x)) x => p.map h.continuous)
        (adjointifyLeft_evalAt η ε x))
      (Eq.trans (Path.map_trans (cN.symm.trans qN) aN h.continuous)
        (congrArg (fun p : Path (h (g (h x))) (h (g (h x))) => p.trans (A x)) hinner))
  have Htrace : Joint (fun x => ((adjointifyLeft η ε).evalAt x).map h.continuous) b := by
    rw [show (fun x => ((adjointifyLeft η ε).evalAt x).map h.continuous) =
      (fun x => ((C x).symm.trans (B x)).trans (A x)) from funext hpath]
    exact H
  obtain ⟨F, hF⟩ := Htrace
  exact ⟨{
    toFun := fun v => F v.2.2 (v.1, v.2.1)
    continuous_toFun := hF.comp (show Continuous (fun v : I × (I × D) =>
      (v.2.2, (v.1, v.2.1))) by fun_prop)
    map_zero_left := fun p => (F p.2).apply_zero p.1
    map_one_left := fun p => (F p.2).apply_one p.1
    prop' := by
      intro r p hp
      rcases hp with hp | hp
      · rcases p with ⟨s, x⟩
        dsimp at hp
        subst s
        change F x (r, 0) = h (adjointifyLeft η ε (0, x))
        rw [(adjointifyLeft η ε).apply_zero]
        exact (F x).source r
      · rcases p with ⟨s, x⟩
        dsimp at hp
        subst s
        change F x (r, 1) = h (adjointifyLeft η ε (1, x))
        rw [(adjointifyLeft η ε).apply_one]
        exact (F x).target r }⟩

/-- A joint triangle deformation from the image of the adjusted left homotopy
to the supplied right homotopy, relative to both path endpoints. -/
noncomputable def adjointifyLeftTriangle
    (η : (g.comp h).Homotopy (ContinuousMap.id D))
    (ε : (h.comp g).Homotopy (ContinuousMap.id E)) :
    (h.comp (adjointifyLeft η ε).toContinuousMap).HomotopyRel
      (ε.compContinuousMap h).toContinuousMap
      {p : I × D | p.1 = 0 ∨ p.1 = 1} :=
  Classical.choice (by exact adjointifyLeftTriangle_nonempty η ε)

/-- At deformation time zero the triangle is the image of the adjusted left trace. -/
theorem adjointifyLeftTriangle_zero
    (η : (g.comp h).Homotopy (ContinuousMap.id D))
    (ε : (h.comp g).Homotopy (ContinuousMap.id E)) (s : I) (x : D) :
    adjointifyLeftTriangle η ε (0, (s, x)) = h (adjointifyLeft η ε (s, x)) :=
  (adjointifyLeftTriangle η ε).apply_zero (s, x)

/-- At deformation time one the triangle is the supplied right trace. -/
theorem adjointifyLeftTriangle_one
    (η : (g.comp h).Homotopy (ContinuousMap.id D))
    (ε : (h.comp g).Homotopy (ContinuousMap.id E)) (s : I) (x : D) :
    adjointifyLeftTriangle η ε (1, (s, x)) = ε (s, h x) :=
  (adjointifyLeftTriangle η ε).apply_one (s, x)

/-- The source endpoint is fixed throughout the triangle deformation. -/
theorem adjointifyLeftTriangle_source
    (η : (g.comp h).Homotopy (ContinuousMap.id D))
    (ε : (h.comp g).Homotopy (ContinuousMap.id E)) (r : I) (x : D) :
    adjointifyLeftTriangle η ε (r, (0, x)) = h (g (h x)) := by
  calc
    _ = h (adjointifyLeft η ε (0, x)) :=
      (adjointifyLeftTriangle η ε).eq_fst r (Or.inl rfl)
    _ = h (g (h x)) := by rw [(adjointifyLeft η ε).apply_zero]; rfl

/-- The target endpoint is fixed throughout the triangle deformation. -/
theorem adjointifyLeftTriangle_target
    (η : (g.comp h).Homotopy (ContinuousMap.id D))
    (ε : (h.comp g).Homotopy (ContinuousMap.id E)) (r : I) (x : D) :
    adjointifyLeftTriangle η ε (r, (1, x)) = h x := by
  calc
    _ = h (adjointifyLeft η ε (1, x)) :=
      (adjointifyLeftTriangle η ε).eq_fst r (Or.inr rfl)
    _ = h x := by rw [(adjointifyLeft η ε).apply_one]; rfl

end ContinuousMap.Homotopy

namespace ContinuousMap.HomotopyEquiv

variable {D : Type uD} {E : Type uE} [TopologicalSpace D] [TopologicalSpace E]

/-- Forgetting the adjusted witness leaves the supplied stock homotopy equivalence
unchanged: only a proof-valued inverse field has changed. -/
theorem adjointifyLeft_bridge (e : ContinuousMap.HomotopyEquiv D E) :
    ({ toFun := e.toFun
       invFun := e.invFun
       left_inv := ⟨ContinuousMap.Homotopy.adjointifyLeft
         (Classical.choice e.left_inv) (Classical.choice e.right_inv)⟩
       right_inv := e.right_inv } : ContinuousMap.HomotopyEquiv D E) = e := by
  cases e
  rfl

end ContinuousMap.HomotopyEquiv
