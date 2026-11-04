/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Homotopy.Path
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Maps on path spaces, paths in subspaces and continuous families of homotopies

A continuous map of spaces induces a continuous map on each fixed-endpoint path
space. Endpoint transport specializes this to based loops for a map with a specified
basepoint equation. A homotopy relative to that point induces a jointly continuous
homotopy of loop maps, fixing the constant loop throughout. A path whose range is
contained in a set can be regarded as a path in that subspace.
The inclusion recovers the original path. A homotopy between paths in a subspace
can likewise be recovered from an ambient based homotopy whose range stays in the
subspace.

Reparametrization, right-unit, associativity and path-followed-by-reverse homotopies
vary jointly continuously in continuous families of paths, even when the endpoints
vary. Vertical composition of homotopies and horizontal composition of path
homotopies also preserve joint continuity. The parameter, homotopy domain and target
may have independent universes. These statements use joint evaluation rather than
a topology on a homotopy space and require no local compactness or separation
assumptions.

## References

* Mathlib's paths and path homotopies supply the underlying constructions.
* The path corestriction factors the construction used in the open-cover descent
  and fundamental-group subspace arguments in this library.
* Mathlib's `Path.Homotopy.reparam`, `reflTransSymm`, `transRefl`, `transAssoc` and
  `hcomp` give the path homotopies.
* Mathlib's `ContinuousMap.Homotopy.trans` and `Path.trans_continuous_family`
  supply composition and continuity of concatenation.
* Mathlib's `Path.map_trans` and `Path.cast_trans` supply compatibility of loop
  maps with ordinary path concatenation.
-/

@[expose] public section

namespace Path

variable {X : Type*} [TopologicalSpace X] {a b : X} {s : Set X}

/-- The continuous map on path spaces induced by a continuous map of spaces. -/
def mapContinuousMap {Y : Type*} [TopologicalSpace Y] (g : C(X, Y)) (a a' : X) :
    C(Path a a', Path (g a) (g a')) where
  toFun γ := γ.map g.continuous
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact g.continuous.comp (Path.continuous_uncurry_iff.mpr
      (continuous_id : Continuous (id : Path a a' → Path a a')))

/-- The induced map on paths is `Path.map`. -/
theorem mapContinuousMap_apply {Y : Type*} [TopologicalSpace Y]
    (g : C(X, Y)) (a a' : X) (γ : Path a a') :
    mapContinuousMap g a a' γ = γ.map g.continuous := rfl

/-- Evaluation of an induced path is pointwise evaluation of the original map. -/
@[simp]
theorem mapContinuousMap_apply_apply {Y : Type*} [TopologicalSpace Y]
    (g : C(X, Y)) (a a' : X) (γ : Path a a') (t : unitInterval) :
    mapContinuousMap g a a' γ t = g (γ t) := rfl

/-- A constant path is mapped to a constant path. -/
@[simp]
theorem mapContinuousMap_refl {Y : Type*} [TopologicalSpace Y] (g : C(X, Y)) (a : X) :
    mapContinuousMap g a a (Path.refl a) = Path.refl (g a) := by
  ext t
  rfl

/-- The identity map induces the identity on path spaces. -/
@[simp]
theorem mapContinuousMap_id (a a' : X) :
    mapContinuousMap (ContinuousMap.id X) a a' = ContinuousMap.id (Path a a') := by
  ext γ t
  rfl

/-- Mapping paths preserves composition of continuous maps. -/
theorem mapContinuousMap_comp {Y T : Type*} [TopologicalSpace Y] [TopologicalSpace T]
    (f : C(X, Y)) (g : C(Y, T)) (a a' : X) :
    mapContinuousMap (g.comp f) a a' =
      (mapContinuousMap g (f a) (f a')).comp (mapContinuousMap f a a') := by
  ext γ t
  rfl

/-- Concatenation of fixed-endpoint paths as a continuous map on their ordinary product. -/
noncomputable def transContinuousMap.{u} {X : Type u} [TopologicalSpace X]
    (x y z : X) : C(Path x y × Path y z, Path x z) :=
  ⟨fun ρ : Path x y × Path y z => ρ.1.trans ρ.2,
    Path.continuous_trans (x := x) (y := y) (z := z)⟩

/-- The binary continuous map sends a pair to its path concatenation. -/
@[simp]
theorem transContinuousMap_apply.{u} {X : Type u} [TopologicalSpace X]
    (x y z : X) (γ : Path x y) (δ : Path y z) :
    Path.transContinuousMap x y z (γ, δ) = γ.trans δ := rfl

/-- Inner-time evaluation follows the first path on the closed first half
and the second path on the open second half. -/
theorem transContinuousMap_apply_apply.{u}
    {X : Type u} [TopologicalSpace X] (x y z : X)
    (γ : Path x y) (δ : Path y z) (t : unitInterval) :
    Path.transContinuousMap x y z (γ, δ) t =
      if h : (t : ℝ) ≤ 1 / 2 then
        γ ⟨2 * t, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
      else δ ⟨2 * t - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ := by
  rw [transContinuousMap_apply]
  exact Path.trans_apply γ δ t

/-- Concatenating the pair of constant loops gives the same constant loop. -/
theorem transContinuousMap_refl_refl.{u}
    {X : Type u} [TopologicalSpace X] (x : X) :
    Path.transContinuousMap x x x (Path.refl x, Path.refl x) = Path.refl x := by
  rw [transContinuousMap_apply, Path.refl_trans_refl]

/-- Postcomposition commutes with binary path concatenation as an equality
of whole continuous maps. -/
theorem mapContinuousMap_comp_transContinuousMap.{u, v}
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x y z : X) :
    (Path.mapContinuousMap f x z).comp (Path.transContinuousMap x y z) =
      (Path.transContinuousMap (f x) (f y) (f z)).comp
        ((Path.mapContinuousMap f x y).prodMap (Path.mapContinuousMap f y z)) := by
  apply ContinuousMap.ext
  rintro ⟨γ, δ⟩
  calc
    Path.mapContinuousMap f x z (Path.transContinuousMap x y z (γ, δ)) =
        (γ.trans δ).map f.continuous := by
      rw [transContinuousMap_apply, mapContinuousMap_apply]
    _ = (γ.map f.continuous).trans (δ.map f.continuous) := Path.map_trans γ δ f.continuous
    _ = Path.transContinuousMap (f x) (f y) (f z)
        (Path.mapContinuousMap f x y γ, Path.mapContinuousMap f y z δ) := by
      rw [transContinuousMap_apply, mapContinuousMap_apply, mapContinuousMap_apply]

/-- Regard a path whose range lies in a set as a path in the corresponding subspace. -/
def codRestrict (γ : Path a b) (hγ : Set.range γ ⊆ s) :
    Path (⟨a, hγ γ.source_mem_range⟩ : s) ⟨b, hγ γ.target_mem_range⟩ where
  toFun t := ⟨γ t, hγ ⟨t, rfl⟩⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

@[simp]
theorem codRestrict_apply (γ : Path a b) (hγ : Set.range γ ⊆ s) (t : unitInterval) :
    γ.codRestrict hγ t = ⟨γ t, hγ ⟨t, rfl⟩⟩ := rfl

/-- Inclusion of a corestricted path recovers the original path. -/
@[simp]
theorem codRestrict_map_subtypeVal (γ : Path a b) (hγ : Set.range γ ⊆ s) :
    (γ.codRestrict hγ).map continuous_subtype_val = γ := by
  ext t
  rfl

/-- Corestriction of a constant path is constant. -/
@[simp]
theorem codRestrict_refl (a : X) (h : Set.range (Path.refl a) ⊆ s) :
    (Path.refl a).codRestrict h = Path.refl (⟨a, h (Path.refl a).source_mem_range⟩ : s) := by
  ext t
  rfl

/-- Corestriction respects concatenation. -/
theorem codRestrict_trans {c : X} (γ : Path a b) (δ : Path b c)
    (hγ : Set.range γ ⊆ s) (hδ : Set.range δ ⊆ s)
    (hγδ : Set.range (γ.trans δ) ⊆ s) :
    (γ.trans δ).codRestrict hγδ = (γ.codRestrict hγ).trans (δ.codRestrict hδ) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  change (((γ.trans δ).codRestrict hγδ).map continuous_subtype_val) t =
    (((γ.codRestrict hγ).trans (δ.codRestrict hδ)).map continuous_subtype_val) t
  rw [codRestrict_map_subtypeVal, Path.map_trans,
    codRestrict_map_subtypeVal, codRestrict_map_subtypeVal]

/-- Corestricting the inclusion of a subspace path recovers that path. -/
@[simp]
theorem map_subtypeVal_codRestrict {a b : s} (γ : Path a b)
    (h : Set.range (γ.map continuous_subtype_val) ⊆ s) :
    (γ.map continuous_subtype_val).codRestrict h = γ := by
  ext t
  rfl

/-- A based ambient homotopy between paths in a subspace gives a homotopy in that
subspace if its whole range is contained there. -/
theorem Homotopic.of_subtypeVal {a b : s} {γ δ : Path a b}
    (H : (γ.map continuous_subtype_val).Homotopy (δ.map continuous_subtype_val))
    (hH : Set.range H ⊆ s) : γ.Homotopic δ := by
  refine ⟨{
    toFun := fun z => ⟨H z, hH ⟨z, rfl⟩⟩
    continuous_toFun := H.continuous.subtype_mk _
    map_zero_left := fun t => Subtype.ext (H.map_zero_left t)
    map_one_left := fun t => Subtype.ext (H.map_one_left t)
    prop' := fun t x hx => Subtype.ext (ContinuousMap.HomotopyRel.eq_fst H t hx) }⟩

end Path


namespace ContinuousMap

/-- Pointwise application of a based map to based loops, with transported endpoints. -/
def loopMap.{u, v} {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b) : C(Path e₀ e₀, Path b b) where
  toFun γ := (Path.mapContinuousMap f e₀ e₀ γ).cast h.symm h.symm
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact f.continuous.comp (Path.continuous_uncurry_iff.mpr
      (continuous_id : Continuous (id : Path e₀ e₀ → Path e₀ e₀)))

/-- The loop map is the mapped path with its endpoints cast along the basepoint equation. -/
theorem loopMap_apply.{u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b) (γ : Path e₀ e₀) :
    f.loopMap e₀ b h γ = (γ.map f.continuous).cast h.symm h.symm := rfl

/-- The whole forward loop is mapped pointwise, without reversal or reparametrization. -/
@[simp]
theorem loopMap_apply_apply.{u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b) (γ : Path e₀ e₀) (t : unitInterval) :
    f.loopMap e₀ b h γ t = f (γ t) := rfl

/-- Loop maps commute with reversal of the whole path. -/
@[simp]
theorem loopMap_symm.{u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b)
    (γ : Path e₀ e₀) :
    f.loopMap e₀ b h γ.symm = (f.loopMap e₀ b h γ).symm := by
  simp only [loopMap_apply, ← Path.map_symm, Path.cast_symm]

/-- Loop maps preserve ordinary path concatenation, by Mathlib's mapping and
endpoint-cast compatibility. -/
theorem loopMap_trans.{u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b)
    (γ δ : Path e₀ e₀) :
    f.loopMap e₀ b h (γ.trans δ) =
      (f.loopMap e₀ b h γ).trans (f.loopMap e₀ b h δ) := by
  simpa only [loopMap_apply, Path.map_trans] using
    Path.cast_trans (γ.map f.continuous) (δ.map f.continuous) h.symm h.symm h.symm

/-- A loop map with its specified endpoint transports commutes with the
whole binary concatenation map, also for independent source and target universes. -/
theorem loopMap_comp_transContinuousMap.{u, v}
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e : E) (b : B) (h : f e = b) :
    (f.loopMap e b h).comp (Path.transContinuousMap e e e) =
      (Path.transContinuousMap b b b).comp
        ((f.loopMap e b h).prodMap (f.loopMap e b h)) := by
  apply ContinuousMap.ext
  rintro ⟨γ, δ⟩
  calc
    f.loopMap e b h (Path.transContinuousMap e e e (γ, δ)) =
        f.loopMap e b h (γ.trans δ) := by rw [Path.transContinuousMap_apply]
    _ = (f.loopMap e b h γ).trans (f.loopMap e b h δ) := loopMap_trans f e b h γ δ
    _ = Path.transContinuousMap b b b (f.loopMap e b h γ, f.loopMap e b h δ) :=
      (Path.transContinuousMap_apply b b b (f.loopMap e b h γ) (f.loopMap e b h δ)).symm

/-- The loop map preserves the constant loop. -/
@[simp]
theorem loopMap_refl.{u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b) :
    f.loopMap e₀ b h (Path.refl e₀) = Path.refl b := by
  ext t
  exact h

/-- The identity based map induces the identity on based loops. -/
@[simp]
theorem loopMap_id.{u} {E : Type u} [TopologicalSpace E] (e₀ : E) :
    (ContinuousMap.id E).loopMap e₀ e₀ rfl = ContinuousMap.id (Path e₀ e₀) := by
  ext γ t
  rfl

/-- Pointwise maps on based loops preserve composition of based maps. -/
theorem loopMap_comp.{u, v, t} {E : Type u} {B : Type v} {T : Type t}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace T]
    (f : C(E, B)) (g : C(B, T)) (e₀ : E) (b : B) (c : T)
    (hf : f e₀ = b) (hg : g b = c) :
    (g.comp f).loopMap e₀ c ((congrArg g hf).trans hg) =
      (g.loopMap b c hg).comp (f.loopMap e₀ b hf) := by
  ext γ s
  rfl

namespace HomotopyRel

/-- A homotopy relative to a point induces a homotopy of loop maps, relative to the
constant loop. The homotopy varies jointly continuously with time and the input loop. -/
def loopMap.{u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {e : E} {f g : C(E, B)}
    (H : HomotopyRel f g {e}) (b : B) (hf : f e = b) (hg : g e = b) :
    HomotopyRel (f.loopMap e b hf) (g.loopMap e b hg) {Path.refl e} where
  toFun p :=
    { toFun t := H (p.1, p.2 t)
      continuous_toFun := H.continuous.comp (continuous_const.prodMk p.2.continuous)
      source' := by
        rw [p.2.source]
        exact (H.eq_fst p.1 (Set.mem_singleton e)).trans hf
      target' := by
        rw [p.2.target]
        exact (H.eq_fst p.1 (Set.mem_singleton e)).trans hf }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    have hev : Continuous (fun p : (unitInterval × Path e e) × unitInterval =>
        p.1.2 p.2) :=
      (Path.continuous_uncurry_iff.mpr
        (continuous_id : Continuous (id : Path e e → Path e e))).comp
          (continuous_fst.snd.prodMk continuous_snd)
    exact H.continuous.comp (continuous_fst.fst.prodMk hev)
  map_zero_left γ := by
    ext t
    exact H.apply_zero (γ t)
  map_one_left γ := by
    ext t
    exact H.apply_one (γ t)
  prop' s γ hγ := by
    obtain rfl : γ = Path.refl e := Set.mem_singleton_iff.mp hγ
    ext t
    exact H.eq_fst s (Set.mem_singleton e)

/-- Evaluation of the induced homotopy is pointwise evaluation of the original homotopy. -/
@[simp]
theorem loopMap_apply_apply.{u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {e : E} {f g : C(E, B)}
    (H : HomotopyRel f g {e}) (b : B) (hf : f e = b) (hg : g e = b)
    (s : unitInterval) (γ : Path e e) (t : unitInterval) :
    H.loopMap b hf hg (s, γ) t = H (s, γ t) := rfl

/-- Every time slice of the induced homotopy fixes the whole constant loop. -/
@[simp]
theorem loopMap_refl.{u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {e : E} {f g : C(E, B)}
    (H : HomotopyRel f g {e}) (b : B) (hf : f e = b) (hg : g e = b)
    (s : unitInterval) :
    H.loopMap b hf hg (s, Path.refl e) = Path.refl b := by
  ext t
  exact (H.eq_fst s (Set.mem_singleton e)).trans hf

end HomotopyRel

/-- Homotopy relative to a point is preserved by passage to the induced loop maps. -/
theorem HomotopicRel.loopMap.{u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {e : E} {f g : C(E, B)}
    (H : HomotopicRel f g {e}) (b : B) (hf : f e = b) (hg : g e = b) :
    HomotopicRel (f.loopMap e b hf) (g.loopMap e b hg) {Path.refl e} :=
  H.map (fun F ↦ F.loopMap b hf hg)

end ContinuousMap

open unitInterval

section PathHomotopyReparametrization

universe uZ uB

namespace Path.Homotopy

variable {Z : Type uZ} {B : Type uB}
variable [TopologicalSpace Z] [TopologicalSpace B]
variable {a b c d : Z → B}

/-- The standard reparametrization homotopy varies jointly continuously with a
continuous path family, allowing both endpoints to vary. -/
theorem reparam_continuous_family
    (p : ∀ z : Z, Path (a z) (b z))
    (hp : Continuous (fun v : Z × I => p v.1 v.2))
    (ρ : I → I) (hρ : Continuous ρ) (hρ₀ : ρ 0 = 0) (hρ₁ : ρ 1 = 1) :
    Continuous (fun v : Z × I × I =>
      Path.Homotopy.reparam (p v.1) ρ hρ hρ₀ hρ₁ (v.2.1, v.2.2)) := by
  let R : I × I → I := Path.Homotopy.reparam Path.id ρ hρ hρ₀ hρ₁
  have hR : Continuous R :=
    (Path.Homotopy.reparam Path.id ρ hρ hρ₀ hρ₁).toHomotopy.continuous
  change Continuous (fun v : Z × I × I => p v.1 (R v.2))
  exact hp.comp (continuous_fst.prodMk (hR.comp continuous_snd))

/-- The standard homotopy from a constant path to a path followed by its reverse
varies jointly continuously with a continuous path family. -/
theorem reflTransSymm_continuous_family
    (p : ∀ z : Z, Path (a z) (b z))
    (hp : Continuous (fun v : Z × I => p v.1 v.2)) :
    Continuous (fun v : Z × I × I =>
      Path.Homotopy.reflTransSymm (p v.1) (v.2.1, v.2.2)) := by
  let R : I × I → I := fun v =>
    ⟨reflTransSymmAux v, reflTransSymmAux_mem_I v⟩
  have hR : Continuous R := continuous_reflTransSymmAux.subtype_mk _
  change Continuous (fun v : Z × I × I => p v.1 (R v.2))
  exact hp.comp (continuous_fst.prodMk (hR.comp continuous_snd))

/-- The standard right-unit homotopy varies jointly continuously with a continuous
path family, allowing both endpoints to vary. -/
theorem transRefl_continuous_family
    (p : ∀ z : Z, Path (a z) (b z))
    (hp : Continuous (fun v : Z × I => p v.1 v.2)) :
    Continuous (fun v : Z × I × I =>
      Path.Homotopy.transRefl (p v.1) (v.2.1, v.2.2)) := by
  let ρ : I → I := fun t =>
    ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩
  have hρ : Continuous ρ := continuous_transReflReparamAux.subtype_mk _
  have hρ₀ : ρ 0 = 0 := Subtype.ext transReflReparamAux_zero
  have hρ₁ : ρ 1 = 1 := Subtype.ext transReflReparamAux_one
  have h := reparam_continuous_family p hp ρ hρ hρ₀ hρ₁
  change Continuous (fun v : Z × I × I =>
    Path.Homotopy.reparam (p v.1) ρ hρ hρ₀ hρ₁ (σ v.2.1, v.2.2))
  exact h.comp (continuous_fst.prodMk
    ((unitInterval.continuous_symm.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)))

/-- The standard associativity homotopy varies jointly continuously with three
continuous path families whose matching endpoints may vary. -/
theorem transAssoc_continuous_family
    (p : ∀ z : Z, Path (a z) (b z))
    (q : ∀ z : Z, Path (b z) (c z))
    (r : ∀ z : Z, Path (c z) (d z))
    (hp : Continuous (fun v : Z × I => p v.1 v.2))
    (hq : Continuous (fun v : Z × I => q v.1 v.2))
    (hr : Continuous (fun v : Z × I => r v.1 v.2)) :
    Continuous (fun v : Z × I × I =>
      Path.Homotopy.transAssoc (p v.1) (q v.1) (r v.1) (v.2.1, v.2.2)) := by
  let ρ : I → I := fun t =>
    ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩
  have hρ : Continuous ρ := continuous_transAssocReparamAux.subtype_mk _
  have hρ₀ : ρ 0 = 0 := Subtype.ext transAssocReparamAux_zero
  have hρ₁ : ρ 1 = 1 := Subtype.ext transAssocReparamAux_one
  have hqr : Continuous (fun v : Z × I => ((q v.1).trans (r v.1)) v.2) :=
    Path.trans_continuous_family q hq r hr
  have hpqr : Continuous (fun v : Z × I =>
      ((p v.1).trans ((q v.1).trans (r v.1))) v.2) :=
    Path.trans_continuous_family p hp (fun z => (q z).trans (r z)) hqr
  have h := reparam_continuous_family
    (fun z => (p z).trans ((q z).trans (r z))) hpqr ρ hρ hρ₀ hρ₁
  change Continuous (fun v : Z × I × I =>
    Path.Homotopy.reparam ((p v.1).trans ((q v.1).trans (r v.1)))
      ρ hρ hρ₀ hρ₁ (σ v.2.1, v.2.2))
  exact h.comp (continuous_fst.prodMk
    ((unitInterval.continuous_symm.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)))

end Path.Homotopy

end PathHomotopyReparametrization

section HomotopyComposition

universe uT uD uX

variable {T : Type uT} {D : Type uD} {X : Type uX}
variable [TopologicalSpace T] [TopologicalSpace D] [TopologicalSpace X]

open unitInterval

namespace ContinuousMap.Homotopy

/-- Vertical composition preserves joint continuity of homotopy families, with no local
compactness assumptions on the parameter, domain, or target. -/
theorem trans_continuous_family {f₀ f₁ f₂ : T → C(D, X)}
    (F : ∀ z : T, ContinuousMap.Homotopy (f₀ z) (f₁ z))
    (G : ∀ z : T, ContinuousMap.Homotopy (f₁ z) (f₂ z))
    (hF : Continuous (fun u : T × (I × D) => F u.1 u.2))
    (hG : Continuous (fun u : T × (I × D) => G u.1 u.2)) :
    Continuous (fun u : T × (I × D) => (F u.1).trans (G u.1) u.2) := by
  -- Endpoint maps on the total domain are continuous by restricting the joint families.
  let f₀Total : C(T × D, X) :=
    ⟨fun u => f₀ u.1 u.2, by
      simpa only [Function.comp_def, ContinuousMap.Homotopy.apply_zero] using
        hF.comp (show Continuous (fun u : T × D => (u.1, ((0 : I), u.2))) from
          continuous_fst.prodMk (continuous_const.prodMk continuous_snd))⟩
  let f₁Total : C(T × D, X) :=
    ⟨fun u => f₁ u.1 u.2, by
      simpa only [Function.comp_def, ContinuousMap.Homotopy.apply_one] using
        hF.comp (show Continuous (fun u : T × D => (u.1, ((1 : I), u.2))) from
          continuous_fst.prodMk (continuous_const.prodMk continuous_snd))⟩
  let f₂Total : C(T × D, X) :=
    ⟨fun u => f₂ u.1 u.2, by
      simpa only [Function.comp_def, ContinuousMap.Homotopy.apply_one] using
        hG.comp (show Continuous (fun u : T × D => (u.1, ((1 : I), u.2))) from
          continuous_fst.prodMk (continuous_const.prodMk continuous_snd))⟩
  let Ftotal : ContinuousMap.Homotopy f₀Total f₁Total :=
    { toFun := fun u => F u.2.1 (u.1, u.2.2)
      continuous_toFun := hF.comp
        (show Continuous (fun u : I × (T × D) => (u.2.1, (u.1, u.2.2))) from
          continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))
      map_zero_left := fun u => (F u.1).apply_zero u.2
      map_one_left := fun u => (F u.1).apply_one u.2 }
  let Gtotal : ContinuousMap.Homotopy f₁Total f₂Total :=
    { toFun := fun u => G u.2.1 (u.1, u.2.2)
      continuous_toFun := hG.comp
        (show Continuous (fun u : I × (T × D) => (u.2.1, (u.1, u.2.2))) from
          continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))
      map_zero_left := fun u => (G u.1).apply_zero u.2
      map_one_left := fun u => (G u.1).apply_one u.2 }
  -- The concatenation on the total domain evaluates to the pointwise concatenations.
  have hEq :
      (fun u : T × (I × D) =>
        (Ftotal.trans Gtotal) (u.2.1, (u.1, u.2.2))) =
      (fun u : T × (I × D) => (F u.1).trans (G u.1) u.2) := by
    funext u
    exact (trans_apply Ftotal Gtotal (u.2.1, (u.1, u.2.2))).trans
      (trans_apply (F u.1) (G u.1) u.2).symm
  rw [← hEq]
  exact (map_continuous (Ftotal.trans Gtotal)).comp
    (show Continuous (fun u : T × (I × D) => (u.2.1, (u.1, u.2.2))) from
      continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd))

end ContinuousMap.Homotopy

namespace Path.Homotopy

/-- Evaluating a horizontal composition gives the concatenation of the evaluated paths. -/
@[simp]
theorem eval_hcomp {a b c : X} {p₀ p₁ : Path a b} {q₀ q₁ : Path b c}
    (F : Path.Homotopy p₀ p₁) (G : Path.Homotopy q₀ q₁) (s : I) :
    (F.hcomp G).eval s = (F.eval s).trans (G.eval s) := by
  ext t
  rfl

/-- Horizontal composition preserves joint continuity of path-homotopy families whose
endpoints may vary with the parameter. -/
theorem hcomp_continuous_family {a b c : T → X}
    {p₀ p₁ : ∀ z : T, Path (a z) (b z)}
    {q₀ q₁ : ∀ z : T, Path (b z) (c z)}
    (F : ∀ z : T, Path.Homotopy (p₀ z) (p₁ z))
    (G : ∀ z : T, Path.Homotopy (q₀ z) (q₁ z))
    (hF : Continuous (fun u : T × (I × I) => F u.1 u.2))
    (hG : Continuous (fun u : T × (I × I) => G u.1 u.2)) :
    Continuous (fun u : T × (I × I) => (F u.1).hcomp (G u.1) u.2) := by
  have hF' : Continuous (fun u : (T × I) × I => (F u.1.1).eval u.1.2 u.2) :=
    hF.comp
      (show Continuous (fun u : (T × I) × I => (u.1.1, (u.1.2, u.2))) from
        continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hG' : Continuous (fun u : (T × I) × I => (G u.1.1).eval u.1.2 u.2) :=
    hG.comp
      (show Continuous (fun u : (T × I) × I => (u.1.1, (u.1.2, u.2))) from
        continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have hTrans : Continuous (fun u : (T × I) × I =>
      ((F u.1.1).eval u.1.2).trans ((G u.1.1).eval u.1.2) u.2) :=
    Path.trans_continuous_family
      (fun u : T × I => (F u.1).eval u.2) hF'
      (fun u : T × I => (G u.1).eval u.2) hG'
  have hEval := hTrans.comp
    (show Continuous (fun u : T × (I × I) => ((u.1, u.2.1), u.2.2)) from
      (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd)
  simpa [Function.comp_def, ← eval_hcomp] using hEval

end Path.Homotopy

end HomotopyComposition
