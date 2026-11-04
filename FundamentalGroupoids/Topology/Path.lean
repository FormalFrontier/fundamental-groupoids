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

At fixed endpoints, the right-unit and associativity homotopies form homotopies
on the ordinary compact-open path spaces. Their values are the time slices of
Mathlib's standard path homotopies, with joint continuity supplied by the same
continuous-family results. Precomposition gives their action on arbitrary
continuous path families.

Coordinate evaluation and Mathlib's `Path.pi` identify paths in a dependent product
with dependent products of path spaces. Their compact-open continuity follows
from `Path.continuous_uncurry_iff` and ordinary product continuity. The comparison
preserves constant paths, reversal and concatenation, and characterizes based
continuous families coordinatewise.

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

namespace Path

/-- The standard right-unit homotopy on a fixed-endpoint path space. -/
noncomputable def transReflHomotopy.{uX}
    {X : Type uX} [TopologicalSpace X] (x y : X) :
    ContinuousMap.Homotopy
      ((Path.transContinuousMap x y y).comp
        ((ContinuousMap.id (Path x y)).prodMk
          (ContinuousMap.const (Path x y) (Path.refl y))))
      (ContinuousMap.id (Path x y)) where
  toFun v := (Path.Homotopy.transRefl v.2).eval v.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    have h := Path.Homotopy.transRefl_continuous_family
      (fun p : Path x y => p)
      (Path.continuous_uncurry_iff.mpr
        (continuous_id : Continuous (id : Path x y → Path x y)))
    exact h.comp
      (show Continuous (fun v : (unitInterval × Path x y) × unitInterval =>
          (v.1.2, (v.1.1, v.2))) from
        continuous_fst.snd.prodMk (continuous_fst.fst.prodMk continuous_snd))
  map_zero_left p := (Path.Homotopy.transRefl p).eval_zero
  map_one_left p := (Path.Homotopy.transRefl p).eval_one

/-- The standard associator homotopy on three composable path spaces. -/
noncomputable def transAssocHomotopy.{uX}
    {X : Type uX} [TopologicalSpace X] (x y z w : X) :
    ContinuousMap.Homotopy
      ((Path.transContinuousMap x z w).comp
        (((Path.transContinuousMap x y z).comp
          ((ContinuousMap.fst :
            C(Path x y × (Path y z × Path z w), Path x y)).prodMk
            (ContinuousMap.fst.comp ContinuousMap.snd))).prodMk
          (ContinuousMap.snd.comp ContinuousMap.snd)))
      ((Path.transContinuousMap x y w).comp
        ((ContinuousMap.fst :
          C(Path x y × (Path y z × Path z w), Path x y)).prodMk
          ((Path.transContinuousMap y z w).comp ContinuousMap.snd))) where
  toFun v := (Path.Homotopy.transAssoc v.2.1 v.2.2.1 v.2.2.2).eval v.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    have hp : Continuous (fun v :
        (Path x y × (Path y z × Path z w)) × unitInterval => v.1.1 v.2) :=
      Path.continuous_uncurry_iff.mpr continuous_fst
    have hq : Continuous (fun v :
        (Path x y × (Path y z × Path z w)) × unitInterval => v.1.2.1 v.2) :=
      Path.continuous_uncurry_iff.mpr continuous_snd.fst
    have hr : Continuous (fun v :
        (Path x y × (Path y z × Path z w)) × unitInterval => v.1.2.2 v.2) :=
      Path.continuous_uncurry_iff.mpr continuous_snd.snd
    have h := Path.Homotopy.transAssoc_continuous_family
      (fun ρ : Path x y × (Path y z × Path z w) => ρ.1)
      (fun ρ : Path x y × (Path y z × Path z w) => ρ.2.1)
      (fun ρ : Path x y × (Path y z × Path z w) => ρ.2.2) hp hq hr
    exact h.comp
      (show Continuous (fun v :
          (unitInterval × (Path x y × (Path y z × Path z w))) × unitInterval =>
          (v.1.2, (v.1.1, v.2))) from
        continuous_fst.snd.prodMk (continuous_fst.fst.prodMk continuous_snd))
  map_zero_left := by
    rintro ⟨p, q, r⟩
    exact (Path.Homotopy.transAssoc p q r).eval_zero
  map_one_left := by
    rintro ⟨p, q, r⟩
    exact (Path.Homotopy.transAssoc p q r).eval_one

/-- Evaluate the right-unit path-space homotopy as the standard path homotopy. -/
@[simp]
theorem transReflHomotopy_apply.{uX}
    {X : Type uX} [TopologicalSpace X] (x y : X)
    (s : unitInterval) (p : Path x y) :
    Path.transReflHomotopy x y (s, p) =
      (Path.Homotopy.transRefl p).eval s := rfl

/-- Evaluate the associator as the standard homotopy on its three input paths. -/
@[simp]
theorem transAssocHomotopy_apply.{uX}
    {X : Type uX} [TopologicalSpace X] (x y z w : X)
    (s : unitInterval) (p : Path x y) (q : Path y z) (r : Path z w) :
    Path.transAssocHomotopy x y z w (s, (p, (q, r))) =
      (Path.Homotopy.transAssoc p q r).eval s := rfl

/-- Precomposition gives the same right-unit homotopy for an arbitrary path family. -/
theorem transReflHomotopy_family_apply.{uX, uP}
    {X : Type uX} {P : Type uP} [TopologicalSpace X] [TopologicalSpace P]
    {x y : X} (a : C(P, Path x y)) (s : unitInterval) (p : P) :
    ((Path.transReflHomotopy x y).compContinuousMap a) (s, p) =
      (Path.Homotopy.transRefl (a p)).eval s := rfl

/-- Precomposition gives the same associator for three arbitrary composable path families. -/
theorem transAssocHomotopy_family_apply.{uX, uP}
    {X : Type uX} {P : Type uP} [TopologicalSpace X] [TopologicalSpace P]
    {x y z w : X} (a : C(P, Path x y)) (b : C(P, Path y z))
    (c : C(P, Path z w)) (s : unitInterval) (p : P) :
    ((Path.transAssocHomotopy x y z w).compContinuousMap
      (a.prodMk (b.prodMk c))) (s, p) =
      (Path.Homotopy.transAssoc (a p) (b p) (c p)).eval s := rfl

end Path

namespace Path

/-- The right-unit homotopy fixes the constant input path at every time. -/
theorem transReflHomotopy_refl.{uX}
    {X : Type uX} [TopologicalSpace X] (x : X) (s : unitInterval) :
    Path.transReflHomotopy x x (s, Path.refl x) = Path.refl x := by
  calc
    Path.transReflHomotopy x x (s, Path.refl x) =
        (Path.Homotopy.transRefl (Path.refl x)).eval s :=
      Path.transReflHomotopy_apply x x s (Path.refl x)
    _ = Path.refl x := rfl

/-- The associator fixes the triple of constant input paths at every time. -/
theorem transAssocHomotopy_refl_refl_refl.{uX}
    {X : Type uX} [TopologicalSpace X] (x : X) (s : unitInterval) :
    Path.transAssocHomotopy x x x x
      (s, (Path.refl x, (Path.refl x, Path.refl x))) = Path.refl x := by
  rw [Path.transAssocHomotopy_apply]
  apply Path.ext
  funext t
  change ((Path.refl x).trans ((Path.refl x).trans (Path.refl x))) _ = x
  simp only [Path.refl_trans_refl]
  rfl

/-- Postcomposition commutes with the entire right-unit homotopy at the same time. -/
theorem mapContinuousMap_comp_transReflHomotopy.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x y : X) :
    (Path.mapContinuousMap f x y).comp
      (Path.transReflHomotopy x y).toContinuousMap =
    (Path.transReflHomotopy (f x) (f y)).toContinuousMap.comp
      ((ContinuousMap.id unitInterval).prodMap (Path.mapContinuousMap f x y)) := by
  apply ContinuousMap.ext
  rintro ⟨s, p⟩
  change Path.mapContinuousMap f x y (Path.transReflHomotopy x y (s, p)) =
    Path.transReflHomotopy (f x) (f y) (s, Path.mapContinuousMap f x y p)
  calc
    Path.mapContinuousMap f x y (Path.transReflHomotopy x y (s, p)) =
        Path.mapContinuousMap f x y ((Path.Homotopy.transRefl p).eval s) :=
      congrArg (Path.mapContinuousMap f x y) (Path.transReflHomotopy_apply x y s p)
    _ = (Path.Homotopy.transRefl (Path.mapContinuousMap f x y p)).eval s := rfl
    _ = Path.transReflHomotopy (f x) (f y) (s, Path.mapContinuousMap f x y p) :=
      (Path.transReflHomotopy_apply (f x) (f y) s (Path.mapContinuousMap f x y p)).symm

/-- Postcomposition commutes with the entire associator at the same time. -/
theorem mapContinuousMap_comp_transAssocHomotopy.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x y z w : X) :
    (Path.mapContinuousMap f x w).comp
      (Path.transAssocHomotopy x y z w).toContinuousMap =
    (Path.transAssocHomotopy (f x) (f y) (f z) (f w)).toContinuousMap.comp
      ((ContinuousMap.id unitInterval).prodMap
        ((Path.mapContinuousMap f x y).prodMap
          ((Path.mapContinuousMap f y z).prodMap (Path.mapContinuousMap f z w)))) := by
  apply ContinuousMap.ext
  rintro ⟨s, p, q, r⟩
  change Path.mapContinuousMap f x w
      (Path.transAssocHomotopy x y z w (s, (p, (q, r)))) =
    Path.transAssocHomotopy (f x) (f y) (f z) (f w)
      (s, (Path.mapContinuousMap f x y p,
        (Path.mapContinuousMap f y z q, Path.mapContinuousMap f z w r)))
  rw [Path.transAssocHomotopy_apply, Path.transAssocHomotopy_apply]
  apply Path.ext
  funext t
  -- The stock associator reparametrizes the right-associated concatenation.
  change ((p.trans (q.trans r)).map f.continuous) _ =
    ((p.map f.continuous).trans
      ((q.map f.continuous).trans (r.map f.continuous))) _
  rw [Path.map_trans, Path.map_trans]

end Path

section PathInverseCancellation

universe uX uY uZ

namespace Path

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [tX : TopologicalSpace X] [tY : TopologicalSpace Y] [tZ : TopologicalSpace Z]

/-- Jointly continuous cancellation of a path followed by its reverse, on the ordinary
path space. This reverses outer time in Mathlib's `Path.Homotopy.reflTransSymm`;
joint continuity is supplied by `Path.Homotopy.reflTransSymm_continuous_family`. -/
noncomputable def transSymmHomotopy (x y : X) :
    ContinuousMap.Homotopy
      ((Path.transContinuousMap x y x).comp
        ((ContinuousMap.id (Path x y)).prodMk
          (⟨Path.symm, Path.continuous_symm⟩ : C(Path x y, Path y x))))
      (ContinuousMap.const (Path x y) (Path.refl x)) where
  toFun v := (Path.Homotopy.reflTransSymm v.2).symm.eval v.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    have hp : Continuous (fun v : Path x y × unitInterval => v.1 v.2) :=
      Path.continuous_uncurry_iff.mpr
        (continuous_id : Continuous (id : Path x y → Path x y))
    have h := Path.Homotopy.reflTransSymm_continuous_family
      (fun p : Path x y => p) hp
    change Continuous (fun v : (unitInterval × Path x y) × unitInterval =>
      Path.Homotopy.reflTransSymm v.1.2 (σ v.1.1, v.2))
    exact h.comp
      (continuous_fst.snd.prodMk
        ((unitInterval.continuous_symm.comp continuous_fst.fst).prodMk continuous_snd))
  map_zero_left p := by
    change (Path.Homotopy.reflTransSymm p).symm.eval 0 = p.trans p.symm
    exact Path.Homotopy.eval_zero _
  map_one_left p := by
    change (Path.Homotopy.reflTransSymm p).symm.eval 1 = Path.refl x
    exact Path.Homotopy.eval_one _

/-- Jointly continuous cancellation of the reverse path followed by the path.
This reverses outer time in Mathlib's `Path.Homotopy.reflSymmTrans`, retaining
its endpoint-path correction cast. Continuity uses the same joint-family engine
as `transSymmHomotopy`, applied to the reversed paths. -/
noncomputable def symmTransHomotopy (x y : X) :
    ContinuousMap.Homotopy
      ((Path.transContinuousMap y x y).comp
        ((⟨Path.symm, Path.continuous_symm⟩ : C(Path x y, Path y x)).prodMk
          (ContinuousMap.id (Path x y))))
      (ContinuousMap.const (Path x y) (Path.refl y)) where
  toFun v := (Path.Homotopy.reflSymmTrans v.2).symm.eval v.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    have hp : Continuous (fun v : Path x y × unitInterval => v.1 v.2) :=
      Path.continuous_uncurry_iff.mpr
        (continuous_id : Continuous (id : Path x y → Path x y))
    have hsymm := Path.symm_continuous_family (fun p : Path x y => p) hp
    have h := Path.Homotopy.reflTransSymm_continuous_family
      (fun p : Path x y => p.symm) hsymm
    change Continuous (fun v : (unitInterval × Path x y) × unitInterval =>
      Path.Homotopy.reflTransSymm v.1.2.symm (σ v.1.1, v.2))
    exact h.comp
      (continuous_fst.snd.prodMk
        ((unitInterval.continuous_symm.comp continuous_fst.fst).prodMk continuous_snd))
  map_zero_left p := by
    change (Path.Homotopy.reflSymmTrans p).symm.eval 0 = p.symm.trans p
    exact Path.Homotopy.eval_zero _
  map_one_left p := by
    change (Path.Homotopy.reflSymmTrans p).symm.eval 1 = Path.refl y
    exact Path.Homotopy.eval_one _

/-- The whole-path slice is the outer-reversed stock path homotopy. -/
@[simp]
theorem transSymmHomotopy_apply (x y : X) (s : unitInterval) (p : Path x y) :
    Path.transSymmHomotopy x y (s, p) =
      (Path.Homotopy.reflTransSymm p).symm.eval s := rfl

/-- The whole-path slice is the outer-reversed stock homotopy with its existing cast. -/
@[simp]
theorem symmTransHomotopy_apply (x y : X) (s : unitInterval) (p : Path x y) :
    Path.symmTransHomotopy x y (s, p) =
      (Path.Homotopy.reflSymmTrans p).symm.eval s := rfl

/-- Inner-time evaluation agrees with the stock homotopy at every pair of times. -/
theorem transSymmHomotopy_apply_apply (x y : X)
    (s t : unitInterval) (p : Path x y) :
    Path.transSymmHomotopy x y (s, p) t =
      (Path.Homotopy.reflTransSymm p).symm (s, t) := by
  simp only [transSymmHomotopy_apply, Path.Homotopy.eval_apply,
    ContinuousMap.Homotopy.curry_apply, ContinuousMap.HomotopyWith.coe_toHomotopy]

/-- Inner-time evaluation agrees with the second stock homotopy at every pair of times. -/
theorem symmTransHomotopy_apply_apply (x y : X)
    (s t : unitInterval) (p : Path x y) :
    Path.symmTransHomotopy x y (s, p) t =
      (Path.Homotopy.reflSymmTrans p).symm (s, t) := by
  simp only [symmTransHomotopy_apply, Path.Homotopy.eval_apply,
    ContinuousMap.Homotopy.curry_apply, ContinuousMap.HomotopyWith.coe_toHomotopy]

/-- Every outer-time slice fixes the constant path. -/
theorem transSymmHomotopy_refl (x : X) (s : unitInterval) :
    Path.transSymmHomotopy x x (s, Path.refl x) = Path.refl x := by
  apply Path.ext
  funext t
  exact transSymmHomotopy_apply_apply x x s t (Path.refl x)

/-- Reverse-then-forward cancellation also fixes the constant path at every time. -/
theorem symmTransHomotopy_refl (x : X) (s : unitInterval) :
    Path.symmTransHomotopy x x (s, Path.refl x) = Path.refl x := by
  apply Path.ext
  funext t
  exact symmTransHomotopy_apply_apply x x s t (Path.refl x)

/-- Precomposition gives cancellation for an arbitrary continuous family of paths. -/
theorem transSymmHomotopy_family_apply {x y : X}
    (a : C(Z, Path x y)) (s : unitInterval) (z : Z) :
    ((Path.transSymmHomotopy x y).compContinuousMap a) (s, z) =
      (Path.Homotopy.reflTransSymm (a z)).symm.eval s :=
  transSymmHomotopy_apply x y s (a z)

/-- Precomposition gives reverse-then-forward cancellation for a continuous family. -/
theorem symmTransHomotopy_family_apply {x y : X}
    (a : C(Z, Path x y)) (s : unitInterval) (z : Z) :
    ((Path.symmTransHomotopy x y).compContinuousMap a) (s, z) =
      (Path.Homotopy.reflSymmTrans (a z)).symm.eval s :=
  symmTransHomotopy_apply x y s (a z)

/-- Postcomposition commutes with cancellation as an equality of whole continuous maps. -/
theorem mapContinuousMap_comp_transSymmHomotopy (f : C(X, Y)) (x y : X) :
    (Path.mapContinuousMap f x x).comp
        (Path.transSymmHomotopy x y).toContinuousMap =
      (Path.transSymmHomotopy (f x) (f y)).toContinuousMap.comp
        ((ContinuousMap.id unitInterval).prodMap (Path.mapContinuousMap f x y)) := by
  apply ContinuousMap.ext
  rintro ⟨s, p⟩
  apply Path.ext
  funext t
  change f (Path.transSymmHomotopy x y (s, p) t) =
    Path.transSymmHomotopy (f x) (f y) (s, Path.mapContinuousMap f x y p) t
  calc
    f (Path.transSymmHomotopy x y (s, p) t) =
        f ((Path.Homotopy.reflTransSymm p).symm (s, t)) :=
      congrArg f (transSymmHomotopy_apply_apply x y s t p)
    _ = (Path.Homotopy.reflTransSymm (Path.mapContinuousMap f x y p)).symm (s, t) := rfl
    _ = Path.transSymmHomotopy (f x) (f y) (s, Path.mapContinuousMap f x y p) t :=
      (transSymmHomotopy_apply_apply (f x) (f y) s t (Path.mapContinuousMap f x y p)).symm

/-- Postcomposition commutes with reverse-then-forward cancellation on whole maps. -/
theorem mapContinuousMap_comp_symmTransHomotopy (f : C(X, Y)) (x y : X) :
    (Path.mapContinuousMap f y y).comp
        (Path.symmTransHomotopy x y).toContinuousMap =
      (Path.symmTransHomotopy (f x) (f y)).toContinuousMap.comp
        ((ContinuousMap.id unitInterval).prodMap (Path.mapContinuousMap f x y)) := by
  apply ContinuousMap.ext
  rintro ⟨s, p⟩
  apply Path.ext
  funext t
  change f (Path.symmTransHomotopy x y (s, p) t) =
    Path.symmTransHomotopy (f x) (f y) (s, Path.mapContinuousMap f x y p) t
  calc
    f (Path.symmTransHomotopy x y (s, p) t) =
        f ((Path.Homotopy.reflSymmTrans p).symm (s, t)) :=
      congrArg f (symmTransHomotopy_apply_apply x y s t p)
    _ = (Path.Homotopy.reflSymmTrans (Path.mapContinuousMap f x y p)).symm (s, t) := rfl
    _ = Path.symmTransHomotopy (f x) (f y) (s, Path.mapContinuousMap f x y p) t :=
      (symmTransHomotopy_apply_apply (f x) (f y) s t (Path.mapContinuousMap f x y p)).symm

end Path

namespace ContinuousMap

variable {X : Type uX} {Y : Type uY}
variable [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/-- Cancellation commutes with the genuine loop map, including both endpoint transports. -/
theorem loopMap_comp_transSymmHomotopy (f : C(X, Y))
    (e : X) (b : Y) (h : f e = b) :
    (f.loopMap e b h).comp (Path.transSymmHomotopy e e).toContinuousMap =
      (Path.transSymmHomotopy b b).toContinuousMap.comp
        ((ContinuousMap.id unitInterval).prodMap (f.loopMap e b h)) := by
  apply ContinuousMap.ext
  rintro ⟨s, p⟩
  apply Path.ext
  funext t
  change f (Path.transSymmHomotopy e e (s, p) t) =
    Path.transSymmHomotopy b b (s, f.loopMap e b h p) t
  calc
    f (Path.transSymmHomotopy e e (s, p) t) =
        f ((Path.Homotopy.reflTransSymm p).symm (s, t)) :=
      congrArg f (Path.transSymmHomotopy_apply_apply e e s t p)
    _ = (Path.Homotopy.reflTransSymm (f.loopMap e b h p)).symm (s, t) := rfl
    _ = Path.transSymmHomotopy b b (s, f.loopMap e b h p) t :=
      (Path.transSymmHomotopy_apply_apply b b s t (f.loopMap e b h p)).symm

/-- Reverse-then-forward cancellation commutes with loop maps with arbitrary basepoint
identification; neither of the original endpoint transports is removed. -/
theorem loopMap_comp_symmTransHomotopy (f : C(X, Y))
    (e : X) (b : Y) (h : f e = b) :
    (f.loopMap e b h).comp (Path.symmTransHomotopy e e).toContinuousMap =
      (Path.symmTransHomotopy b b).toContinuousMap.comp
        ((ContinuousMap.id unitInterval).prodMap (f.loopMap e b h)) := by
  apply ContinuousMap.ext
  rintro ⟨s, p⟩
  apply Path.ext
  funext t
  change f (Path.symmTransHomotopy e e (s, p) t) =
    Path.symmTransHomotopy b b (s, f.loopMap e b h p) t
  calc
    f (Path.symmTransHomotopy e e (s, p) t) =
        f ((Path.Homotopy.reflSymmTrans p).symm (s, t)) :=
      congrArg f (Path.symmTransHomotopy_apply_apply e e s t p)
    _ = (Path.Homotopy.reflSymmTrans (f.loopMap e b h p)).symm (s, t) := rfl
    _ = Path.symmTransHomotopy b b (s, f.loopMap e b h p) t :=
      (Path.symmTransHomotopy_apply_apply b b s t (f.loopMap e b h p)).symm

end ContinuousMap

end PathInverseCancellation

/-- The standard left-unit homotopy on a fixed-endpoint path space.
Mathlib's `Path.Homotopy.reflTrans` supplies its time slices; continuity follows by
reversing paths before and after `Path.transReflHomotopy`. -/
noncomputable def Path.reflTransHomotopy.{uX}
    {X : Type uX} [TopologicalSpace X] (x y : X) :
    ContinuousMap.Homotopy
      ((Path.transContinuousMap x x y).comp
        ((ContinuousMap.const (Path x y) (Path.refl x)).prodMk
          (ContinuousMap.id (Path x y))))
      (ContinuousMap.id (Path x y)) where
  toFun v := (Path.Homotopy.reflTrans v.2).eval v.1
  continuous_toFun := by
    change Continuous (fun v : unitInterval × Path x y =>
      (Path.transReflHomotopy y x (v.1, v.2.symm)).symm)
    exact Path.continuous_symm.comp
      ((Path.transReflHomotopy y x).toContinuousMap.continuous.comp
        (continuous_fst.prodMk (Path.continuous_symm.comp continuous_snd)))
  map_zero_left p := (Path.Homotopy.reflTrans p).eval_zero
  map_one_left p := (Path.Homotopy.reflTrans p).eval_one

/-- Evaluate the left-unit path-space homotopy as Mathlib's standard path homotopy. -/
@[simp] theorem Path.reflTransHomotopy_apply.{uX}
    {X : Type uX} [TopologicalSpace X] (x y : X)
    (s : unitInterval) (p : Path x y) :
    Path.reflTransHomotopy x y (s, p) =
      (Path.Homotopy.reflTrans p).eval s := rfl

/-- Inner-time evaluation agrees with the standard left-unit path homotopy. -/
theorem Path.reflTransHomotopy_apply_apply.{uX}
    {X : Type uX} [TopologicalSpace X] (x y : X)
    (s : unitInterval) (p : Path x y) (t : unitInterval) :
    Path.reflTransHomotopy x y (s, p) t =
      Path.Homotopy.reflTrans p (s, t) := rfl

/-- The left-unit homotopy starts at concatenation with the constant path. -/
theorem Path.reflTransHomotopy_zero.{uX}
    {X : Type uX} [TopologicalSpace X] (x y : X) (p : Path x y) :
    Path.reflTransHomotopy x y (0, p) = (Path.refl x).trans p :=
  (Path.reflTransHomotopy x y).apply_zero p

/-- The left-unit homotopy ends at the original path. -/
theorem Path.reflTransHomotopy_one.{uX}
    {X : Type uX} [TopologicalSpace X] (x y : X) (p : Path x y) :
    Path.reflTransHomotopy x y (1, p) = p :=
  (Path.reflTransHomotopy x y).apply_one p

/-- The left-unit homotopy fixes the constant input path at every time. -/
theorem Path.reflTransHomotopy_refl.{uX}
    {X : Type uX} [TopologicalSpace X] (x : X) (s : unitInterval) :
    Path.reflTransHomotopy x x (s, Path.refl x) = Path.refl x := by
  rw [Path.reflTransHomotopy_apply]
  rfl

/-- Precomposition gives the standard left-unit homotopy for an arbitrary path family. -/
theorem Path.reflTransHomotopy_family_apply.{uX, uP}
    {X : Type uX} {P : Type uP} [TopologicalSpace X] [TopologicalSpace P]
    {x y : X} (a : C(P, Path x y)) (s : unitInterval) (p : P) :
    ((Path.reflTransHomotopy x y).compContinuousMap a) (s, p) =
      (Path.Homotopy.reflTrans (a p)).eval s := rfl

/-- Inner-time evaluation of a left-unit homotopy family is the stock path homotopy. -/
theorem Path.reflTransHomotopy_family_apply_apply.{uX, uP}
    {X : Type uX} {P : Type uP} [TopologicalSpace X] [TopologicalSpace P]
    {x y : X} (a : C(P, Path x y))
    (s : unitInterval) (p : P) (t : unitInterval) :
    ((Path.reflTransHomotopy x y).compContinuousMap a) (s, p) t =
      Path.Homotopy.reflTrans (a p) (s, t) := rfl

/-- A parameter whose path is constant remains fixed throughout the left-unit family. -/
theorem Path.reflTransHomotopy_family_point.{uX, uP}
    {X : Type uX} {P : Type uP} [TopologicalSpace X] [TopologicalSpace P]
    {x : X} (a : C(P, Path x x)) (p₀ : P)
    (ha : a p₀ = Path.refl x) (s : unitInterval) :
    ((Path.reflTransHomotopy x x).compContinuousMap a) (s, p₀) = Path.refl x := by
  change Path.reflTransHomotopy x x (s, a p₀) = Path.refl x
  rw [ha, Path.reflTransHomotopy_refl]

/-- The left-unit loop-space homotopy relative to the constant loop. -/
noncomputable def Path.reflTransHomotopyRel.{uX}
    {X : Type uX} [TopologicalSpace X] (x : X) :
    ContinuousMap.HomotopyRel
      ((Path.transContinuousMap x x x).comp
        ((ContinuousMap.const (Path x x) (Path.refl x)).prodMk
          (ContinuousMap.id (Path x x))))
      (ContinuousMap.id (Path x x)) {Path.refl x} where
  toHomotopy := Path.reflTransHomotopy x x
  prop' s p hp := by
    rcases Set.mem_singleton_iff.mp hp with rfl
    change Path.reflTransHomotopy x x (s, Path.refl x) =
      (Path.refl x).trans (Path.refl x)
    rw [Path.reflTransHomotopy_refl, Path.refl_trans_refl]

/-- Forgetting the relative condition recovers the left-unit path-space homotopy. -/
@[simp] theorem Path.reflTransHomotopyRel_toHomotopy.{uX}
    {X : Type uX} [TopologicalSpace X] (x : X) :
    (Path.reflTransHomotopyRel x).toHomotopy = Path.reflTransHomotopy x x := rfl

/-- The relative left-unit homotopy has the same values as its underlying homotopy. -/
theorem Path.reflTransHomotopyRel_apply.{uX}
    {X : Type uX} [TopologicalSpace X] (x : X)
    (s : unitInterval) (p : Path x x) :
    Path.reflTransHomotopyRel x (s, p) = Path.reflTransHomotopy x x (s, p) := rfl

/-- Postcomposition commutes with the entire left-unit homotopy at the same time. -/
theorem Path.mapContinuousMap_comp_reflTransHomotopy.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x y : X) :
    (Path.mapContinuousMap f x y).comp
      (Path.reflTransHomotopy x y).toContinuousMap =
    (Path.reflTransHomotopy (f x) (f y)).toContinuousMap.comp
      ((ContinuousMap.id unitInterval).prodMap (Path.mapContinuousMap f x y)) := by
  apply ContinuousMap.ext
  rintro ⟨s, p⟩
  change Path.mapContinuousMap f x y (Path.reflTransHomotopy x y (s, p)) =
    Path.reflTransHomotopy (f x) (f y) (s, Path.mapContinuousMap f x y p)
  rw [Path.reflTransHomotopy_apply, Path.reflTransHomotopy_apply]
  apply Path.ext
  funext t
  rfl

/-- The original endpoint-transported loop map commutes with the left-unit homotopy. -/
theorem ContinuousMap.loopMap_comp_reflTransHomotopy.{uX, uY}
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) :
    (f.loopMap x y h).comp (Path.reflTransHomotopy x x).toContinuousMap =
    (Path.reflTransHomotopy y y).toContinuousMap.comp
      ((ContinuousMap.id unitInterval).prodMap (f.loopMap x y h)) := by
  apply ContinuousMap.ext
  rintro ⟨s, p⟩
  change f.loopMap x y h (Path.reflTransHomotopy x x (s, p)) =
    Path.reflTransHomotopy y y (s, f.loopMap x y h p)
  rw [Path.reflTransHomotopy_apply, Path.reflTransHomotopy_apply]
  apply Path.ext
  funext t
  rfl

/-- Postcomposition commutes with left-unit homotopies of arbitrary path families. -/
theorem Path.mapContinuousMap_comp_reflTransHomotopy_family.{uX, uP, uY}
    {X : Type uX} {P : Type uP} {Y : Type uY}
    [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace Y]
    {x y : X} (a : C(P, Path x y)) (f : C(X, Y)) :
    (Path.mapContinuousMap f x y).comp
      ((Path.reflTransHomotopy x y).compContinuousMap a).toContinuousMap =
    ((Path.reflTransHomotopy (f x) (f y)).compContinuousMap
      ((Path.mapContinuousMap f x y).comp a)).toContinuousMap := by
  apply ContinuousMap.ext
  rintro ⟨s, p⟩
  exact congrArg (fun g : C(unitInterval × Path x y, Path (f x) (f y)) =>
    g (s, a p)) (Path.mapContinuousMap_comp_reflTransHomotopy f x y)

/-- Endpoint-transported loop maps commute with left-unit homotopies of loop families. -/
theorem ContinuousMap.loopMap_comp_reflTransHomotopy_family.{uX, uP, uY}
    {X : Type uX} {P : Type uP} {Y : Type uY}
    [TopologicalSpace X] [TopologicalSpace P] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (a : C(P, Path x x)) :
    (f.loopMap x y h).comp
      ((Path.reflTransHomotopy x x).compContinuousMap a).toContinuousMap =
    ((Path.reflTransHomotopy y y).compContinuousMap
      ((f.loopMap x y h).comp a)).toContinuousMap := by
  apply ContinuousMap.ext
  rintro ⟨s, p⟩
  exact congrArg (fun g : C(unitInterval × Path x x, Path y y) =>
    g (s, a p)) (ContinuousMap.loopMap_comp_reflTransHomotopy f x y h)

namespace Path

/-- Paths in a dependent product are homeomorphic to dependent products of path spaces.
The inverse is `Path.pi`. The whole continuous-map inverse identities are
`Homeomorph.symm_comp_toContinuousMap` and `Homeomorph.toContinuousMap_comp_symm`. -/
def piHomeomorph.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (x y : ∀ i, X i) :
    Path x y ≃ₜ (∀ i, Path (x i) (y i)) where
  toFun γ i := Path.mapContinuousMap (ContinuousMap.eval i) x y γ
  invFun := Path.pi
  left_inv γ := by
    apply Path.ext
    funext t i
    rfl
  right_inv p := by
    funext i
    apply Path.ext
    funext t
    rfl
  continuous_toFun :=
    map_continuous (ContinuousMap.pi
      (fun i => Path.mapContinuousMap (ContinuousMap.eval i) x y))
  continuous_invFun := by
    apply Path.continuous_uncurry_iff.mp
    exact continuous_pi fun i =>
      Path.continuous_uncurry_iff.mpr
        (continuous_apply i :
          Continuous (fun p : ∀ j, Path (x j) (y j) => p i))

/-- The forward continuous map is the product of the coordinate path maps. -/
theorem piHomeomorph_toContinuousMap.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (x y : ∀ i, X i) :
    (Path.piHomeomorph x y :
        C(Path x y, ∀ i, Path (x i) (y i))) =
      ContinuousMap.pi
        (fun i => Path.mapContinuousMap (ContinuousMap.eval i) x y) := rfl

/-- The coordinate path of the comparison is induced by coordinate evaluation. -/
@[simp]
theorem piHomeomorph_apply.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (x y : ∀ i, X i) (γ : Path x y) (i : ι) :
    Path.piHomeomorph x y γ i =
      Path.mapContinuousMap (ContinuousMap.eval i) x y γ := rfl

/-- Evaluating a coordinate path recovers that coordinate of the original path. -/
theorem piHomeomorph_apply_apply.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (x y : ∀ i, X i) (γ : Path x y) (i : ι) (t : unitInterval) :
    Path.piHomeomorph x y γ i t = γ t i := rfl

/-- The inverse comparison is the pointwise product of the coordinate paths. -/
@[simp]
theorem piHomeomorph_symm_apply.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (x y : ∀ i, X i) (p : ∀ i, Path (x i) (y i)) :
    (Path.piHomeomorph x y).symm p = Path.pi p := rfl

/-- Evaluating the inverse comparison recovers the given coordinate path value. -/
theorem piHomeomorph_symm_apply_apply.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (x y : ∀ i, X i) (p : ∀ i, Path (x i) (y i))
    (t : unitInterval) (i : ι) :
    (Path.piHomeomorph x y).symm p t i = p i t := rfl

/-- Paths in a dependent product are equal exactly when all coordinate values agree. -/
theorem pi_ext_iff.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    {x y : ∀ i, X i} {γ δ : Path x y} :
    γ = δ ↔ ∀ i (t : unitInterval), γ t i = δ t i := by
  constructor
  · rintro rfl i t
    rfl
  · intro h
    apply Path.ext
    funext t i
    exact h i t

/-- The constant path corresponds to the family of constant coordinate paths. -/
@[simp]
theorem piHomeomorph_refl.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)] (x : ∀ i, X i) :
    Path.piHomeomorph x x (Path.refl x) = fun i => Path.refl (x i) := by
  funext i
  apply Path.ext
  funext t
  exact piHomeomorph_apply_apply x x (Path.refl x) i t

/-- Reversing a path reverses every coordinate path. -/
@[simp]
theorem piHomeomorph_apply_symm.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (x y : ∀ i, X i) (γ : Path x y) :
    Path.piHomeomorph y x γ.symm =
      fun i => (Path.piHomeomorph x y γ i).symm := by
  funext i
  exact (piHomeomorph_apply y x γ.symm i).trans
    ((Path.map_symm γ (ContinuousMap.eval i).continuous).symm.trans
      (congrArg (fun p : Path (x i) (y i) => p.symm)
        (piHomeomorph_apply x y γ i).symm))

/-- Concatenation corresponds to coordinatewise concatenation with the same clock. -/
@[simp]
theorem piHomeomorph_apply_trans.{uι, uX}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (x y z : ∀ i, X i) (γ : Path x y) (δ : Path y z) :
    Path.piHomeomorph x z (γ.trans δ) =
      fun i => (Path.piHomeomorph x y γ i).trans
        (Path.piHomeomorph y z δ i) := by
  funext i
  exact (piHomeomorph_apply x z (γ.trans δ) i).trans
    ((Path.map_trans γ δ (ContinuousMap.eval i).continuous).trans
      (congrArg₂ (fun (p : Path (x i) (y i)) (q : Path (y i) (z i)) => p.trans q)
        (piHomeomorph_apply x y γ i).symm
        (piHomeomorph_apply y z δ i).symm))

/-- A loop family has a constant selected value exactly when all its coordinates do. -/
theorem piHomeomorph_family_refl_iff.{uι, uX, uP}
    {ι : Type uι} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    {P : Type uP} [TopologicalSpace P]
    (x : ∀ i, X i) (A : C(P, Path x x)) (p₀ : P) :
    A p₀ = Path.refl x ↔
      ∀ i, ((Path.mapContinuousMap (ContinuousMap.eval i) x x).comp A) p₀ =
        Path.refl (x i) := by
  constructor
  · intro h i
    exact ((piHomeomorph_apply x x (A p₀) i).symm.trans
      (congrArg (fun γ : Path x x => Path.piHomeomorph x x γ i) h)).trans
        (congrFun (piHomeomorph_refl x) i)
  · intro h
    apply Path.pi_ext_iff.mpr
    intro i t
    exact congrArg (fun γ : Path (x i) (x i) => γ t) (h i)

end Path

@[expose] public section

namespace Path

/-- Taking coordinate paths commutes with componentwise continuous maps. -/
theorem piHomeomorph_comp_mapContinuousMap.{uι, uX, uY}
    {ι : Type uι} {X : ι → Type uX} {Y : ι → Type uY}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, C(X i, Y i)) (x y : ∀ i, X i) :
    (Path.piHomeomorph (fun i => f i (x i)) (fun i => f i (y i)) :
        C(Path (fun i => f i (x i)) (fun i => f i (y i)),
          ∀ i, Path (f i (x i)) (f i (y i)))).comp
      (Path.mapContinuousMap (ContinuousMap.piMap f) x y) =
    (ContinuousMap.piMap
      (fun i => Path.mapContinuousMap (f i) (x i) (y i))).comp
      (Path.piHomeomorph x y : C(Path x y, ∀ i, Path (x i) (y i))) := by
  apply ContinuousMap.ext
  intro γ
  funext i
  apply Path.ext
  funext t
  calc
    _ = Path.mapContinuousMap (ContinuousMap.piMap f) x y γ t i :=
      piHomeomorph_apply_apply _ _ _ i t
    _ = f i (γ t i) :=
      congrArg (fun z => z i)
        (mapContinuousMap_apply_apply (ContinuousMap.piMap f) x y γ t)
    _ = f i (Path.piHomeomorph x y γ i t) :=
      congrArg (f i) (piHomeomorph_apply_apply x y γ i t).symm
    _ = _ :=
      (mapContinuousMap_apply_apply (f i) (x i) (y i)
        (Path.piHomeomorph x y γ i) t).symm

/-- Assembling coordinate paths commutes with componentwise continuous maps. -/
theorem mapContinuousMap_comp_piHomeomorph_symm.{uι, uX, uY}
    {ι : Type uι} {X : ι → Type uX} {Y : ι → Type uY}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, C(X i, Y i)) (x y : ∀ i, X i) :
    (Path.mapContinuousMap (ContinuousMap.piMap f) x y).comp
      ((Path.piHomeomorph x y).symm :
        C((∀ i, Path (x i) (y i)), Path x y)) =
    ((Path.piHomeomorph (fun i => f i (x i)) (fun i => f i (y i))).symm :
        C((∀ i, Path (f i (x i)) (f i (y i))),
          Path (fun i => f i (x i)) (fun i => f i (y i)))).comp
      (ContinuousMap.piMap
        (fun i => Path.mapContinuousMap (f i) (x i) (y i))) := by
  apply ContinuousMap.ext
  intro p
  apply pi_ext_iff.mpr
  intro i t
  calc
    _ = f i ((Path.piHomeomorph x y).symm p t i) :=
      congrArg (fun z => z i)
        (mapContinuousMap_apply_apply (ContinuousMap.piMap f) x y
          ((Path.piHomeomorph x y).symm p) t)
    _ = f i (p i t) :=
      congrArg (f i) (piHomeomorph_symm_apply_apply x y p t i)
    _ = Path.mapContinuousMap (f i) (x i) (y i) (p i) t :=
      (mapContinuousMap_apply_apply (f i) (x i) (y i) (p i) t).symm
    _ = _ :=
      (piHomeomorph_symm_apply_apply _ _
        (ContinuousMap.piMap
          (fun i => Path.mapContinuousMap (f i) (x i) (y i)) p) t i).symm

/-- Taking coordinate paths commutes with reindexing along any function. -/
theorem piHomeomorph_reindex.{uι, uJ, uX}
    {ι : Type uι} {J : Type uJ} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (r : J → ι) (x y : ∀ i, X i) :
    (Path.piHomeomorph (fun j => x (r j)) (fun j => y (r j)) :
        C(Path (fun j => x (r j)) (fun j => y (r j)),
          ∀ j, Path (x (r j)) (y (r j)))).comp
      (Path.mapContinuousMap (ContinuousMap.precomp (X := X) r) x y) =
    (ContinuousMap.precomp (X := fun i => Path (x i) (y i)) r).comp
      (Path.piHomeomorph x y : C(Path x y, ∀ i, Path (x i) (y i))) := by
  apply ContinuousMap.ext
  intro γ
  funext j
  apply Path.ext
  funext t
  calc
    _ = Path.mapContinuousMap (ContinuousMap.precomp (X := X) r) x y γ t j :=
      piHomeomorph_apply_apply _ _ _ j t
    _ = γ t (r j) :=
      congrArg (fun z => z j)
        (mapContinuousMap_apply_apply (ContinuousMap.precomp (X := X) r) x y γ t)
    _ = _ := (piHomeomorph_apply_apply x y γ (r j) t).symm

/-- Assembling coordinate paths commutes with reindexing along any function. -/
theorem piHomeomorph_symm_reindex.{uι, uJ, uX}
    {ι : Type uι} {J : Type uJ} {X : ι → Type uX}
    [∀ i, TopologicalSpace (X i)]
    (r : J → ι) (x y : ∀ i, X i) :
    (Path.mapContinuousMap (ContinuousMap.precomp (X := X) r) x y).comp
      ((Path.piHomeomorph x y).symm :
        C((∀ i, Path (x i) (y i)), Path x y)) =
    ((Path.piHomeomorph (fun j => x (r j)) (fun j => y (r j))).symm :
        C((∀ j, Path (x (r j)) (y (r j))),
          Path (fun j => x (r j)) (fun j => y (r j)))).comp
      (ContinuousMap.precomp (X := fun i => Path (x i) (y i)) r) := by
  apply ContinuousMap.ext
  intro p
  apply pi_ext_iff.mpr
  intro j t
  calc
    _ = (Path.piHomeomorph x y).symm p t (r j) :=
      congrArg (fun z => z j)
        (mapContinuousMap_apply_apply (ContinuousMap.precomp (X := X) r) x y
          ((Path.piHomeomorph x y).symm p) t)
    _ = p (r j) t := piHomeomorph_symm_apply_apply x y p t (r j)
    _ = _ :=
      (piHomeomorph_symm_apply_apply _ _
        (ContinuousMap.precomp (X := fun i => Path (x i) (y i)) r p) t j).symm

/-- Taking coordinate loops commutes with loop maps with specified endpoint equations. -/
theorem piHomeomorph_comp_loopMap.{uι, uX, uY}
    {ι : Type uι} {X : ι → Type uX} {Y : ι → Type uY}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, C(X i, Y i)) (a : ∀ i, X i) (b : ∀ i, Y i)
    (h : ∀ i, f i (a i) = b i) :
    (Path.piHomeomorph b b : C(Path b b, ∀ i, Path (b i) (b i))).comp
      ((ContinuousMap.piMap f).loopMap a b (funext h)) =
    (ContinuousMap.piMap
      (fun i => (f i).loopMap (a i) (b i) (h i))).comp
      (Path.piHomeomorph a a : C(Path a a, ∀ i, Path (a i) (a i))) := by
  apply ContinuousMap.ext
  intro γ
  funext i
  apply Path.ext
  funext t
  calc
    _ = (ContinuousMap.piMap f).loopMap a b (funext h) γ t i :=
      piHomeomorph_apply_apply b b _ i t
    _ = f i (γ t i) :=
      congrArg (fun z => z i)
        (ContinuousMap.loopMap_apply_apply (ContinuousMap.piMap f) a b (funext h) γ t)
    _ = f i (Path.piHomeomorph a a γ i t) :=
      congrArg (f i) (piHomeomorph_apply_apply a a γ i t).symm
    _ = _ :=
      (ContinuousMap.loopMap_apply_apply (f i) (a i) (b i) (h i)
        (Path.piHomeomorph a a γ i) t).symm

/-- Assembling coordinate loops commutes with loop maps with specified endpoint equations. -/
theorem loopMap_comp_piHomeomorph_symm.{uι, uX, uY}
    {ι : Type uι} {X : ι → Type uX} {Y : ι → Type uY}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (f : ∀ i, C(X i, Y i)) (a : ∀ i, X i) (b : ∀ i, Y i)
    (h : ∀ i, f i (a i) = b i) :
    ((ContinuousMap.piMap f).loopMap a b (funext h)).comp
      ((Path.piHomeomorph a a).symm :
        C((∀ i, Path (a i) (a i)), Path a a)) =
    ((Path.piHomeomorph b b).symm :
        C((∀ i, Path (b i) (b i)), Path b b)).comp
      (ContinuousMap.piMap (fun i => (f i).loopMap (a i) (b i) (h i))) := by
  apply ContinuousMap.ext
  intro p
  apply pi_ext_iff.mpr
  intro i t
  calc
    _ = f i ((Path.piHomeomorph a a).symm p t i) :=
      congrArg (fun z => z i)
        (ContinuousMap.loopMap_apply_apply (ContinuousMap.piMap f) a b (funext h)
          ((Path.piHomeomorph a a).symm p) t)
    _ = f i (p i t) :=
      congrArg (f i) (piHomeomorph_symm_apply_apply a a p t i)
    _ = (f i).loopMap (a i) (b i) (h i) (p i) t :=
      (ContinuousMap.loopMap_apply_apply (f i) (a i) (b i) (h i) (p i) t).symm
    _ = _ :=
      (piHomeomorph_symm_apply_apply b b
        (ContinuousMap.piMap (fun i => (f i).loopMap (a i) (b i) (h i)) p) t i).symm

end Path
