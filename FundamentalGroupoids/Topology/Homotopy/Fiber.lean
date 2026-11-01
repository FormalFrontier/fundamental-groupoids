/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.RelativePathSpace
public import FundamentalGroupoids.Topology.Homeomorph.Subtype
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks

/-!
# Ordinary homotopy fibers

`ContinuousMap.HomotopyFiber f b` retains a point `e` and a compact-open path
from `b` to `f e`, with the subspace topology from `E × C(I, X)`. In particular,
different points with the same image remain different fiber points.

The fiber is homeomorphic to the ordinary pullback of `f` and terminal evaluation
on paths starting at `b`. For an embedding `f`, forgetting the point gives a
homeomorphism to paths starting at `b` and ending in `Set.range f`. The comparison
uses Mathlib's whole `TopCat.pullbackHomeoPreimage`, after regrouping and swapping
the product coordinates, and then flattens the two endpoint subspaces.

For the original subspace inclusion `ContinuousMap.subtypeVal A`, this yields
paths ending in `A` itself. The inverse point is their terminal point in `A`.
Maps under continuous commutative squares act on the point and postcompose the
path, and the embedding comparison is natural under these maps.

## Implementation notes

Only ordinary product, subspace and compact-open topologies are used. The default
topology on a sigma of fixed-endpoint path spaces is not used: it would separate
the varying point coordinate. May's weak-Hausdorff/k-space conventions are not
identified with the ordinary topologies here. No relative homotopy groups or
fiber sequence assertions are made.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, §6, p. 61
  (path direction and pullback fiber), and Chapter 9, §1, p. 65 (subspace endpoint
  paths).
* Mathlib, `TopCat.pullbackHomeoPreimage`, for elimination of the embedded
  coordinate with its inverse continuity; compact-open and subtype APIs for the
  surrounding constructions.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap

universe uE uX uE' uX' uE'' uX'' uT

variable {E : Type uE} {X : Type uX}
variable [TopologicalSpace E] [TopologicalSpace X]

/-- The ordinary homotopy fiber of `f` over `b`: a point and a path from `b` to
its image, with the product/subspace topology. -/
def HomotopyFiber (f : C(E, X)) (b : X) :=
  {z : E × C(I, X) // z.2 0 = b ∧ z.2 1 = f z.1}

namespace HomotopyFiber

variable {f : C(E, X)} {b : X}

/-- The subspace topology inherited from the point and compact-open path product. -/
instance instTopologicalSpace : TopologicalSpace (HomotopyFiber f b) :=
  inferInstanceAs (TopologicalSpace {z : E × C(I, X) // z.2 0 = b ∧ z.2 1 = f z.1})

/-- The point retained in the homotopy fiber. -/
def point : C(HomotopyFiber f b, E) where
  toFun z := z.1.1
  continuous_toFun := continuous_fst.comp continuous_subtype_val

/-- The compact-open path retained in the homotopy fiber. -/
def path : C(HomotopyFiber f b, C(I, X)) where
  toFun z := z.1.2
  continuous_toFun := continuous_snd.comp continuous_subtype_val

/-- Construct a fiber point from a point, a path, and its endpoint equations. -/
def mk (e : E) (γ : C(I, X)) (h₀ : γ 0 = b) (h₁ : γ 1 = f e) :
    HomotopyFiber f b :=
  ⟨(e, γ), h₀, h₁⟩

@[simp]
theorem point_mk (e : E) (γ : C(I, X)) (h₀ : γ 0 = b) (h₁ : γ 1 = f e) :
    point (mk e γ h₀ h₁) = e :=
  rfl

@[simp]
theorem path_mk (e : E) (γ : C(I, X)) (h₀ : γ 0 = b) (h₁ : γ 1 = f e) :
    path (mk e γ h₀ h₁) = γ :=
  rfl

@[simp]
theorem mk_point_path (z : HomotopyFiber f b) :
    mk (point z) (path z) z.2.1 z.2.2 = z :=
  rfl

/-- A fiber point is determined by its point and compact-open path. -/
@[ext]
theorem ext {z w : HomotopyFiber f b}
    (he : point z = point w) (hγ : path z = path w) : z = w := by
  exact Subtype.ext (Prod.ext he hγ)

@[simp]
theorem path_zero (z : HomotopyFiber f b) : path z 0 = b :=
  z.2.1

@[simp]
theorem path_one (z : HomotopyFiber f b) : path z 1 = f (point z) :=
  z.2.2

/-- Evaluation of the retained path at a specified time. -/
def eval (t : I) : C(HomotopyFiber f b, X) where
  toFun z := path z t
  continuous_toFun := (continuous_eval_const t).comp path.continuous

@[simp]
theorem eval_apply (t : I) (z : HomotopyFiber f b) : eval t z = path z t :=
  rfl

theorem eval_zero (z : HomotopyFiber f b) : eval 0 z = b :=
  z.2.1

theorem eval_one (z : HomotopyFiber f b) : eval 1 z = f (point z) :=
  z.2.2

/-- The topology is the joint topology of the retained point and compact-open path. -/
theorem topology_eq :
    (inferInstance : TopologicalSpace (HomotopyFiber f b)) =
      TopologicalSpace.induced (point : HomotopyFiber f b → E) inferInstance ⊓
        TopologicalSpace.induced (path : HomotopyFiber f b → C(I, X)) inferInstance := by
  let val : HomotopyFiber f b → E × C(I, X) := Subtype.val
  calc
    (inferInstance : TopologicalSpace (HomotopyFiber f b)) =
        (TopologicalSpace.induced val
          (TopologicalSpace.induced (Prod.fst : E × C(I, X) → E) inferInstance ⊓
            TopologicalSpace.induced (Prod.snd : E × C(I, X) → C(I, X)) inferInstance) :
          TopologicalSpace (HomotopyFiber f b)) := rfl
    _ = (TopologicalSpace.induced (point : HomotopyFiber f b → E) inferInstance ⊓
        TopologicalSpace.induced (path : HomotopyFiber f b → C(I, X)) inferInstance :
          TopologicalSpace (HomotopyFiber f b)) := by
      rw [_root_.induced_inf]
      exact congrArg₂ (fun t₁ t₂ : TopologicalSpace (HomotopyFiber f b) => t₁ ⊓ t₂)
        (_root_.induced_compose (f := val) (g := (Prod.fst : E × C(I, X) → E)))
        (_root_.induced_compose (f := val) (g := (Prod.snd : E × C(I, X) → C(I, X))))

/-- A family of fiber points is continuous exactly when both coordinates are continuous. -/
theorem continuous_iff {T : Type uT} [TopologicalSpace T]
    {k : T → HomotopyFiber f b} :
    Continuous k ↔ Continuous (fun t => point (k t)) ∧
      Continuous (fun t => path (k t)) := by
  constructor
  · intro h
    exact ⟨point.continuous.comp h, path.continuous.comp h⟩
  · rintro ⟨he, hγ⟩
    exact continuous_induced_rng.2 (he.prodMk hγ)

/-- A specified source point over `b` gives the constant-path fiber point. An arbitrary
`b` alone does not specify a source point. -/
def const (e₀ : E) (h : f e₀ = b) : HomotopyFiber f b :=
  mk e₀ (ContinuousMap.const I b) rfl h.symm

@[simp]
theorem point_const (e₀ : E) (h : f e₀ = b) : point (const e₀ h) = e₀ :=
  rfl

@[simp]
theorem path_const (e₀ : E) (h : f e₀ = b) :
    path (const e₀ h) = ContinuousMap.const I b :=
  rfl

@[simp]
theorem eval_const (e₀ : E) (h : f e₀ = b) (t : I) : eval t (const e₀ h) = b :=
  rfl

section Map

variable {E' : Type uE'} {X' : Type uX'} {E'' : Type uE''} {X'' : Type uX''}
variable [TopologicalSpace E'] [TopologicalSpace X']
variable [TopologicalSpace E''] [TopologicalSpace X'']
variable {f' : C(E', X')} {f'' : C(E'', X'')} {b' : X'} {b'' : X''}

/-- Map homotopy fibers under a continuous commutative square preserving the target point.
The source point is mapped by `F`, and the path is postcomposed by `G`. -/
def map (F : C(E, E')) (G : C(X, X'))
    (w : ∀ e, f' (F e) = G (f e)) (hb : G b = b') :
    C(HomotopyFiber f b, HomotopyFiber f' b') where
  toFun z := mk (F (point z)) (G.comp (path z))
    ((congrArg G (path_zero z)).trans hb)
    ((congrArg G (path_one z)).trans (w (point z)).symm)
  continuous_toFun := by
    apply continuous_iff.2
    exact ⟨F.continuous.comp point.continuous,
      (continuous_postcomp G).comp path.continuous⟩

@[simp]
theorem point_map (F : C(E, E')) (G : C(X, X'))
    (w : ∀ e, f' (F e) = G (f e)) (hb : G b = b') (z : HomotopyFiber f b) :
    point (map F G w hb z) = F (point z) :=
  rfl

@[simp]
theorem path_map (F : C(E, E')) (G : C(X, X'))
    (w : ∀ e, f' (F e) = G (f e)) (hb : G b = b') (z : HomotopyFiber f b) :
    path (map F G w hb z) = G.comp (path z) :=
  rfl

@[simp]
theorem eval_map (F : C(E, E')) (G : C(X, X'))
    (w : ∀ e, f' (F e) = G (f e)) (hb : G b = b')
    (z : HomotopyFiber f b) (t : I) :
    eval t (map F G w hb z) = G (eval t z) :=
  rfl

/-- The identity square acts as the identity. -/
@[simp]
theorem map_id :
    map (f := f) (f' := f) (ContinuousMap.id E) (ContinuousMap.id X)
        (fun _ => rfl) (b := b) (b' := b) rfl =
      ContinuousMap.id (HomotopyFiber f b) := by
  apply ContinuousMap.ext
  intro z
  apply ext
  · exact (point_map (f := f) (f' := f) (b := b) (b' := b)
      (ContinuousMap.id E) (ContinuousMap.id X) (fun _ => rfl) rfl z).trans
      (ContinuousMap.id_apply (point z))
  · exact (path_map (f := f) (f' := f) (b := b) (b' := b)
      (ContinuousMap.id E) (ContinuousMap.id X) (fun _ => rfl) rfl z).trans
      (ContinuousMap.id_comp (path z))

/-- Maps of homotopy fibers respect composition of continuous commutative squares. -/
theorem map_comp (F : C(E, E')) (G : C(X, X'))
    (F' : C(E', E'')) (G' : C(X', X''))
    (w : ∀ e, f' (F e) = G (f e)) (w' : ∀ e, f'' (F' e) = G' (f' e))
    (hb : G b = b') (hb' : G' b' = b'') :
    (map F' G' w' hb').comp (map F G w hb) =
      map (F'.comp F) (G'.comp G)
        (fun e => (w' (F e)).trans (congrArg G' (w e)))
        ((congrArg G' hb).trans hb') := by
  apply ContinuousMap.ext
  intro z
  apply ext
  · calc
      point (map F' G' w' hb' (map F G w hb z)) = F' (point (map F G w hb z)) :=
        point_map F' G' w' hb' (map F G w hb z)
      _ = F' (F (point z)) := congrArg F' (point_map F G w hb z)
      _ = (F'.comp F) (point z) := (ContinuousMap.comp_apply F' F (point z)).symm
      _ = point (map (F'.comp F) (G'.comp G)
          (fun e => (w' (F e)).trans (congrArg G' (w e)))
          ((congrArg G' hb).trans hb') z) :=
        (point_map (F'.comp F) (G'.comp G)
          (fun e => (w' (F e)).trans (congrArg G' (w e)))
          ((congrArg G' hb).trans hb') z).symm
  · calc
      path (map F' G' w' hb' (map F G w hb z)) = G'.comp (path (map F G w hb z)) :=
        path_map F' G' w' hb' (map F G w hb z)
      _ = G'.comp (G.comp (path z)) :=
        congrArg (fun η : C(I, X') => G'.comp η) (path_map F G w hb z)
      _ = (G'.comp G).comp (path z) :=
        (ContinuousMap.comp_assoc G' G (path z)).symm
      _ = path (map (F'.comp F) (G'.comp G)
          (fun e => (w' (F e)).trans (congrArg G' (w e)))
          ((congrArg G' hb).trans hb') z) :=
        (path_map (F'.comp F) (G'.comp G)
          (fun e => (w' (F e)).trans (congrArg G' (w e)))
          ((congrArg G' hb).trans hb') z).symm

/-- A square preserves the constant point associated to a specified source point. -/
@[simp]
theorem map_const (F : C(E, E')) (G : C(X, X'))
    (w : ∀ e, f' (F e) = G (f e)) (hb : G b = b') (e₀ : E) (h : f e₀ = b) :
    map F G w hb (const e₀ h) =
      const (F e₀) ((w e₀).trans ((congrArg G h).trans hb)) := by
  apply ext
  · simp only [point_map, point_const]
  · simp only [path_map, path_const, ContinuousMap.comp_const, hb]

/-- A commutative square induces the corresponding map between the ranges. -/
theorem mapsTo_range (F : C(E, E')) (G : C(X, X'))
    (w : ∀ e, f' (F e) = G (f e)) :
    Set.MapsTo G (Set.range f) (Set.range f') := by
  rintro _ ⟨e, rfl⟩
  exact ⟨F e, w e⟩

end Map

/-- Terminal evaluation on the compact-open subspace of paths starting at `b`. -/
def terminalEvaluation (b : X) : C({γ : C(I, X) // γ 0 = b}, X) where
  toFun γ := γ.1 1
  continuous_toFun := (continuous_eval_const 1).comp continuous_subtype_val

@[simp]
theorem terminalEvaluation_apply (b : X) (γ : {γ : C(I, X) // γ 0 = b}) :
    terminalEvaluation b γ = γ.1 1 :=
  rfl

/-- The ordinary fiber is the path-factor-first pullback of terminal evaluation and `f`.
The homeomorphism only regroups the fixed-start proof and swaps the product factors. -/
def pullbackHomeomorph (f : C(E, X)) (b : X) :
    HomotopyFiber f b ≃ₜ
      {z : {γ : C(I, X) // γ 0 = b} × E // terminalEvaluation b z.1 = f z.2} :=
  let regroup : HomotopyFiber f b ≃ₜ
      {z : E × {γ : C(I, X) // γ 0 = b} // f z.1 = z.2.1 1} :=
    { toFun := fun z => ⟨(point z, ⟨path z, path_zero z⟩), (path_one z).symm⟩
      invFun := fun z => mk z.1.1 z.1.2.1 z.1.2.2 z.2.symm
      left_inv := by
        intro z
        exact mk_point_path z
      right_inv := by
        intro z
        apply Subtype.ext
        rfl
      continuous_toFun := by
        exact (point.continuous.prodMk
          (path.continuous.subtype_mk (fun z => path_zero z))).subtype_mk _
      continuous_invFun := by
        exact (continuous_subtype_val.fst.prodMk
          continuous_subtype_val.snd.subtype_val).subtype_mk _ }
  regroup.trans
    ((Homeomorph.prodComm E {γ : C(I, X) // γ 0 = b}).subtype
      (fun _ => eq_comm))

@[simp]
theorem pullbackHomeomorph_path (z : HomotopyFiber f b) :
    (DFunLike.coe (F := HomotopyFiber f b ≃ₜ
      {z : {γ : C(I, X) // γ 0 = b} × E // z.1.1 1 = f z.2})
      (pullbackHomeomorph f b) z).1.1.1 = path z :=
  rfl

@[simp]
theorem pullbackHomeomorph_point (z : HomotopyFiber f b) :
    (DFunLike.coe (F := HomotopyFiber f b ≃ₜ
      {z : {γ : C(I, X) // γ 0 = b} × E // z.1.1 1 = f z.2})
      (pullbackHomeomorph f b) z).1.2 = point z :=
  rfl

@[simp]
theorem pullbackHomeomorph_symm_path
    (z : {z : {γ : C(I, X) // γ 0 = b} × E // z.1.1 1 = f z.2}) :
    path (DFunLike.coe
      (F := {z : {γ : C(I, X) // γ 0 = b} × E // z.1.1 1 = f z.2} ≃ₜ
        HomotopyFiber f b)
      (Homeomorph.symm
        (Y := {z : {γ : C(I, X) // γ 0 = b} × E // z.1.1 1 = f z.2})
        (pullbackHomeomorph f b)) z) = z.1.1.1 :=
  rfl

@[simp]
theorem pullbackHomeomorph_symm_point
    (z : {z : {γ : C(I, X) // γ 0 = b} × E // z.1.1 1 = f z.2}) :
    point (DFunLike.coe
      (F := {z : {γ : C(I, X) // γ 0 = b} × E // z.1.1 1 = f z.2} ≃ₜ
        HomotopyFiber f b)
      (Homeomorph.symm
        (Y := {z : {γ : C(I, X) // γ 0 = b} × E // z.1.1 1 = f z.2})
        (pullbackHomeomorph f b)) z) = z.1.2 :=
  rfl

/-- For an embedding, the ordinary homotopy fiber is homeomorphic to compact-open paths
starting at `b` and ending in its range. The inverse is the existing generic pullback
inverse, not a separately chosen continuous section. This is the ordinary-space
embedding version of the endpoint-path identification motivating May, Chapter 9, §1. -/
noncomputable def endpointHomeomorph (hf : Topology.IsEmbedding f) (b : X) :
    HomotopyFiber f b ≃ₜ RelativePathSpace b (Set.range f) :=
  (pullbackHomeomorph f b).trans
    ((TopCat.pullbackHomeoPreimage (terminalEvaluation b) (terminalEvaluation b).continuous
      f hf).trans
      (Homeomorph.subtypeSubtypeEquivSubtypeInter
        (fun γ : C(I, X) => γ 0 = b) (fun γ => γ 1 ∈ Set.range f)))

@[simp]
theorem endpointHomeomorph_path (hf : Topology.IsEmbedding f) (z : HomotopyFiber f b) :
    RelativePathSpace.path (endpointHomeomorph hf b z) = path z :=
  rfl

/-- Forward evaluation keeps the path with its original direction. -/
@[simp]
theorem endpointHomeomorph_eval (hf : Topology.IsEmbedding f)
    (z : HomotopyFiber f b) (t : I) :
    RelativePathSpace.eval t (endpointHomeomorph hf b z) = eval t z :=
  rfl

theorem endpointHomeomorph_endpoint_coe (hf : Topology.IsEmbedding f)
    (z : HomotopyFiber f b) :
    (RelativePathSpace.endpoint (endpointHomeomorph hf b z) : X) = f (point z) := by
  rw [RelativePathSpace.endpoint_coe, endpointHomeomorph_path, path_one]

@[simp]
theorem endpointHomeomorph_symm_path (hf : Topology.IsEmbedding f)
    (γ : RelativePathSpace b (Set.range f)) :
    path ((endpointHomeomorph hf b).symm γ) = RelativePathSpace.path γ :=
  rfl

/-- The inverse also keeps the entire parametrized path. -/
@[simp]
theorem endpointHomeomorph_symm_eval (hf : Topology.IsEmbedding f)
    (γ : RelativePathSpace b (Set.range f)) (t : I) :
    eval t ((endpointHomeomorph hf b).symm γ) = RelativePathSpace.eval t γ :=
  rfl

/-- The recovered source point is the inverse of the embedding onto its range,
applied to the terminal point. -/
theorem endpointHomeomorph_symm_point (hf : Topology.IsEmbedding f)
    (γ : RelativePathSpace b (Set.range f)) :
    point ((endpointHomeomorph hf b).symm γ) =
      hf.toHomeomorph.symm (RelativePathSpace.endpoint γ) := by
  apply hf.toHomeomorph.injective
  apply Subtype.ext
  simpa only [Topology.IsEmbedding.toHomeomorph_apply_coe, Homeomorph.apply_symm_apply,
    RelativePathSpace.endpoint_coe, endpointHomeomorph_symm_path] using
    (path_one ((endpointHomeomorph hf b).symm γ)).symm

@[simp]
theorem endpointHomeomorph_symm_point_image (hf : Topology.IsEmbedding f)
    (γ : RelativePathSpace b (Set.range f)) :
    f (point ((endpointHomeomorph hf b).symm γ)) = RelativePathSpace.path γ 1 := by
  rw [← path_one, endpointHomeomorph_symm_path]

/-- The specified constant fiber point is sent to the exact constant path. -/
@[simp]
theorem endpointHomeomorph_const (hf : Topology.IsEmbedding f)
    (e₀ : E) (h : f e₀ = b) :
    endpointHomeomorph hf b (const e₀ h) =
      RelativePathSpace.const (b := b) (A := Set.range f)
        (show b ∈ Set.range f from ⟨e₀, h⟩) := by
  apply RelativePathSpace.ext
  simp only [endpointHomeomorph_path, path_const, RelativePathSpace.path_const]

theorem endpointHomeomorph_symm_const (hf : Topology.IsEmbedding f)
    (e₀ : E) (h : f e₀ = b) :
    (endpointHomeomorph hf b).symm (RelativePathSpace.const ⟨e₀, h⟩) = const e₀ h := by
  exact (endpointHomeomorph hf b).symm_apply_eq.mpr
    (endpointHomeomorph_const hf e₀ h).symm

/-- The embedding comparison is natural under continuous squares. Only the two maps
whose fibers are compared are embeddings; the maps `F` and `G` are arbitrary continuous
maps subject to the square and starting-point equations. -/
theorem endpointHomeomorph_naturality
    {E' : Type uE'} {X' : Type uX'} [TopologicalSpace E'] [TopologicalSpace X']
    {f' : C(E', X')} {b' : X'}
    (hf : Topology.IsEmbedding f) (hf' : Topology.IsEmbedding f')
    (F : C(E, E')) (G : C(X, X'))
    (w : ∀ e, f' (F e) = G (f e)) (hb : G b = b') (z : HomotopyFiber f b) :
    endpointHomeomorph hf' b' (map F G w hb z) =
      RelativePathSpace.map G (mapsTo_range F G w) hb (endpointHomeomorph hf b z) := by
  apply RelativePathSpace.ext
  simp only [endpointHomeomorph_path, path_map, RelativePathSpace.path_map]

section Subspace

variable {A : Set X}

/-- The ordinary fiber of the original inclusion of `A` at an arbitrary `b : X` is
the space of paths starting at `b` and ending in exactly `A`. The point `b` need not
belong to `A`; a specified `a ∈ A` gives the constant point when `b = a`.
This specializes the embedding comparison using `IsEmbedding.subtypeVal` and
`Subtype.range_coe`; it follows the endpoint-path construction in May, Chapter 9,
§1, p. 65, with ordinary topologies. -/
noncomputable def subtypeHomeomorph (b : X) :
    HomotopyFiber (ContinuousMap.subtypeVal A) b ≃ₜ RelativePathSpace b A :=
  (endpointHomeomorph
    (Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding (ContinuousMap.subtypeVal A))
    b).trans
    ((Homeomorph.refl C(I, X)).subtype (fun γ => by
      rw [show Set.range (ContinuousMap.subtypeVal A) = A from Subtype.range_coe]
      exact Iff.rfl))

@[simp]
theorem subtypeHomeomorph_path (b : X)
    (z : HomotopyFiber (ContinuousMap.subtypeVal A) b) :
    RelativePathSpace.path (subtypeHomeomorph (A := A) b z) = path z :=
  rfl

@[simp]
theorem subtypeHomeomorph_eval (b : X)
    (z : HomotopyFiber (ContinuousMap.subtypeVal A) b) (t : I) :
    RelativePathSpace.eval t (subtypeHomeomorph (A := A) b z) = eval t z :=
  rfl

/-- The endpoint in `A` agrees with the original fiber's source point in `A`. -/
@[simp]
theorem subtypeHomeomorph_endpoint (b : X)
    (z : HomotopyFiber (ContinuousMap.subtypeVal A) b) :
    RelativePathSpace.endpoint (subtypeHomeomorph (A := A) b z) = point z := by
  apply Subtype.ext
  simpa only [RelativePathSpace.endpoint_coe, subtypeHomeomorph_path,
    ContinuousMap.subtypeVal_apply] using path_one z

@[simp]
theorem subtypeHomeomorph_symm_path (b : X) (γ : RelativePathSpace b A) :
    path ((subtypeHomeomorph (A := A) b).symm γ) = RelativePathSpace.path γ :=
  rfl

@[simp]
theorem subtypeHomeomorph_symm_eval (b : X) (γ : RelativePathSpace b A) (t : I) :
    eval t ((subtypeHomeomorph (A := A) b).symm γ) = RelativePathSpace.eval t γ :=
  rfl

/-- The inverse source point is exactly `γ(1)` as a point of the original subspace. -/
@[simp]
theorem subtypeHomeomorph_symm_point (b : X) (γ : RelativePathSpace b A) :
    point ((subtypeHomeomorph (A := A) b).symm γ) = RelativePathSpace.endpoint γ := by
  simpa only [Homeomorph.apply_symm_apply] using
    (subtypeHomeomorph_endpoint b ((subtypeHomeomorph (A := A) b).symm γ)).symm

/-- Exact preservation of the inclusion's specified constant point. -/
@[simp]
theorem subtypeHomeomorph_const (a : A) :
    subtypeHomeomorph (A := A) (a : X) (const a rfl) = RelativePathSpace.const a.2 := by
  apply RelativePathSpace.ext
  exact (subtypeHomeomorph_path (a : X) (const a rfl)).trans
    ((path_const (f := ContinuousMap.subtypeVal A) (b := (a : X)) a rfl).trans
      (RelativePathSpace.path_const a.2).symm)

@[simp]
theorem subtypeHomeomorph_symm_const (a : A) :
    (subtypeHomeomorph (A := A) (a : X)).symm (RelativePathSpace.const a.2) =
      const a rfl := by
  apply ((subtypeHomeomorph (A := A) (a : X)).symm_apply_eq).2
  exact (subtypeHomeomorph_const a).symm

/-- Naturality for the original inclusions under a continuous map of pairs, at
arbitrary starting points `b : X` and `b' : X'` with `G b = b'`.
The source-coordinate map is the restriction of `G` to `A`, not an unrelated
model of the subspace inclusion. Neither starting point must lie in its subspace. -/
theorem subtypeHomeomorph_naturality
    {X' : Type uX'} [TopologicalSpace X'] {B : Set X'}
    (G : C(X, X')) (hA : Set.MapsTo G A B) (b : X) (b' : X') (hb : G b = b')
    (z : HomotopyFiber (ContinuousMap.subtypeVal A) b) :
    let F : C(A, B) :=
      ⟨fun x => ⟨G x, hA x.2⟩,
        (G.continuous.comp continuous_subtype_val).subtype_mk (fun x => hA x.2)⟩
    subtypeHomeomorph (A := B) b' (map F G (fun _ => rfl) hb z) =
      RelativePathSpace.map G hA hb (subtypeHomeomorph (A := A) b z) := by
  intro F
  apply RelativePathSpace.ext
  calc
    RelativePathSpace.path
        (subtypeHomeomorph (A := B) b' (map F G (fun _ => rfl) hb z)) =
        path (map F G (fun _ => rfl) hb z) :=
      subtypeHomeomorph_path b' _
    _ = G.comp (path z) :=
      path_map (f := ContinuousMap.subtypeVal A) (f' := ContinuousMap.subtypeVal B)
        (b := b) (b' := b') F G (fun _ => rfl) hb z
    _ = G.comp (RelativePathSpace.path (subtypeHomeomorph (A := A) b z)) :=
      congrArg (fun γ : C(I, X) => G.comp γ) (subtypeHomeomorph_path b z).symm
    _ = RelativePathSpace.path
        (RelativePathSpace.map G hA hb (subtypeHomeomorph (A := A) b z)) :=
      (RelativePathSpace.path_map G hA hb (subtypeHomeomorph (A := A) b z)).symm

end Subspace

end HomotopyFiber
end ContinuousMap
