/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.UnitInterval

/-!
# Paths from a point to a subspace

`ContinuousMap.RelativePathSpace b A` consists of compact-open paths starting at
`b` and ending anywhere in `A`, with the subspace topology from `C(I, X)`.
The path is not required to stay in `A`, nor to end at `b`. The point `b` is
arbitrary; a constant path belongs to this space precisely when `b ∈ A`.

## Implementation notes

These are ordinary compact-open and subspace topologies. The endpoint-path
construction in May's *A Concise Course in Algebraic Topology*, Chapter 9,
§1, p. 65 motivates this space. Its standing weak-Hausdorff/k-space conventions
are not identified with these ordinary topologies here. Compact-open evaluation
and postcomposition use Mathlib's APIs.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap

universe u v w z

variable {X : Type u} {Y : Type v} {Z : Type w} {T : Type z}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable [TopologicalSpace T]

/-- Compact-open paths starting at `b` and ending in `A`, with their subspace topology. -/
def RelativePathSpace (b : X) (A : Set X) :=
  {γ : C(I, X) // γ 0 = b ∧ γ 1 ∈ A}

namespace RelativePathSpace

variable {b : X} {A : Set X}

/-- The subspace topology inherited from compact-open paths. -/
instance instTopologicalSpace : TopologicalSpace (RelativePathSpace b A) :=
  inferInstanceAs (TopologicalSpace {γ : C(I, X) // γ 0 = b ∧ γ 1 ∈ A})

/-- The underlying compact-open path. -/
def path : C(RelativePathSpace b A, C(I, X)) :=
  ContinuousMap.subtypeVal _

/-- Construct an endpoint-constrained path from its two endpoint properties. -/
def mk (γ : C(I, X)) (h₀ : γ 0 = b) (h₁ : γ 1 ∈ A) : RelativePathSpace b A :=
  ⟨γ, h₀, h₁⟩

@[simp]
theorem path_mk (γ : C(I, X)) (h₀ : γ 0 = b) (h₁ : γ 1 ∈ A) :
    path (mk γ h₀ h₁) = γ :=
  rfl

@[simp]
theorem mk_path (γ : RelativePathSpace b A) : mk (path γ) γ.2.1 γ.2.2 = γ :=
  rfl

/-- Endpoint-constrained paths are determined by their compact-open paths. -/
@[ext]
theorem ext {γ δ : RelativePathSpace b A} (h : path γ = path δ) : γ = δ := by
  exact Subtype.ext h

@[simp]
theorem path_zero (γ : RelativePathSpace b A) : path γ 0 = b :=
  γ.2.1

@[simp]
theorem path_one_mem (γ : RelativePathSpace b A) : path γ 1 ∈ A :=
  γ.2.2

/-- Evaluation at a specified time. -/
def eval (t : I) : C(RelativePathSpace b A, X) where
  toFun γ := path γ t
  continuous_toFun := (continuous_eval_const t).comp path.continuous

@[simp]
theorem eval_apply (t : I) (γ : RelativePathSpace b A) : eval t γ = path γ t :=
  rfl

theorem eval_zero (γ : RelativePathSpace b A) : eval 0 γ = b :=
  γ.2.1

/-- The terminal point as a point of the original subspace `A`. -/
def endpoint : C(RelativePathSpace b A, A) where
  toFun γ := ⟨path γ 1, path_one_mem γ⟩
  continuous_toFun := by
    exact (eval (b := b) (A := A) 1).continuous.subtype_mk (fun γ => path_one_mem γ)

@[simp]
theorem endpoint_coe (γ : RelativePathSpace b A) : (endpoint γ : X) = path γ 1 :=
  rfl

/-- The topology is induced by the underlying compact-open path. -/
theorem isEmbedding_path :
    Topology.IsEmbedding (path : RelativePathSpace b A → C(I, X)) := by
  exact Topology.IsEmbedding.subtypeVal

/-- Continuity into the endpoint-path space is continuity of the underlying paths. -/
theorem continuous_iff {k : T → RelativePathSpace b A} :
    Continuous k ↔ Continuous (fun t => path (k t)) := by
  exact isEmbedding_path.continuous_iff

/-- The constant path at `b`, when `b` belongs to the endpoint subspace. -/
def const (hb : b ∈ A) : RelativePathSpace b A :=
  mk (ContinuousMap.const I b) rfl hb

@[simp]
theorem path_const (hb : b ∈ A) : path (const hb) = ContinuousMap.const I b :=
  rfl

@[simp]
theorem eval_const (hb : b ∈ A) (t : I) : eval t (const hb) = b :=
  rfl

@[simp]
theorem endpoint_const (hb : b ∈ A) : endpoint (const hb) = ⟨b, hb⟩ :=
  rfl

section Map

variable {b' : Y} {b'' : Z} {B : Set Y} {D : Set Z}

/-- Postcompose an endpoint-constrained path by a continuous map of pairs preserving
its specified starting point. -/
def map (G : C(X, Y)) (hA : Set.MapsTo G A B) (hb : G b = b') :
    C(RelativePathSpace b A, RelativePathSpace b' B) where
  toFun γ := mk (G.comp (path γ)) ((congrArg G (path_zero γ)).trans hb)
    (hA (path_one_mem γ))
  continuous_toFun := by
    apply continuous_iff.mpr
    exact (ContinuousMap.continuous_postcomp G).comp path.continuous

@[simp]
theorem path_map (G : C(X, Y)) (hA : Set.MapsTo G A B) (hb : G b = b')
    (γ : RelativePathSpace b A) :
    path (map G hA hb γ) = G.comp (path γ) :=
  rfl

@[simp]
theorem eval_map (G : C(X, Y)) (hA : Set.MapsTo G A B) (hb : G b = b')
    (γ : RelativePathSpace b A) (t : I) :
    eval t (map G hA hb γ) = G (eval t γ) :=
  rfl

@[simp]
theorem endpoint_map_coe (G : C(X, Y)) (hA : Set.MapsTo G A B) (hb : G b = b')
    (γ : RelativePathSpace b A) :
    (endpoint (map G hA hb γ) : Y) = G (endpoint γ) :=
  rfl

/-- Postcomposition by the identity is the identity. -/
@[simp]
theorem map_id :
    map (ContinuousMap.id X) (A := A) (B := A) (fun _ h => h)
        (b := b) (b' := b) rfl =
      ContinuousMap.id (RelativePathSpace b A) := by
  apply ContinuousMap.ext
  intro γ
  apply ext
  exact (path_map (b := b) (b' := b) (A := A) (B := A)
    (ContinuousMap.id X) (fun _ h => h) rfl γ).trans
    (ContinuousMap.id_comp (path γ))

/-- Postcomposition respects composition of maps of pairs. -/
theorem map_comp (G : C(X, Y)) (H : C(Y, Z))
    (hA : Set.MapsTo G A B) (hB : Set.MapsTo H B D)
    (hb : G b = b') (hb' : H b' = b'') :
    (map H hB hb').comp (map G hA hb) =
      map (H.comp G) (fun _ hx => hB (hA hx)) ((congrArg H hb).trans hb') := by
  apply ContinuousMap.ext
  intro γ
  apply ext
  calc
    path (map H hB hb' (map G hA hb γ)) = H.comp (path (map G hA hb γ)) :=
      path_map H hB hb' (map G hA hb γ)
    _ = H.comp (G.comp (path γ)) :=
      congrArg (fun η : C(I, Y) => H.comp η) (path_map G hA hb γ)
    _ = (H.comp G).comp (path γ) :=
      (ContinuousMap.comp_assoc H G (path γ)).symm
    _ = path (map (H.comp G) (fun _ hx => hB (hA hx))
        ((congrArg H hb).trans hb') γ) :=
      (path_map (H.comp G) (fun _ hx => hB (hA hx))
        ((congrArg H hb).trans hb') γ).symm

/-- A map of pairs carries the specified constant path to the specified constant path. -/
@[simp]
theorem map_const (G : C(X, Y)) (hA : Set.MapsTo G A B) (hb : G b = b')
    (hbA : b ∈ A) :
    map G hA hb (const hbA) = const (hb ▸ hA hbA) := by
  apply ext
  simp only [path_map, path_const, ContinuousMap.comp_const, hb]

end Map

end RelativePathSpace
end ContinuousMap
