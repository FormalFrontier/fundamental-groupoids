/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Cube
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.LoopSpace
public import FundamentalGroupoids.Topology.Homotopy.Relative
public import FundamentalGroupoids.Topology.Piecewise

/-!
# Generalized loops with infinitely many coordinates

For an infinite index type, the generalized loop space `GenLoop N X x` is
contractible in its subtype topology from the compact-open topology on
continuous maps. Every such loop is also homotopic relative to the coordinate-face
boundary to the constant loop. Consequently, the corresponding homotopy group is
a subsingleton, without separation assumptions on the target.

The boundary is dense, so continuity puts every value of a generalized loop in
the closure of the singleton containing its basepoint. The resulting pointwise
specializations show that the constant loop specializes to every loop, giving
contractibility of the loop space. The canonical comparison with paths and path
components then gives relative nullhomotopies and collapse of the homotopy
quotient. An individual loop need not be pointwise constant.

Given a path between basepoints, any two generalized loops admit a homotopy
whose boundary follows that path. Away from the endpoint times, the homotopy is
constant on each cube slice, with value the prescribed path at that time.
The generalized-loop spaces at any two basepoints are homotopy equivalent via
constant maps, even when there is no path between the basepoints.

## References

* Mathlib's `Mathlib.Topology.Homotopy.HomotopyGroup` supplies generalized loops,
  their relative homotopy relation and its quotient.
* Mathlib's `Set.MapsTo.closure` and `specializes_iff_mem_closure` relate
  continuity and closure to specialization.
* `IsClosed.continuous_piecewise_of_specializes_on` pastes the endpoint time
  slices using pointwise specialization.
-/

public section

universe u v

open scoped unitInterval Topology ContinuousMap

namespace GenLoop

variable {N : Type u} [Infinite N] {X : Type v} [TopologicalSpace X] {x : X}

/-- Every value of a generalized loop with infinitely many coordinates lies in
the closure of the singleton containing its basepoint. -/
theorem mem_closure_singleton_of_infinite (γ : GenLoop N X x) (s : I^N) :
    γ s ∈ closure ({x} : Set X) := by
  have hboundary : Set.MapsTo γ (Cube.boundary N) ({x} : Set X) := by
    intro s hs
    exact Set.mem_singleton_iff.mpr (GenLoop.boundary γ s hs)
  exact hboundary.closure γ.1.continuous (Cube.dense_boundary N s)

/-- The constant loop specializes to every generalized loop with infinitely many
coordinates, in the subtype topology on the space of continuous maps. -/
theorem const_specializes_of_infinite (γ : GenLoop N X x) :
    (GenLoop.const : GenLoop N X x) ⤳ γ := by
  apply (subtype_specializes_iff _ _).mpr
  apply ContinuousMap.specializes_coe.mp
  exact specializes_pi.mpr fun s ↦
    specializes_iff_mem_closure.mpr (GenLoop.mem_closure_singleton_of_infinite γ s)

/-- The generalized loop space with infinitely many coordinates is contractible
in its subtype topology from the compact-open topology on continuous maps,
without separation assumptions on the target. -/
theorem contractibleSpace_of_infinite (N : Type u) [Infinite N] (X : Type v)
    [TopologicalSpace X] (x : X) : ContractibleSpace (GenLoop N X x) :=
  contractibleSpace_of_specializes (GenLoop.const : GenLoop N X x)
    (fun γ ↦ GenLoop.const_specializes_of_infinite γ)

/-- A generalized loop with infinitely many coordinates is homotopic relative to
its boundary to the constant loop, without separation assumptions on the target. -/
theorem homotopic_const_of_infinite (γ : GenLoop N X x) :
    GenLoop.Homotopic γ (GenLoop.const : GenLoop N X x) := by
  let : ContractibleSpace (GenLoop N X x) :=
    GenLoop.contractibleSpace_of_infinite N X x
  exact (GenLoop.homotopic_iff_joined γ GenLoop.const).mpr
    (PathConnectedSpace.joined γ GenLoop.const)

/-- The generalized-loop spaces at any two basepoints are homotopy equivalent
when the coordinate type is infinite. Both maps are constant at the respective
constant loops; no path between the basepoints is required. -/
noncomputable def homotopyEquivOfInfinite (N : Type u) [Infinite N] (X : Type v)
    [TopologicalSpace X] (x y : X) : GenLoop N X x ≃ₕ GenLoop N X y where
  toFun := ContinuousMap.const _ (GenLoop.const : GenLoop N X y)
  invFun := ContinuousMap.const _ (GenLoop.const : GenLoop N X x)
  left_inv := ⟨(ContinuousMap.HomotopyWith.ofSpecializes
    (f₀ := ContinuousMap.const _ (GenLoop.const : GenLoop N X x))
    (f₁ := ContinuousMap.id (GenLoop N X x)) (P := fun _ ↦ True)
    (fun p ↦ const_specializes_of_infinite p) trivial trivial).toHomotopy⟩
  right_inv := ⟨(ContinuousMap.HomotopyWith.ofSpecializes
    (f₀ := ContinuousMap.const _ (GenLoop.const : GenLoop N X y))
    (f₁ := ContinuousMap.id (GenLoop N X y)) (P := fun _ ↦ True)
    (fun q ↦ const_specializes_of_infinite q) trivial trivial).toHomotopy⟩

/-- The forward map sends every loop to the constant loop at the new basepoint. -/
@[simp]
theorem homotopyEquivOfInfinite_apply (x y : X) (p : GenLoop N X x) :
    homotopyEquivOfInfinite N X x y p = (GenLoop.const : GenLoop N X y) := by
  unfold homotopyEquivOfInfinite
  rfl

/-- The inverse map sends every loop to the constant loop at the old basepoint. -/
@[simp]
theorem homotopyEquivOfInfinite_symm_apply (x y : X) (q : GenLoop N X y) :
    (homotopyEquivOfInfinite N X x y).symm q = (GenLoop.const : GenLoop N X x) := by
  unfold homotopyEquivOfInfinite
  rfl

variable {y : X}

omit [Infinite N] in
private theorem continuous_time_patch (a : I) {f g : (I × (N → I)) → X}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ r, r.1 = a → g r ⤳ f r) :
    Continuous (fun r ↦ if r.1 = a then f r else g r) := by
  classical
  have hpiecewise :
      (fun r : I × I^N ↦ if r.1 = a then f r else g r) =
        {r : I × I^N | r.1 = a}.piecewise f g := by
    funext r
    by_cases hr : r.1 = a
    · rw [ite_eq_left hr,
        Set.piecewise_eq_of_mem {r : I × I^N | r.1 = a} f g hr]
    · rw [ite_eq_right hr,
        Set.piecewise_eq_of_notMem {r : I × I^N | r.1 = a} f g hr]
  rw [hpiecewise]
  exact IsClosed.continuous_piecewise_of_specializes_on
    (s := {r : I × I^N | r.1 = a})
    (isClosed_singleton.preimage continuous_fst) hf hg h

/-- For infinitely many coordinates, a path between basepoints gives a homotopy
between any two generalized loops whose boundary follows the prescribed path.
At every time other than `0` and `1`, the entire cube is sent to the path value. -/
noncomputable def homotopyAlongOfInfinite (γ : Path x y)
    (p : GenLoop N X x) (q : GenLoop N X y) :
    ContinuousMap.Homotopy p.val q.val := by
  classical
  refine
    { toFun := fun r ↦ if r.1 = 0 then p r.2 else if r.1 = 1 then q r.2 else γ r.1
      continuous_toFun := ?_
      map_zero_left := fun _ ↦ by simp
      map_one_left := fun _ ↦ by simp }
  have hγ : Continuous (fun r : I × I^N ↦ γ r.1) :=
    γ.continuous.comp continuous_fst
  have hq : Continuous (fun r : I × I^N ↦ if r.1 = 1 then q r.2 else γ r.1) := by
    apply continuous_time_patch 1 (q.val.continuous.comp continuous_snd) hγ
    intro r hr
    simpa only [Function.comp_apply, GenLoop.coe_coe, hr, Path.target] using
      specializes_iff_mem_closure.mpr (mem_closure_singleton_of_infinite q r.2)
  apply continuous_time_patch 0 (p.val.continuous.comp continuous_snd) hq
  intro r hr
  simpa [hr] using
    specializes_iff_mem_closure.mpr (mem_closure_singleton_of_infinite p r.2)

/-- The homotopy uses the given loops at the endpoint times and the prescribed
path value at all other times. -/
@[simp]
theorem homotopyAlongOfInfinite_apply (γ : Path x y)
    (p : GenLoop N X x) (q : GenLoop N X y) (r : I × I^N) :
    homotopyAlongOfInfinite γ p q r =
      if r.1 = 0 then p r.2 else if r.1 = 1 then q r.2 else γ r.1 := by
  classical
  rfl

/-- Away from the endpoint times, the homotopy is constant on each cube slice. -/
theorem homotopyAlongOfInfinite_apply_of_ne (γ : Path x y)
    (p : GenLoop N X x) (q : GenLoop N X y) {t : I}
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (z : I^N) :
    homotopyAlongOfInfinite γ p q (t, z) = γ t := by
  simp [ht₀, ht₁]

/-- The boundary of the homotopy follows the given path at every time. -/
theorem homotopyAlongOfInfinite_boundary (γ : Path x y)
    (p : GenLoop N X x) (q : GenLoop N X y) (t : I)
    {z : I^N} (hz : z ∈ Cube.boundary N) :
    homotopyAlongOfInfinite γ p q (t, z) = γ t := by
  by_cases ht₀ : t = 0
  · subst t
    rw [ContinuousMap.Homotopy.apply_zero, Path.source]
    exact (congrFun (GenLoop.coe_coe p) z).trans (GenLoop.boundary p z hz)
  by_cases ht₁ : t = 1
  · subst t
    rw [ContinuousMap.Homotopy.apply_one, Path.target]
    exact (congrFun (GenLoop.coe_coe q) z).trans (GenLoop.boundary q z hz)
  exact homotopyAlongOfInfinite_apply_of_ne γ p q ht₀ ht₁ z

/-- When the final loop is constant, every nonzero time slice has the prescribed
path value, including the final time. -/
theorem homotopyAlongOfInfinite_const_apply_of_ne_zero (γ : Path x y)
    (p : GenLoop N X x) {t : I} (ht : t ≠ 0) (z : I^N) :
    homotopyAlongOfInfinite γ p (GenLoop.const : GenLoop N X y) (t, z) = γ t := by
  by_cases ht₁ : t = 1
  · subst t
    rw [ContinuousMap.Homotopy.apply_one, Path.target]
    exact GenLoop.const_apply (N := N) (x := y) (t := z)
  exact homotopyAlongOfInfinite_apply_of_ne γ p GenLoop.const ht ht₁ z

end GenLoop

namespace HomotopyGroup

/-- The homotopy group indexed by an infinite type has only one homotopy class,
without separation assumptions on the target. -/
theorem subsingleton_of_infinite (N : Type u) [Infinite N] (X : Type v)
    [TopologicalSpace X] (x : X) : Subsingleton (HomotopyGroup N X x) := by
  let : ContractibleSpace (GenLoop N X x) :=
    GenLoop.contractibleSpace_of_infinite N X x
  refine ⟨fun a b ↦ (HomotopyGroup.equivZerothHomotopy N x).injective ?_⟩
  exact Subsingleton.elim _ _

end HomotopyGroup
