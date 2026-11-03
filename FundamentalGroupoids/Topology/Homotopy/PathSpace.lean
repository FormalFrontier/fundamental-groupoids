/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.ContinuousMap
public import Mathlib.Topology.UnitInterval

/-!
# Initial segments of compact-open paths

Multiplication on the unit interval gives a homotopy from the constant-zero map
to the identity. Precomposition along this homotopy gives the jointly continuous
family `ContinuousMap.initialSegment`, sending `(u, γ)` to `t ↦ γ (u * t)`.

The target is an arbitrary topological space. Local compactness is used only for
the unit interval, through `ContinuousMap.Homotopy.compRightContinuousMap`.
The homotopy-fiber initial segments and the contraction of fixed-start paths are
specializations of this same family. Reversing homotopy time gives shortening
from a path to its constant initial path; the endpoint is free to move.
-/

@[expose] public section

open scoped unitInterval

namespace unitInterval

/-- Multiplication gives a homotopy from the constant-zero map to the identity. -/
def initialSegmentHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.const I (0 : I)) (ContinuousMap.id I) where
  toFun p := p.1 * p.2
  continuous_toFun :=
    (continuous_fst.subtype_val.mul continuous_snd.subtype_val).subtype_mk
      fun p => mul_mem p.1.property p.2.property
  map_zero_left t := zero_mul t
  map_one_left t := one_mul t

/-- The interval homotopy multiplies the two time parameters. -/
@[simp]
theorem initialSegmentHomotopy_apply (u t : I) :
    initialSegmentHomotopy (u, t) = u * t :=
  rfl

end unitInterval

namespace ContinuousMap

universe u v

variable {B : Type u} {Y : Type v} [TopologicalSpace B] [TopologicalSpace Y]

/-- Precomposition with interval multiplication, as a homotopy of path spaces. -/
def initialSegmentHomotopy :
    Homotopy (ContinuousMap.compRightContinuousMap B (ContinuousMap.const I (0 : I)))
      (ContinuousMap.compRightContinuousMap B (ContinuousMap.id I)) :=
  unitInterval.initialSegmentHomotopy.compRightContinuousMap (Z := B)

/-- The lifted homotopy retains the entire rescaled path. -/
@[simp]
theorem initialSegmentHomotopy_apply (u t : I) (γ : C(I, B)) :
    initialSegmentHomotopy (u, γ) t = γ (u * t) :=
  rfl

/-- The jointly continuous family of all multiplicative initial segments of paths. -/
def initialSegment : C(I × C(I, B), C(I, B)) :=
  (initialSegmentHomotopy (B := B)).toContinuousMap

/-- Evaluation of an initial segment at any path time. -/
@[simp]
theorem initialSegment_apply (u t : I) (γ : C(I, B)) :
    initialSegment (u, γ) t = γ (u * t) :=
  rfl

/-- Joint compact-open continuity, with no local-compactness assumption on the target. -/
theorem continuous_initialSegment : Continuous (initialSegment (B := B)) :=
  (initialSegment (B := B)).continuous

/-- Every initial segment starts at the original initial point. -/
theorem initialSegment_apply_zero (u : I) (γ : C(I, B)) :
    initialSegment (u, γ) 0 = γ 0 := by
  simp only [initialSegment_apply, mul_zero]

/-- The terminal point of an initial segment is the original path at its scale. -/
theorem initialSegment_apply_one (u : I) (γ : C(I, B)) :
    initialSegment (u, γ) 1 = γ u := by
  simp only [initialSegment_apply, mul_one]

/-- At scale zero the entire path is constant at its initial point. -/
@[simp]
theorem initialSegment_zero (γ : C(I, B)) :
    initialSegment (0, γ) = const I (γ 0) := by
  ext t
  simp only [initialSegment_apply, zero_mul, const_apply]

/-- At scale one the entire original path is retained. -/
@[simp]
theorem initialSegment_one (γ : C(I, B)) : initialSegment (1, γ) = γ := by
  ext t
  simp only [initialSegment_apply, one_mul]

/-- Constant paths are fixed at every scale. -/
@[simp]
theorem initialSegment_const (u : I) (b : B) :
    initialSegment (u, const I b) = const I b := by
  ext t
  rfl

/-- Initial segments commute with postcomposition by any continuous map. -/
theorem initialSegment_comp (f : C(B, Y)) (u : I) (γ : C(I, B)) :
    initialSegment (u, f.comp γ) = f.comp (initialSegment (u, γ)) := by
  ext t
  rfl

end ContinuousMap
