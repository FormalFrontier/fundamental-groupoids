/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Cube.Deformation
public import FundamentalGroupoids.Topology.Homotopy.Relative

/-!
# Comparing maps on a finite cylinder

Maps from a finite cylinder that agree on its bottom and coordinate-face sides
are homotopic relative to that subset. The construction allows an arbitrary
parameter space, which remains fixed by the source deformation. Restricting the
comparison to the top gives a homotopy of the final cube maps relative to their
coordinate-face boundary.

There are no assumptions on the target beyond a topology. In particular, the
comparison deforms the source cylinder, not the values of the maps.

## References

* `FundamentalGroupoids.Topology.Homotopy.Cube.Deformation` supplies the cylinder
  retraction and its relative deformation.
* Mathlib's `ContinuousMap.Homotopy.prodMap` supplies the product deformation;
  `ContinuousMap.HomotopyRel.ofEqOnRetraction` supplies the comparison.
-/

public section

noncomputable section

universe u v w

open unitInterval

namespace Cube

private def cylinderProductRetraction (N : Type u) [Finite N]
    (P : Type v) [TopologicalSpace P] :
    C(P × (I × (N → I)), {q : P × (I × (N → I)) | q.2 ∈ bottomSides N}) where
  toFun q :=
    ⟨(q.1, (cylinderRetraction N q.2).val), (cylinderRetraction N q.2).property⟩
  continuous_toFun :=
    ((ContinuousMap.id P).prodMap
      ((ContinuousMap.subtypeVal (bottomSides N)).comp
        (cylinderRetraction N))).continuous.subtype_mk _

private def cylinderProductDeformation (N : Type u) [Finite N]
    (P : Type v) [TopologicalSpace P] :
    ContinuousMap.HomotopyRel (ContinuousMap.id (P × (I × (N → I))))
      ((ContinuousMap.subtypeVal {q : P × (I × (N → I)) | q.2 ∈ bottomSides N}).comp
        (cylinderProductRetraction N P))
      {q : P × (I × (N → I)) | q.2 ∈ bottomSides N} where
  toHomotopy :=
    ((ContinuousMap.Homotopy.refl (ContinuousMap.id P)).prodMap
      (cylinderDeformation N).toHomotopy).cast
        (ContinuousMap.ext fun _ ↦ rfl) (ContinuousMap.ext fun _ ↦ rfl)
  prop' t _q hq := Prod.ext rfl ((cylinderDeformation N).eq_fst t hq)

private theorem cylinderProductDeformation_apply (N : Type u) [Finite N]
    (P : Type v) [TopologicalSpace P] (t : I) (q : P × (I × (N → I))) :
    cylinderProductDeformation N P (t, q) = (q.1, cylinderDeformation N (t, q.2)) :=
  rfl

variable {N : Type u} {P : Type v} {X : Type w}
  [TopologicalSpace P] [TopologicalSpace X]

/-- Maps on a finite cylinder agreeing on the bottom and sides are homotopic
relative to that subset, with an arbitrary parameter space left unchanged. -/
def cylinderComparison [Finite N] (F G : C(P × (I × (N → I)), X))
    (hFG : Set.EqOn F G {q | q.2 ∈ bottomSides N}) :
    ContinuousMap.HomotopyRel F G {q | q.2 ∈ bottomSides N} :=
  ContinuousMap.HomotopyRel.ofEqOnRetraction
    (cylinderProductRetraction N P) (cylinderProductDeformation N P) F G hFG

/-- The cylinder comparison follows the source deformation through `F` and then
follows it backwards through `G`, keeping the parameter fixed. -/
theorem cylinderComparison_apply [Finite N] (F G : C(P × (I × (N → I)), X))
    (hFG : Set.EqOn F G {q | q.2 ∈ bottomSides N}) (q : I × (P × (I × (N → I)))) :
    cylinderComparison F G hFG q =
      if h : (q.1 : ℝ) ≤ 1 / 2 then
        F (q.2.1, cylinderDeformation N (⟨2 * q.1,
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨q.1.2.1, h⟩⟩, q.2.2))
      else
        G (q.2.1, cylinderDeformation N (σ ⟨2 * q.1 - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, q.1.2.2⟩⟩, q.2.2)) := by
  simp only [cylinderComparison, ContinuousMap.HomotopyRel.ofEqOnRetraction_apply,
    cylinderProductDeformation_apply]

/-- Restriction of a parameterized cylinder map to its top face. -/
@[expose]
def restrictCylinderTop (F : C(P × (I × (N → I)), X)) : C(P × (N → I), X) :=
  F.comp ((ContinuousMap.id P).prodMap
    ((ContinuousMap.const (N → I) (1 : I)).prodMk (ContinuousMap.id (N → I))))

@[simp]
theorem restrictCylinderTop_apply (F : C(P × (I × (N → I)), X))
    (q : P × (N → I)) : restrictCylinderTop F q = F (q.1, (1, q.2)) :=
  rfl

/-- Agreement on the bottom and sides of a finite cylinder gives a homotopy
between the top restrictions, relative to the cube boundary, for every parameter. -/
def cylinderComparisonTop [Finite N] (F G : C(P × (I × (N → I)), X))
    (hFG : Set.EqOn F G {q | q.2 ∈ bottomSides N}) :
    ContinuousMap.HomotopyRel (restrictCylinderTop F) (restrictCylinderTop G)
      {q : P × (N → I) | q.2 ∈ boundary N} :=
  (cylinderComparison F G hFG).precomp
    ((ContinuousMap.id P).prodMap
      ((ContinuousMap.const (N → I) (1 : I)).prodMk (ContinuousMap.id (N → I))))
    (fun _ hq ↦ Or.inr hq)

@[simp]
theorem cylinderComparisonTop_apply [Finite N] (F G : C(P × (I × (N → I)), X))
    (hFG : Set.EqOn F G {q | q.2 ∈ bottomSides N}) (q : I × (P × (N → I))) :
    cylinderComparisonTop F G hFG q =
      cylinderComparison F G hFG (q.1, (q.2.1, (1, q.2.2))) := by
  rfl

end Cube
