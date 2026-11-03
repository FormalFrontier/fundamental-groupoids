/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.CompactOpen

/-!
# Evaluation and target refinement for compact-open maps

For arbitrary topological spaces `A` and `Y`, `ContinuousMap.evalOfCompactlyGenerated`
is point evaluation from `κ_u (C(A, Y) × A)` to `Y`. The topology inside the refinement
is the ordinary product of the ordinary compact-open space and `A`. This does not
assert continuity of ordinary joint evaluation.

For a `UCompactlyGeneratedSpace.{u}` source `A` and an arbitrary target `Y`,
`Homeomorph.compactlyGeneratedCompactOpen` identifies `κ C(A, κY)` with `κ C(A, Y)`.
Its forward map is compactly generated counit postcomposition; its inverse lifts
continuous maps into the refined target without changing their values. Both maps
are natural in the original target.

`ContinuousMap.uncurryOfCompactlyGenerated` uncurries a continuous family when the
parameter is locally compact and both factors are `u`-compactly generated. Its
agreement with ordinary uncurrying is recorded when the argument is also locally
compact.

## Implementation notes

Continuity of evaluation is tested on compact Hausdorff probes. Precomposing each
map in a probe family by the probe's argument component gives a family of maps
on the probe itself. Ordinary uncurrying and the diagonal then give evaluation
along the probe. This uses local compactness of the probe, not of `A` or `C(A, Y)`.
Generated-space uncurrying factors through this evaluation, and supplies the
joint continuity used by the target lift. The original mapping-space topologies
are retained explicitly, and the compact-probe universe is independent of the
carrier universes.

## References

J. P. May, *A Concise Course in Algebraic Topology*, Chapter 5, §2, for the kified
compact-open mapping-space convention.
-/

@[expose] public section

universe u v w z

open TopologicalSpace

namespace ContinuousMap

variable (A : Type v) (Y : Type w) [tA : TopologicalSpace A] [tY : TopologicalSpace Y]

/-- Postcomposition by the compactly generated counit, with the ordinary compact-open
mapping-space topologies. This does not require a compactly generated source. -/
def compactOpenPostcompCounit :
    @ContinuousMap (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
      (@ContinuousMap A Y tA tY) inferInstance inferInstance where
  toFun := @ContinuousMap.comp A Y Y tA (compactlyGenerated.{u} Y) tY
    (compactlyGeneratedCounit.{u} Y)
  continuous_toFun := @ContinuousMap.continuous_postcomp A Y Y tA
    (compactlyGenerated.{u} Y) tY (compactlyGeneratedCounit.{u} Y)

/-- Postcomposition by the counit acts by composition on each continuous map. -/
theorem compactOpenPostcompCounit_apply
    (f : @ContinuousMap A Y tA (compactlyGenerated.{u} Y)) :
    compactOpenPostcompCounit.{u} A Y f =
      @ContinuousMap.comp A Y Y tA (compactlyGenerated.{u} Y) tY
        (compactlyGeneratedCounit.{u} Y) f := by
  rfl

/-- Postcomposition by the counit preserves point evaluations. -/
@[simp]
theorem compactOpenPostcompCounit_apply_apply
    (f : @ContinuousMap A Y tA (compactlyGenerated.{u} Y)) (a : A) :
    compactOpenPostcompCounit.{u} A Y f a = f a := by
  simp only [compactOpenPostcompCounit_apply, comp_apply, compactlyGeneratedCounit_apply]

/-- The comparison from the refinement of `C(A, κY)` to the refinement of `C(A, Y)`,
obtained by applying the compactly generated map functor to counit postcomposition. -/
def compactlyGeneratedCompactOpenComparison :
    @ContinuousMap (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
      (@ContinuousMap A Y tA tY)
      (compactlyGenerated.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y)))
      (compactlyGenerated.{u} (@ContinuousMap A Y tA tY)) :=
  compactlyGeneratedMap.{u} (compactOpenPostcompCounit.{u} A Y)

/-- The refined comparison has the same carrier map as counit postcomposition. -/
theorem compactlyGeneratedCompactOpenComparison_apply
    (f : @ContinuousMap A Y tA (compactlyGenerated.{u} Y)) :
    compactlyGeneratedCompactOpenComparison.{u} A Y f =
      compactOpenPostcompCounit.{u} A Y f := by
  exact compactlyGeneratedMap_apply.{u} (compactOpenPostcompCounit.{u} A Y) f

/-- The refined comparison preserves point evaluations. -/
@[simp]
theorem compactlyGeneratedCompactOpenComparison_apply_apply
    (f : @ContinuousMap A Y tA (compactlyGenerated.{u} Y)) (a : A) :
    compactlyGeneratedCompactOpenComparison.{u} A Y f a = f a := by
  simp only [compactlyGeneratedCompactOpenComparison_apply,
    compactOpenPostcompCounit_apply_apply]

/-- The comparison intertwines evaluation with the counits of both mapping spaces
and of the target. -/
theorem compactlyGeneratedCompactOpenComparison_counit_apply
    (f : @ContinuousMap A Y tA (compactlyGenerated.{u} Y)) (a : A) :
    compactlyGeneratedCounit.{u} (@ContinuousMap A Y tA tY)
        (compactlyGeneratedCompactOpenComparison.{u} A Y f) a =
      compactlyGeneratedCounit.{u} Y
        (compactlyGeneratedCounit.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
          f a) := by
  simp only [compactlyGeneratedCounit_apply,
    compactlyGeneratedCompactOpenComparison_apply_apply]

/-- Point evaluation from the compactly generated refinement of the ordinary
compact-open product. Neither the argument space nor the target needs to be
locally compact or compactly generated, and the probe universe is independent
of both carrier universes. -/
def evalOfCompactlyGenerated :
    @ContinuousMap (C(A, Y) × A) Y (compactlyGenerated.{u} (C(A, Y) × A)) tY :=
  @ContinuousMap.mk (C(A, Y) × A) Y (compactlyGenerated.{u} (C(A, Y) × A)) tY
    (fun p => p.1 p.2) (by
      refine @continuous_from_compactlyGenerated.{u} (C(A, Y) × A) Y
        instTopologicalSpaceProd tY (fun p => p.1 p.2) ?_
      intro K β
      let q : C(K, A) :=
        ⟨fun k => (β k).2, continuous_snd.comp β.continuous⟩
      let family : C(K, C(K, Y)) :=
        ⟨fun k => ((β k).1).comp q,
          (continuous_precomp q).comp (continuous_fst.comp β.continuous)⟩
      exact (continuous_uncurry_of_continuous family).comp
        (continuous_id.prodMk continuous_id))

/-- Evaluation retains the value at every function-argument pair. -/
@[simp]
theorem evalOfCompactlyGenerated_apply (p : C(A, Y) × A) :
    evalOfCompactlyGenerated.{u} A Y p = p.1 p.2 :=
  rfl

/-- On a locally compact argument space, refined evaluation is ordinary
uncurrying of the identity family after the counit of the ordinary product. -/
theorem evalOfCompactlyGenerated_eq_uncurry_comp_counit [LocallyCompactSpace A] :
    evalOfCompactlyGenerated.{u} A Y =
      @ContinuousMap.comp (C(A, Y) × A) (C(A, Y) × A) Y
        (compactlyGenerated.{u} (C(A, Y) × A)) instTopologicalSpaceProd tY
        ((ContinuousMap.id C(A, Y)).uncurry)
        (compactlyGeneratedCounit.{u} (C(A, Y) × A)) :=
  rfl

variable [UCompactlyGeneratedSpace.{u} A]

/-- Lift each continuous map into the compactly generated target. Continuity for
the refined compact-open topologies is `continuous_compactOpenTargetLift`. -/
def compactOpenTargetLift :
    (@ContinuousMap A Y tA tY) → @ContinuousMap A Y tA (compactlyGenerated.{u} Y) :=
  fun f => toCompactlyGenerated.{u} f

/-- The target lift is the generated-source lift of the individual continuous map. -/
theorem compactOpenTargetLift_apply (f : @ContinuousMap A Y tA tY) :
    compactOpenTargetLift.{u} A Y f = toCompactlyGenerated.{u} f := by
  rfl

/-- The target lift preserves point evaluations. -/
@[simp]
theorem compactOpenTargetLift_apply_apply (f : @ContinuousMap A Y tA tY) (a : A) :
    compactOpenTargetLift.{u} A Y f a = f a := by
  simp only [compactOpenTargetLift_apply, toCompactlyGenerated_apply]

/-- Evaluation of the target lift commutes with the mapping-space and target counits. -/
theorem compactOpenTargetLift_counit_apply (f : @ContinuousMap A Y tA tY) (a : A) :
    compactlyGeneratedCounit.{u} Y
        (compactlyGeneratedCounit.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
          (compactOpenTargetLift.{u} A Y f) a) =
      compactlyGeneratedCounit.{u} (@ContinuousMap A Y tA tY) f a := by
  simp only [compactlyGeneratedCounit_apply, compactOpenTargetLift_apply_apply]

/-- Uncurry a continuous compact-open family with locally compact parameter and
`u`-compactly generated parameter and argument spaces. The argument space need not
be locally compact. -/
def uncurryOfCompactlyGenerated {P : Type z} [TopologicalSpace P]
    [UCompactlyGeneratedSpace.{u} P] [LocallyCompactSpace P] (f : C(P, C(A, Y))) :
    C(P × A, Y) :=
  @ContinuousMap.comp (P × A) (C(A, Y) × A) Y instTopologicalSpaceProd
    (compactlyGenerated.{u} (C(A, Y) × A)) tY
    (evalOfCompactlyGenerated.{u} A Y)
    (toCompactlyGenerated.{u} (f.prodMap (ContinuousMap.id A)))

/-- Uncurrying retains every value of the given family. -/
@[simp]
theorem uncurryOfCompactlyGenerated_apply {P : Type z} [TopologicalSpace P]
    [UCompactlyGeneratedSpace.{u} P] [LocallyCompactSpace P] (f : C(P, C(A, Y)))
    (p : P) (a : A) :
    uncurryOfCompactlyGenerated.{u} A Y f (p, a) = f p a :=
  rfl

/-- On a locally compact argument space, generated-space uncurrying agrees with
ordinary compact-open uncurrying. -/
theorem uncurryOfCompactlyGenerated_eq_uncurry {P : Type z} [TopologicalSpace P]
    [UCompactlyGeneratedSpace.{u} P] [LocallyCompactSpace P] [LocallyCompactSpace A]
    (f : C(P, C(A, Y))) :
    uncurryOfCompactlyGenerated.{u} A Y f = f.uncurry := by
  apply ContinuousMap.ext
  rintro ⟨p, a⟩
  rfl

/-- The carrier target lift is continuous between the compactly generated
refinements of the two ordinary compact-open mapping spaces. -/
theorem continuous_compactOpenTargetLift :
    @Continuous (@ContinuousMap A Y tA tY)
      (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
      (compactlyGenerated.{u} (@ContinuousMap A Y tA tY))
      (compactlyGenerated.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y)))
      (compactOpenTargetLift.{u} A Y) := by
  refine @continuous_from_compactlyGenerated.{u}
    (@ContinuousMap A Y tA tY)
    (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
    inferInstance
    (compactlyGenerated.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y)))
    (compactOpenTargetLift.{u} A Y) ?_
  intro K α
  have hjoint : @Continuous (K × A) Y
      instTopologicalSpaceProd (compactlyGenerated.{u} Y) (fun p => α p.1 p.2) :=
    (@continuous_to_compactlyGenerated_iff.{u} (K × A) Y
      instTopologicalSpaceProd tY inferInstance
      (fun p => α p.1 p.2)).2 (uncurryOfCompactlyGenerated.{u} A Y α).continuous
  have hfamily : @Continuous K (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
      inferInstance inferInstance (fun k => compactOpenTargetLift.{u} A Y (α k)) := by
    refine @continuous_of_continuous_uncurry K A Y inferInstance tA
      (compactlyGenerated.{u} Y) (fun k => compactOpenTargetLift.{u} A Y (α k)) ?_
    refine @Continuous.congr (K × A) Y instTopologicalSpaceProd
      (compactlyGenerated.{u} Y) _ _ hjoint ?_
    rintro ⟨k, a⟩
    exact (compactOpenTargetLift_apply_apply.{u} A Y (α k) a).symm
  exact (@continuous_to_compactlyGenerated_iff.{u} K
    (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
    inferInstance inferInstance inferInstance
    (fun k => compactOpenTargetLift.{u} A Y (α k))).2 hfamily

/-- Lifting after the refined comparison recovers the original map into the
refined target. -/
@[simp]
theorem compactOpenTargetLift_compactlyGeneratedCompactOpenComparison
    (f : @ContinuousMap A Y tA (compactlyGenerated.{u} Y)) :
    compactOpenTargetLift.{u} A Y (compactlyGeneratedCompactOpenComparison.{u} A Y f) = f := by
  apply @ContinuousMap.ext A Y tA (compactlyGenerated.{u} Y)
  intro a
  rfl

/-- The refined comparison after lifting recovers the original map into the
original target. -/
@[simp]
theorem compactlyGeneratedCompactOpenComparison_compactOpenTargetLift
    (f : @ContinuousMap A Y tA tY) :
    compactlyGeneratedCompactOpenComparison.{u} A Y (compactOpenTargetLift.{u} A Y f) = f := by
  apply @ContinuousMap.ext A Y tA tY
  intro a
  rfl

omit [UCompactlyGeneratedSpace.{u} A] in
/-- The refined comparison commutes with target postcomposition. -/
theorem compactlyGeneratedCompactOpenComparison_naturality
    (Z : Type z) [tZ : TopologicalSpace Z] (g : @ContinuousMap Y Z tY tZ)
    (f : @ContinuousMap A Y tA (compactlyGenerated.{u} Y)) :
    compactlyGeneratedCompactOpenComparison.{u} A Z
        (compactlyGeneratedMap.{u}
          (⟨@ContinuousMap.comp A Y Z tA (compactlyGenerated.{u} Y)
              (compactlyGenerated.{u} Z) (compactlyGeneratedMap.{u} g),
            @ContinuousMap.continuous_postcomp A Y Z tA (compactlyGenerated.{u} Y)
              (compactlyGenerated.{u} Z) (compactlyGeneratedMap.{u} g)⟩ :
            @ContinuousMap (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
              (@ContinuousMap A Z tA (compactlyGenerated.{u} Z))
              inferInstance inferInstance) f) =
      compactlyGeneratedMap.{u}
        (⟨@ContinuousMap.comp A Y Z tA tY tZ g,
          @ContinuousMap.continuous_postcomp A Y Z tA tY tZ g⟩ :
          @ContinuousMap (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
            inferInstance inferInstance)
        (compactlyGeneratedCompactOpenComparison.{u} A Y f) := by
  apply @ContinuousMap.ext A Z tA tZ
  intro a
  rfl

/-- The carrier target lift commutes with target postcomposition. -/
theorem compactOpenTargetLift_naturality
    (Z : Type z) [tZ : TopologicalSpace Z] (g : @ContinuousMap Y Z tY tZ)
    (f : @ContinuousMap A Y tA tY) :
    compactOpenTargetLift.{u} A Z
        (compactlyGeneratedMap.{u}
          (⟨@ContinuousMap.comp A Y Z tA tY tZ g,
            @ContinuousMap.continuous_postcomp A Y Z tA tY tZ g⟩ :
            @ContinuousMap (@ContinuousMap A Y tA tY) (@ContinuousMap A Z tA tZ)
              inferInstance inferInstance) f) =
      compactlyGeneratedMap.{u}
        (⟨@ContinuousMap.comp A Y Z tA (compactlyGenerated.{u} Y)
            (compactlyGenerated.{u} Z) (compactlyGeneratedMap.{u} g),
          @ContinuousMap.continuous_postcomp A Y Z tA (compactlyGenerated.{u} Y)
            (compactlyGenerated.{u} Z) (compactlyGeneratedMap.{u} g)⟩ :
          @ContinuousMap (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
            (@ContinuousMap A Z tA (compactlyGenerated.{u} Z))
            inferInstance inferInstance)
        (compactOpenTargetLift.{u} A Y f) := by
  apply @ContinuousMap.ext A Z tA (compactlyGenerated.{u} Z)
  intro a
  rfl

end ContinuousMap

namespace Homeomorph

variable (A : Type v) (Y : Type w) [tA : TopologicalSpace A] [tY : TopologicalSpace Y]
  [UCompactlyGeneratedSpace.{u} A]

/-- Refining the target does not change the compactly generated compact-open
mapping space from a `u`-compactly generated source. The forward map is counit
postcomposition and the inverse is the unchanged-function target lift. -/
def compactlyGeneratedCompactOpen :
    @Homeomorph (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
      (@ContinuousMap A Y tA tY)
      (compactlyGenerated.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y)))
      (compactlyGenerated.{u} (@ContinuousMap A Y tA tY)) :=
  @Homeomorph.mk (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
    (@ContinuousMap A Y tA tY)
    (compactlyGenerated.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y)))
    (compactlyGenerated.{u} (@ContinuousMap A Y tA tY))
    { toFun := ContinuousMap.compactlyGeneratedCompactOpenComparison.{u} A Y
      invFun := ContinuousMap.compactOpenTargetLift.{u} A Y
      left_inv := fun f =>
        ContinuousMap.compactOpenTargetLift_compactlyGeneratedCompactOpenComparison.{u} A Y f
      right_inv := fun f =>
        ContinuousMap.compactlyGeneratedCompactOpenComparison_compactOpenTargetLift.{u} A Y f }
    (@ContinuousMap.continuous_toFun
      (@ContinuousMap A Y tA (compactlyGenerated.{u} Y)) (@ContinuousMap A Y tA tY)
      (compactlyGenerated.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y)))
      (compactlyGenerated.{u} (@ContinuousMap A Y tA tY))
      (ContinuousMap.compactlyGeneratedCompactOpenComparison.{u} A Y))
    (ContinuousMap.continuous_compactOpenTargetLift.{u} A Y)

/-- The forward homeomorphism is the specified refined comparison. -/
theorem compactlyGeneratedCompactOpen_apply
    (f : @ContinuousMap A Y tA (compactlyGenerated.{u} Y)) :
    compactlyGeneratedCompactOpen.{u} A Y f =
      ContinuousMap.compactlyGeneratedCompactOpenComparison.{u} A Y f :=
  rfl

/-- The forward homeomorphism preserves point evaluations. -/
@[simp]
theorem compactlyGeneratedCompactOpen_apply_apply
    (f : @ContinuousMap A Y tA (compactlyGenerated.{u} Y)) (a : A) :
    compactlyGeneratedCompactOpen.{u} A Y f a = f a := by
  simp only [compactlyGeneratedCompactOpen_apply,
    ContinuousMap.compactlyGeneratedCompactOpenComparison_apply_apply]

/-- The inverse homeomorphism is the specified carrier target lift. -/
theorem compactlyGeneratedCompactOpen_symm_apply (f : @ContinuousMap A Y tA tY) :
    (@Homeomorph.symm (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
      (@ContinuousMap A Y tA tY)
      (compactlyGenerated.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y)))
      (compactlyGenerated.{u} (@ContinuousMap A Y tA tY))
      (compactlyGeneratedCompactOpen.{u} A Y)) f =
        ContinuousMap.compactOpenTargetLift.{u} A Y f :=
  rfl

/-- The inverse homeomorphism preserves point evaluations. -/
@[simp]
theorem compactlyGeneratedCompactOpen_symm_apply_apply
    (f : @ContinuousMap A Y tA tY) (a : A) :
    (@Homeomorph.symm (@ContinuousMap A Y tA (compactlyGenerated.{u} Y))
      (@ContinuousMap A Y tA tY)
      (compactlyGenerated.{u} (@ContinuousMap A Y tA (compactlyGenerated.{u} Y)))
      (compactlyGenerated.{u} (@ContinuousMap A Y tA tY))
      (compactlyGeneratedCompactOpen.{u} A Y)) f a = f a := by
  simp only [compactlyGeneratedCompactOpen_symm_apply,
    ContinuousMap.compactOpenTargetLift_apply_apply]

/-- The full forward continuous map of the homeomorphism is the specified
compactly generated comparison. -/
theorem compactlyGeneratedCompactOpen_continuousMap :
    let S := @ContinuousMap A Y tA (compactlyGenerated.{u} Y)
    let T := @ContinuousMap A Y tA tY
    let tS := compactlyGenerated.{u} S
    let tT := compactlyGenerated.{u} T
    @_root_.toContinuousMap (@Homeomorph S T tS tT) S T tS tT
      inferInstance inferInstance
      (compactlyGeneratedCompactOpen.{u} A Y) =
        ContinuousMap.compactlyGeneratedCompactOpenComparison.{u} A Y := by
  rfl

end Homeomorph
