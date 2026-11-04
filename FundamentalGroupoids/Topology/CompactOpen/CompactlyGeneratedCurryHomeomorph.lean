/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.CompactOpen.CompactlyGeneratedCurry

/-!
# The refined compact-open currying homeomorphism

For compactly generated original spaces `P` and `A`, the scalar currying
equivalence is a homeomorphism after refining the two ordinary compact-open
operator spaces. Its source consists of maps from the refinement of the original
product; its target consists of families in the refinement of `C(A, Y)`. The
original target `Y` is arbitrary, and all carrier universes are independent of
the compact Hausdorff probe universe.

Operator continuity follows by applying scalar uncurrying to an identity map,
reassociating refined products, and applying scalar currying twice. In particular,
the intermediate parameter space is the refinement of a product, not an assumed
compactly generated ordinary product.

The characteristic laws retain the scalar equivalence, its ordinary-curry
compatibility, and simultaneous source-source-target naturality. Evaluation is
only asserted on refined products. The construction reuses the scalar exponential
law and Mathlib's compact-open mapping spaces.

## References

For the compactly generated-space setting of the exponential law, see J. Peter
May, *A Concise Course in Algebraic Topology*. The scalar equivalence used here is
`ContinuousMap.compactlyGeneratedCurryEquiv`.

Mathlib's [generated-topology framework][generated-by] is by Joël Riou, Dagur
Asgeirsson and Ben Eltschig. Its [generated-map continuity][generated-maps] and
[convenient hom-space][hom-space] APIs are by Joël Riou.

[generated-by]: https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/GeneratedBy.lean
[generated-maps]: https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/ContinuousMapGeneratedBy.lean
[hom-space]: https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/HomSpace.lean
-/

@[expose] public section

noncomputable section

universe u p a y p' a' y' p'' a'' y'' x z x' z' x'' z''

open TopologicalSpace Topology

namespace Homeomorph

section Curry

variable (P : Type p) (A : Type a) (Y : Type y)
  [tP : TopologicalSpace P] [tA : TopologicalSpace A] [tY : TopologicalSpace Y]
  [hP : UCompactlyGeneratedSpace.{u} P] [hA : UCompactlyGeneratedSpace.{u} A]

local notation "τPA" => @instTopologicalSpaceProd P A tP tA

local notation "B" => @ContinuousMap A Y tA tY

/-- Currying is a homeomorphism between the compactly generated refinements of
these ordinary compact-open spaces. The product uses the original factor
topologies before refinement, and the right-hand compact-open topology uses the
refined argument mapping space as target. No condition on the original target
space is required. For the compactly generated-space setting of the exponential
law, see J. Peter May, *A Concise Course in Algebraic Topology*. -/
def compactlyGeneratedCurry :
    @Homeomorph
      (@ContinuousMap (P × A) Y
        (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)
      (@ContinuousMap P (@ContinuousMap A Y tA tY) tP
        (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY)
          (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u}
        (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)
        (@ContinuousMap.compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY))
      (@compactlyGenerated.{u}
        (@ContinuousMap P (@ContinuousMap A Y tA tY) tP
          (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY)
            (@ContinuousMap.compactOpen A Y tA tY)))
        (@ContinuousMap.compactOpen P (@ContinuousMap A Y tA tY) tP
          (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY)
            (@ContinuousMap.compactOpen A Y tA tY)))) := by
  let τB : TopologicalSpace B :=
    @compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)
  let S := @ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY
  let τS : TopologicalSpace S := @compactlyGenerated.{u} S
    (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
  let T := @ContinuousMap P B tP τB
  let τT : TopologicalSpace T :=
    @compactlyGenerated.{u} T (@ContinuousMap.compactOpen P B tP τB)
  -- Scalar uncurrying of the identity gives evaluation on a refined product.
  -- The two subsequent scalar currying steps use the refined intermediate product.
  let curryOperator : @ContinuousMap S T τS τT := by
    let v : @ContinuousMap ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P
      × A)) Y (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P
      × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u} (P × A) τPA))) tY :=
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} (@ContinuousMap (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) Y (@compactlyGenerated.{u} (@ContinuousMap
        (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u} (P × A) τPA) tY
        inferInstance inferInstance).symm
          (@ContinuousMap.id (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
            (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
            tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)))
    let r : @Homeomorph (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × P) ×
      A) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
      (@compactlyGenerated.{u} (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
      A) τPA) tY) × P) A (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY) × P) (@instTopologicalSpaceProd (@ContinuousMap (P ×
      A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) P (@compactlyGenerated.{u} (@ContinuousMap (P ×
      A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY)) tP)) tA)) (@compactlyGenerated.{u} ((@ContinuousMap
      (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A)) (@instTopologicalSpaceProd
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A)
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (P × A) τPA))) :=
      @Homeomorph.compactlyGeneratedProdAssoc.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u}
        (P × A) τPA) tY) P A (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY)) tP tA
    let rMap : @ContinuousMap (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      × P) × A) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
      (@compactlyGenerated.{u} (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
      A) τPA) tY) × P) A (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY) × P) (@instTopologicalSpaceProd (@ContinuousMap (P ×
      A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) P (@compactlyGenerated.{u} (@ContinuousMap (P ×
      A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY)) tP)) tA)) (@compactlyGenerated.{u} ((@ContinuousMap
      (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A)) (@instTopologicalSpaceProd
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A)
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (P × A) τPA))) :=
      @ContinuousMap.mk (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × P) ×
        A) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
        (@compactlyGenerated.{u} (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
        tY) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u}
        (P × A) τPA) tY) × P) A (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY) × P) (@instTopologicalSpaceProd (@ContinuousMap (P
        × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) P (@compactlyGenerated.{u} (@ContinuousMap
        (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY)) tP)) tA)) (@compactlyGenerated.{u}
        ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
        (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
        tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
        A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@compactlyGenerated.{u} (P × A) τPA)))
        (@Homeomorph.toEquiv (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) ×
          P) × A) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
          (@compactlyGenerated.{u} (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) × P) A (@compactlyGenerated.{u} ((@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × P) (@instTopologicalSpaceProd
          (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) P
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) tP))
          tA)) (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          τPA) tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u} (P × A) τPA))) r)
        (@Homeomorph.continuous_toFun (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          τPA) tY) × P) × A) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) ×
          (P × A)) (@compactlyGenerated.{u} (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
          × A) τPA) tY) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) × P) A (@compactlyGenerated.{u} ((@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × P) (@instTopologicalSpaceProd
          (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) P
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) tP))
          tA)) (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          τPA) tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u} (P × A) τPA))) r)
    let w : @ContinuousMap (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) ×
      P) × A) Y (@compactlyGenerated.{u} (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
      A) τPA) tY) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY) × P) A (@compactlyGenerated.{u} ((@ContinuousMap (P
      × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × P) (@instTopologicalSpaceProd
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) P (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY)) tP)) tA)) tY :=
      @ContinuousMap.comp (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × P)
        × A) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A)) Y
        (@compactlyGenerated.{u} (((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
        tY) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u}
        (P × A) τPA) tY) × P) A (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY) × P) (@instTopologicalSpaceProd (@ContinuousMap (P
        × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) P (@compactlyGenerated.{u} (@ContinuousMap
        (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY)) tP)) tA)) (@compactlyGenerated.{u}
        ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
        (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
        tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
        A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@compactlyGenerated.{u} (P × A) τPA))) tY v rMap
    let c : @ContinuousMap ((@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY) × P) B
      (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      × P) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY) P (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) tP))
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)) :=
      @ContinuousMap.compactlyGeneratedCurryEquiv.{u}
        ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × P) A Y
          (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) × P) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
          × A) τPA) tY) P (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) tP)) tA tY inferInstance hA w
    exact @ContinuousMap.compactlyGeneratedCurryEquiv.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
        tY) P B (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
        τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)) inferInstance hP c
  let uncurryOperator : @ContinuousMap T S τT τS := by
    let v : @ContinuousMap ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) B (@compactlyGenerated.{u} ((@ContinuousMap P B
      tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P)
      (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY)))) tP))
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)) :=
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) P B
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)) inferInstance hP).symm
          (@ContinuousMap.id (@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u} (@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
          (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY)))))
    let w : @ContinuousMap (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) × A) Y (@compactlyGenerated.{u}
      (((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) ×
      P) × A) (@instTopologicalSpaceProd ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u} ((@ContinuousMap P B
      tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P)
      (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y
      tA tY)))) tP)) tA)) tY :=
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} ((@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) A Y
        (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × P) (@instTopologicalSpaceProd (@ContinuousMap P B
        tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) P
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) tP)) tA
        tY inferInstance hA).symm v
    let r : @Homeomorph (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) × A) ((@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × (P × A))
      (@compactlyGenerated.{u} (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap
      P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) A
      (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) (@instTopologicalSpaceProd (@ContinuousMap P B
      tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) P
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) tP))
      tA)) (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap
      P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (P × A)
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGenerated.{u} (P × A) τPA))) :=
      @Homeomorph.compactlyGeneratedProdAssoc.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) P A (@compactlyGenerated.{u} (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY)))) tP tA
    let rInv : @Homeomorph ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (((@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) × A)
      (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap
      P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (P × A)
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
      (P × A) τPA))) (@compactlyGenerated.{u} (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap
      P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) A
      (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) (@instTopologicalSpaceProd (@ContinuousMap P B
      tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) P
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) tP)) tA)) :=
      @Homeomorph.symm (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × P) × A) ((@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × (P ×
        A)) (@compactlyGenerated.{u} (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × P) × A) (@instTopologicalSpaceProd
        ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        × P) A (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × P) (@instTopologicalSpaceProd (@ContinuousMap P B
        tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) P
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) tP))
        tA)) (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
        (@compactlyGenerated.{u} (P × A) τPA))) r
    let rInvMap : @ContinuousMap ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (((@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) × A)
      (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap
      P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (P × A)
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
      (P × A) τPA))) (@compactlyGenerated.{u} (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap
      P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) A
      (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × P) (@instTopologicalSpaceProd (@ContinuousMap P B
      tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) P
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) tP)) tA)) :=
      @ContinuousMap.mk ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (((@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) ×
        A) (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
        (@compactlyGenerated.{u} (P × A) τPA))) (@compactlyGenerated.{u} (((@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) × A)
        (@instTopologicalSpaceProd ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u} ((@ContinuousMap P
        B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P)
        (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY)))) tP)) tA))
        (@Homeomorph.toEquiv ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (((@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) × A)
          (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd
          (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
          (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
          (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
          (@compactlyGenerated.{u} (P × A) τPA))) (@compactlyGenerated.{u} (((@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) × A)
          (@instTopologicalSpaceProd ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u} ((@ContinuousMap
          P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P)
          (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
          (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen
          A Y tA tY)))) tP)) tA)) rInv)
        (@Homeomorph.continuous_toFun ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (((@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) × A)
          (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd
          (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
          (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
          (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
          (@compactlyGenerated.{u} (P × A) τPA))) (@compactlyGenerated.{u} (((@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) × A)
          (@instTopologicalSpaceProd ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u} ((@ContinuousMap
          P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P)
          (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@ContinuousMap.compactOpen A Y tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
          (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen
          A Y tA tY)))) tP)) tA)) rInv)
    let z : @ContinuousMap ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) Y (@compactlyGenerated.{u}
      ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) ×
      (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B
      tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y
      tA tY)))) (@compactlyGenerated.{u} (P × A) τPA))) tY :=
      @ContinuousMap.comp ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (((@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) × A) Y
        (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
        (@compactlyGenerated.{u} (P × A) τPA))) (@compactlyGenerated.{u} (((@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P) × A)
        (@instTopologicalSpaceProd ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u} ((@ContinuousMap P
        B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) × P)
        (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A
        Y tA tY)))) tP)) tA)) tY w rInvMap
    exact @ContinuousMap.compactlyGeneratedCurryEquiv.{u}
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (P
        × A) Y (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA
        tY)))) (@compactlyGenerated.{u} (P × A) τPA) tY inferInstance inferInstance z
  have curryOperator_apply : ∀ (h : S) (p : P) (a : A),
      curryOperator h p a = h (p, a) := by
    intro h p a
    let τSP : TopologicalSpace (S × P) :=
      @compactlyGenerated.{u} (S × P) (@instTopologicalSpaceProd S P τS tP)
    let τL : TopologicalSpace ((S × P) × A) :=
      @compactlyGenerated.{u} ((S × P) × A) (@instTopologicalSpaceProd (S × P) A τSP tA)
    let τR : TopologicalSpace (S × (P × A)) :=
      @compactlyGenerated.{u} (S × (P × A))
        (@instTopologicalSpaceProd S (P × A) τS (@compactlyGenerated.{u} (P × A) τPA))
    let v : @ContinuousMap (S × (P × A)) Y τR tY :=
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} S (P × A) Y
        τS (@compactlyGenerated.{u} (P × A) τPA) tY inferInstance inferInstance).symm
          (@ContinuousMap.id S τS)
    let r : @Homeomorph ((S × P) × A) (S × (P × A)) τL τR :=
      @Homeomorph.compactlyGeneratedProdAssoc.{u} S P A τS tP tA
    let rMap : @ContinuousMap ((S × P) × A) (S × (P × A)) τL τR :=
      @ContinuousMap.mk ((S × P) × A) (S × (P × A)) τL τR
        (@Homeomorph.toEquiv ((S × P) × A) (S × (P × A)) τL τR r)
        (@Homeomorph.continuous_toFun ((S × P) × A) (S × (P × A)) τL τR r)
    let w : @ContinuousMap ((S × P) × A) Y τL tY :=
      @ContinuousMap.comp ((S × P) × A) (S × (P × A)) Y τL τR tY v rMap
    let c : @ContinuousMap (S × P) B τSP τB :=
      @ContinuousMap.compactlyGeneratedCurryEquiv.{u} (S × P) A Y
        τSP tA tY inferInstance hA w
    change (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} S P B
      τS tP τB inferInstance hP c) h p a = h (p, a)
    calc
      _ = c (h, p) a := congrArg (fun b : B => b a)
        (@ContinuousMap.compactlyGeneratedCurryEquiv_apply_apply.{u}
          S P B τS tP τB inferInstance hP c h p)
      _ = w ((h, p), a) :=
        @ContinuousMap.compactlyGeneratedCurryEquiv_apply_apply.{u}
          (S × P) A Y τSP tA tY inferInstance hA w (h, p) a
      _ = v ((@Homeomorph.toEquiv ((S × P) × A) (S × (P × A)) τL τR r)
          ((h, p), a)) := rfl
      _ = v (h, (p, a)) := congrArg (fun q : S × (P × A) => v q)
        (@compactlyGeneratedProdAssoc_apply.{u} S P A τS tP tA ((h, p), a))
      _ = h (p, a) := @ContinuousMap.compactlyGeneratedCurryEquiv_symm_apply_apply.{u}
        S (P × A) Y τS (@compactlyGenerated.{u} (P × A) τPA) tY
        inferInstance inferInstance (@ContinuousMap.id S τS) h (p, a)
  have uncurryOperator_apply : ∀ (g : T) (p : P) (a : A),
      uncurryOperator g (p, a) = g p a := by
    intro g p a
    let τTP : TopologicalSpace (T × P) :=
      @compactlyGenerated.{u} (T × P) (@instTopologicalSpaceProd T P τT tP)
    let τL : TopologicalSpace ((T × P) × A) :=
      @compactlyGenerated.{u} ((T × P) × A) (@instTopologicalSpaceProd (T × P) A τTP tA)
    let τR : TopologicalSpace (T × (P × A)) :=
      @compactlyGenerated.{u} (T × (P × A))
        (@instTopologicalSpaceProd T (P × A) τT (@compactlyGenerated.{u} (P × A) τPA))
    let v : @ContinuousMap (T × P) B τTP τB :=
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} T P B
        τT tP τB inferInstance hP).symm (@ContinuousMap.id T τT)
    let w : @ContinuousMap ((T × P) × A) Y τL tY :=
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} (T × P) A Y
        τTP tA tY inferInstance hA).symm v
    let r : @Homeomorph ((T × P) × A) (T × (P × A)) τL τR :=
      @Homeomorph.compactlyGeneratedProdAssoc.{u} T P A τT tP tA
    let rInv : @Homeomorph (T × (P × A)) ((T × P) × A) τR τL :=
      @Homeomorph.symm ((T × P) × A) (T × (P × A)) τL τR r
    let rInvMap : @ContinuousMap (T × (P × A)) ((T × P) × A) τR τL :=
      @ContinuousMap.mk (T × (P × A)) ((T × P) × A) τR τL
        (@Homeomorph.toEquiv (T × (P × A)) ((T × P) × A) τR τL rInv)
        (@Homeomorph.continuous_toFun (T × (P × A)) ((T × P) × A) τR τL rInv)
    let z : @ContinuousMap (T × (P × A)) Y τR tY :=
      @ContinuousMap.comp (T × (P × A)) ((T × P) × A) Y τR τL tY w rInvMap
    change (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} T (P × A) Y
      τT (@compactlyGenerated.{u} (P × A) τPA) tY inferInstance inferInstance z)
        g (p, a) = g p a
    calc
      _ = z (g, (p, a)) :=
        @ContinuousMap.compactlyGeneratedCurryEquiv_apply_apply.{u}
          T (P × A) Y τT (@compactlyGenerated.{u} (P × A) τPA) tY
          inferInstance inferInstance z g (p, a)
      _ = w (((@Homeomorph.toEquiv ((T × P) × A) (T × (P × A)) τL τR r).symm)
          (g, (p, a))) := rfl
      _ = w ((g, p), a) := congrArg (fun q : (T × P) × A => w q)
        (@compactlyGeneratedProdAssoc_symm_apply.{u} T P A τT tP tA (g, (p, a)))
      _ = v (g, p) a :=
        @ContinuousMap.compactlyGeneratedCurryEquiv_symm_apply_apply.{u}
          (T × P) A Y τTP tA tY inferInstance hA v (g, p) a
      _ = g p a := congrArg (fun b : B => b a)
        (@ContinuousMap.compactlyGeneratedCurryEquiv_symm_apply_apply.{u}
          T P B τT tP τB inferInstance hP (@ContinuousMap.id T τT) g p)
  refine @Homeomorph.mk (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
    (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
    (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
    (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
    (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
    (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
    (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
    (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y tP tA tY hP hA) ?_ ?_
  · have he : ⇑(curryOperator) =
        ⇑(ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y) := by
      funext h
      apply @ContinuousMap.ext P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA
        tY))
      intro p
      apply @ContinuousMap.ext A Y tA tY
      intro a
      exact (curryOperator_apply h p a).trans
        (ContinuousMap.compactlyGeneratedCurryEquiv_apply_apply.{u} P A Y h p a).symm
    have hc : @Continuous S T τS τT (⇑(curryOperator)) :=
      @ContinuousMap.continuous S T τS τT (curryOperator)
    exact Eq.mp (congrArg (@Continuous S T τS τT) he) hc
  · have he : ⇑(uncurryOperator) =
        ⇑(ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).symm := by
      funext g
      apply @ContinuousMap.ext (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY
      rintro ⟨p, a⟩
      exact (uncurryOperator_apply g p a).trans
        (ContinuousMap.compactlyGeneratedCurryEquiv_symm_apply_apply.{u} P A Y g p a).symm
    have hc : @Continuous T S τT τS (⇑(uncurryOperator)) :=
      @ContinuousMap.continuous T S τT τS (uncurryOperator)
    exact Eq.mp (congrArg (@Continuous T S τT τS) he) hc

/-- The whole underlying equivalence is the scalar currying equivalence. -/
@[simp]
theorem compactlyGeneratedCurry_toEquiv :
    (@Homeomorph.toEquiv (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)) =
      ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y := rfl

/-- The inverse retains the whole scalar inverse equivalence. -/
@[simp]
theorem compactlyGeneratedCurry_symm_toEquiv :
    (@Homeomorph.toEquiv (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
      × A) τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))) =
      (ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).symm := rfl

/-- The whole forward operator is scalar currying. -/
theorem coe_compactlyGeneratedCurry :
    ⇑(compactlyGeneratedCurry.{u} P A Y) = ContinuousMap.compactlyGeneratedCurry.{u} P A Y :=
  ContinuousMap.coe_compactlyGeneratedCurryEquiv.{u} P A Y

/-- The whole inverse operator is scalar uncurrying. -/
theorem coe_compactlyGeneratedCurry_symm :
    ⇑(@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)) =
      ContinuousMap.compactlyGeneratedUncurry.{u} P A Y :=
  ContinuousMap.coe_compactlyGeneratedCurryEquiv_symm.{u} P A Y

/-- The bundled forward map has the entire scalar equivalence as its function. -/
theorem coe_compactlyGeneratedCurry_toContinuousMap :
    ⇑(@ContinuousMap.mk (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@Homeomorph.toEquiv
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)) (@Homeomorph.continuous_toFun
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))) =
      ⇑(ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y) := rfl

/-- The bundled inverse map has the entire scalar inverse as its function. -/
theorem coe_compactlyGeneratedCurry_symm_toContinuousMap :
    ⇑(@ContinuousMap.mk (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
      × A) τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@Homeomorph.toEquiv (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
      × A) τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))) (@Homeomorph.continuous_toFun
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactlyGenerated.{u}
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y
      tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)))) =
      ⇑(ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).symm := rfl

/-- Applying the homeomorphism gives the whole scalar curried map. -/
theorem compactlyGeneratedCurry_apply (h : (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
  A) τPA) tY)) :
    compactlyGeneratedCurry.{u} P A Y h = ContinuousMap.compactlyGeneratedCurry.{u} P A Y h :=
  ContinuousMap.compactlyGeneratedCurryEquiv_apply.{u} P A Y h

/-- Applying the inverse gives the whole scalar uncurried map. -/
theorem compactlyGeneratedCurry_symm_apply (g : (@ContinuousMap P B tP (@compactlyGenerated.{u} B
  (@ContinuousMap.compactOpen A Y tA tY)))) :
    (@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)) g =
      ContinuousMap.compactlyGeneratedUncurry.{u} P A Y g :=
  ContinuousMap.compactlyGeneratedCurryEquiv_symm_apply.{u} P A Y g

/-- Every map is curried at every pair of original arguments. -/
@[simp]
theorem compactlyGeneratedCurry_apply_apply (h : (@ContinuousMap (P × A) Y (@compactlyGenerated.{u}
  (P × A) τPA) tY)) (p : P) (a : A) :
    compactlyGeneratedCurry.{u} P A Y h p a = h (p, a) :=
  ContinuousMap.compactlyGeneratedCurryEquiv_apply_apply.{u} P A Y h p a

/-- Every family is uncurried at every pair of original arguments. -/
@[simp]
theorem compactlyGeneratedCurry_symm_apply_apply (g : (@ContinuousMap P B tP
  (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (p : P) (a : A) :
    (@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)) g (p, a) = g p a :=
  ContinuousMap.compactlyGeneratedCurryEquiv_symm_apply_apply.{u} P A Y g p a

/-- The whole two-variable function of a curried map. -/
theorem coe_compactlyGeneratedCurry_apply (h : (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
  × A) τPA) tY)) :
    (fun p a => compactlyGeneratedCurry.{u} P A Y h p a) = fun p a => h (p, a) :=
  ContinuousMap.coe_compactlyGeneratedCurryEquiv_apply.{u} P A Y h

/-- The whole function of an uncurried family. -/
theorem coe_compactlyGeneratedCurry_symm_apply (g : (@ContinuousMap P B tP (@compactlyGenerated.{u}
  B (@ContinuousMap.compactOpen A Y tA tY)))) :
    ⇑((@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)) g) = fun q => g q.1 q.2 :=
  ContinuousMap.coe_compactlyGeneratedCurryEquiv_symm_apply.{u} P A Y g

/-- The inverse followed by the forward map is the bundled identity. -/
@[simp]
theorem compactlyGeneratedCurry_comp_symm :
    @ContinuousMap.comp (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
      × A) τPA) tY) (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A
      Y tA tY))) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@ContinuousMap.mk
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y tP tA tY hP hA)
      (@Homeomorph.continuous_toFun
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))) (@ContinuousMap.mk (@ContinuousMap P B
      tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap (P × A)
      Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y
      tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y tP tA tY hP hA).symm
      (@Homeomorph.continuous_toFun
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactlyGenerated.{u}
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y
      tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)))) =
      @ContinuousMap.id (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u} (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A
        Y tA tY)))) := by
  apply DFunLike.ext
  intro g
  change ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y
    ((ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).symm g) = g
  exact (ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).apply_symm_apply g

/-- The forward followed by the inverse map is the bundled identity. -/
@[simp]
theorem compactlyGeneratedCurry_symm_comp :
    @ContinuousMap.comp (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@ContinuousMap.mk (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
      × A) τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y tP tA tY hP hA).symm
      (@Homeomorph.continuous_toFun
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactlyGenerated.{u}
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y
      tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)))) (@ContinuousMap.mk (@ContinuousMap (P ×
      A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP (@compactlyGenerated.{u}
      B (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u} (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y
      tA tY))))
      (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y tP tA tY hP hA)
      (@Homeomorph.continuous_toFun
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))) =
      @ContinuousMap.id (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) := by
  apply DFunLike.ext
  intro h
  change (ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).symm
    (ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y h) = h
  exact (ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).symm_apply_apply h

/-- Forgetting the right outer refinement preserves the whole scalar operator.
This does not assert continuity between the two unrefined operator spaces. -/
theorem coe_compactlyGeneratedCurry_counit :
    ⇑(@ContinuousMap.comp (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
      (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y
      tA tY)))
      (@ContinuousMap.compactlyGeneratedCounit.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@ContinuousMap.mk
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u}
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@Homeomorph.toEquiv
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u}
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
        (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)) (@Homeomorph.continuous_toFun
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@compactlyGenerated.{u}
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
        (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)))) =
        ⇑(ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y) ∘
          ⇑(@ContinuousMap.compactlyGeneratedCounit.{u} (@ContinuousMap (P × A) Y
            (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
            (@compactlyGenerated.{u} (P × A) τPA) tY)) := by
  funext h
  let τB : TopologicalSpace B :=
    @compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)
  let S := @ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY
  let T := @ContinuousMap P B tP τB
  change (@ContinuousMap.compactlyGeneratedCounit.{u} T
    (@ContinuousMap.compactOpen P B tP τB))
      (ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y h) =
    ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y
      ((@ContinuousMap.compactlyGeneratedCounit.{u} S
        (@ContinuousMap.compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) h)
  rw [ContinuousMap.compactlyGeneratedCounit_apply,
    ContinuousMap.compactlyGeneratedCounit_apply]

/-- Forgetting the left outer refinement preserves the whole scalar inverse. -/
theorem coe_compactlyGeneratedCurry_symm_counit :
    ⇑(@ContinuousMap.comp (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
      × A) τPA) tY) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
      (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
      (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
      (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (@ContinuousMap.compactlyGeneratedCounit.{u} (@ContinuousMap (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY)) (@ContinuousMap.mk (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap (P × A)
        Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A
        Y tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
        A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@Homeomorph.toEquiv (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u}
        (P × A) τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
        (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
        (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))) (@Homeomorph.continuous_toFun
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactlyGenerated.{u}
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A
        Y tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
        A) τPA) tY) (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
        (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap.compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@ContinuousMap.compactOpen A Y tA tY))) (@ContinuousMap.compactOpen P B tP
        (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))))
        (@compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))))) =
        ⇑(ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).symm ∘
          ⇑(@ContinuousMap.compactlyGeneratedCounit.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)))
            (@ContinuousMap.compactOpen P B tP (@compactlyGenerated.{u} B
            (@ContinuousMap.compactOpen A Y tA tY)))) := by
  funext g
  let τB : TopologicalSpace B :=
    @compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY)
  let S := @ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY
  let T := @ContinuousMap P B tP τB
  change (@ContinuousMap.compactlyGeneratedCounit.{u} S
    (@ContinuousMap.compactOpen (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY))
      ((ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).symm g) =
    (ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y).symm
      ((@ContinuousMap.compactlyGeneratedCounit.{u} T
        (@ContinuousMap.compactOpen P B tP τB)) g)
  rw [ContinuousMap.compactlyGeneratedCounit_apply,
    ContinuousMap.compactlyGeneratedCounit_apply]

/-- On an ordinary product map this homeomorphism agrees with ordinary currying
and the canonical lift to the refined argument mapping space. -/
theorem compactlyGeneratedCurry_curry (h : C(P × A, Y)) :
    compactlyGeneratedCurry.{u} P A Y
        (@ContinuousMap.comp (P × A) (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) τPA tY h
          (@ContinuousMap.compactlyGeneratedCounit.{u} (P × A) τPA)) =
      @ContinuousMap.mk P B tP (@compactlyGenerated.{u} B (@ContinuousMap.compactOpen A Y tA tY))
        (@ContinuousMap.toFun P B tP (@ContinuousMap.compactOpen A Y tA tY) h.curry)
        ((continuous_to_compactlyGenerated_iff (tZ := tP)
          (tX := @ContinuousMap.compactOpen A Y tA tY) h.curry).2
            (@ContinuousMap.continuous P B tP (@ContinuousMap.compactOpen A Y tA tY)
              h.curry)) :=
  ContinuousMap.compactlyGeneratedCurryEquiv_curry.{u} P A Y h

end Curry

end Homeomorph

namespace ContinuousMap

private theorem refinedPrePostcomp_id (X : Type x) (Z : Type z)
    [tX : TopologicalSpace X] [tZ : TopologicalSpace Z] :
    @compactlyGeneratedMap.{u} C(X, Z) C(X, Z)
        (@compactOpen X Z tX tZ) (@compactOpen X Z tX tZ)
        (@ContinuousMap.comp C(X, Z) C(X, Z) C(X, Z)
          (@compactOpen X Z tX tZ) (@compactOpen X Z tX tZ) (@compactOpen X Z tX tZ)
          (postcompContinuousMap (A := X) (tA := tX) (tY := tZ) (tZ := tZ)
            (@ContinuousMap.id Z tZ))
          (precompContinuousMap (tA := tX) (tB := tX) (Y := Z) (tY := tZ)
            (@ContinuousMap.id X tX))) =
      @ContinuousMap.id C(X, Z)
        (@compactlyGenerated.{u} C(X, Z) (@compactOpen X Z tX tZ)) := by
  rw [postcompContinuousMap_id, precompContinuousMap_id]
  have hcomp :
      @ContinuousMap.comp C(X, Z) C(X, Z) C(X, Z)
        (@compactOpen X Z tX tZ) (@compactOpen X Z tX tZ) (@compactOpen X Z tX tZ)
        (@ContinuousMap.id C(X, Z) (@compactOpen X Z tX tZ))
        (@ContinuousMap.id C(X, Z) (@compactOpen X Z tX tZ)) =
      @ContinuousMap.id C(X, Z) (@compactOpen X Z tX tZ) := by
    apply @ContinuousMap.ext C(X, Z) C(X, Z)
      (@compactOpen X Z tX tZ) (@compactOpen X Z tX tZ)
    intro h
    simp only [ContinuousMap.comp_apply, ContinuousMap.id_apply]
  rw [hcomp]
  apply compactlyGeneratedMap_id

private theorem refinedPrePostcomp_comp
    {X : Type x} {X' : Type x'} {X'' : Type x''}
    {Z : Type z} {Z' : Type z'} {Z'' : Type z''}
    [tX : TopologicalSpace X] [tX' : TopologicalSpace X'] [tX'' : TopologicalSpace X'']
    [tZ : TopologicalSpace Z] [tZ' : TopologicalSpace Z'] [tZ'' : TopologicalSpace Z'']
    (f : C(X', X)) (f' : C(X'', X')) (k : C(Z, Z')) (k' : C(Z', Z'')) :
    @compactlyGeneratedMap.{u} C(X, Z) C(X'', Z'')
        (@compactOpen X Z tX tZ) (@compactOpen X'' Z'' tX'' tZ'')
        (@ContinuousMap.comp C(X, Z) C(X'', Z) C(X'', Z'')
          (@compactOpen X Z tX tZ) (@compactOpen X'' Z tX'' tZ)
          (@compactOpen X'' Z'' tX'' tZ'')
          (postcompContinuousMap (A := X'') (tA := tX'') (tY := tZ) (tZ := tZ'')
            (@ContinuousMap.comp Z Z' Z'' tZ tZ' tZ'' k' k))
          (precompContinuousMap (tA := tX) (tB := tX'') (Y := Z) (tY := tZ)
            (@ContinuousMap.comp X'' X' X tX'' tX' tX f f'))) =
      @ContinuousMap.comp C(X, Z) C(X', Z') C(X'', Z'')
        (@compactlyGenerated.{u} C(X, Z) (@compactOpen X Z tX tZ))
        (@compactlyGenerated.{u} C(X', Z') (@compactOpen X' Z' tX' tZ'))
        (@compactlyGenerated.{u} C(X'', Z'') (@compactOpen X'' Z'' tX'' tZ''))
        (@compactlyGeneratedMap.{u} C(X', Z') C(X'', Z'')
          (@compactOpen X' Z' tX' tZ') (@compactOpen X'' Z'' tX'' tZ'')
          (@ContinuousMap.comp C(X', Z') C(X'', Z') C(X'', Z'')
            (@compactOpen X' Z' tX' tZ') (@compactOpen X'' Z' tX'' tZ')
            (@compactOpen X'' Z'' tX'' tZ'')
            (postcompContinuousMap (A := X'') (tA := tX'') (tY := tZ') (tZ := tZ'') k')
            (precompContinuousMap (tA := tX') (tB := tX'') (Y := Z') (tY := tZ') f')))
        (@compactlyGeneratedMap.{u} C(X, Z) C(X', Z')
          (@compactOpen X Z tX tZ) (@compactOpen X' Z' tX' tZ')
          (@ContinuousMap.comp C(X, Z) C(X', Z) C(X', Z')
            (@compactOpen X Z tX tZ) (@compactOpen X' Z tX' tZ)
            (@compactOpen X' Z' tX' tZ')
            (postcompContinuousMap (A := X') (tA := tX') (tY := tZ) (tZ := tZ') k)
            (precompContinuousMap (tA := tX) (tB := tX') (Y := Z) (tY := tZ) f))) := by
  rw [← compactlyGeneratedMap_comp]
  apply congrArg (@compactlyGeneratedMap.{u} C(X, Z) C(X'', Z'')
    (@compactOpen X Z tX tZ) (@compactOpen X'' Z'' tX'' tZ''))
  rw [postcompContinuousMap_comp, precompContinuousMap_comp]
  apply @ContinuousMap.ext C(X, Z) C(X'', Z'')
    (@compactOpen X Z tX tZ) (@compactOpen X'' Z'' tX'' tZ'')
  intro h
  apply @ContinuousMap.ext X'' Z'' tX'' tZ''
  intro q
  simp only [ContinuousMap.comp_apply, postcompContinuousMap_apply_apply,
    precompContinuousMap_apply_apply]

section Actions

variable {P : Type p} {A : Type a} {Y : Type y}
  {P' : Type p'} {A' : Type a'} {Y' : Type y'}
  [tP : TopologicalSpace P] [tA : TopologicalSpace A] [tY : TopologicalSpace Y]
  [tP' : TopologicalSpace P'] [tA' : TopologicalSpace A'] [tY' : TopologicalSpace Y']

local notation "B" => @ContinuousMap A Y tA tY
local notation "B'" => @ContinuousMap A' Y' tA' tY'

local notation "D" => @ContinuousMap A' Y tA' tY

/-- Simultaneous precomposition in both original factors and postcomposition in
the target, on the refined uncurried mapping space. -/
def compactlyGeneratedUncurriedMap (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y')) :
    @ContinuousMap (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      (@instTopologicalSpaceProd P A tP tA)) tY) (@ContinuousMap (P' × A') Y'
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P
      × A) (@instTopologicalSpaceProd P A tP tA)) tY)) (@compactlyGenerated.{u} (@ContinuousMap (P'
      × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
      (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A'
      tP' tA')) tY')) :=
  @compactlyGeneratedMap.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
    (@instTopologicalSpaceProd P A tP tA)) tY) (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u}
    (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@compactOpen (P × A) Y
    (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P' ×
    A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
    (@ContinuousMap.comp (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      (@instTopologicalSpaceProd P A tP tA)) tY) (@ContinuousMap (P' × A') Y
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY)
      (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P'
      A' tP' tA')) tY') (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A)
      (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P' × A') Y (@compactlyGenerated.{u}
      (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY) (@compactOpen (P' × A') Y'
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
      (postcompContinuousMap (A := P' × A') (tA := (@compactlyGenerated.{u} (P' × A')
        (@instTopologicalSpaceProd P' A' tP' tA'))) (tY := tY) (tZ := tY') k)
      (precompContinuousMap (tA := (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A
        tP tA))) (tB := (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP'
        tA'))) (Y := Y) (tY := tY)
        (@compactlyGeneratedMap.{u} (P' × A') (P × A)
          (@instTopologicalSpaceProd P' A' tP' tA')
          (@instTopologicalSpaceProd P A tP tA)
          (@ContinuousMap.prodMap P' P A' A tP' tP tA' tA f j))))

/-- Simultaneous precomposition in the parameter and argument and postcomposition
in the target, on the refined curried mapping space. -/
def compactlyGeneratedCurriedMap (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y')) :
    @ContinuousMap (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
      (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
      (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
      tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
      (@compactlyGenerated.{u} (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen
      A' Y' tA' tY'))) (@compactOpen P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA'
      tY')))) :=
  @compactlyGeneratedMap.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
    tY))) (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
    (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P' B'
    tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
    (@ContinuousMap.comp (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
      tY))) (@ContinuousMap P' B tP' (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
      (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
      (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P' B
      tP' (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P' B' tP'
      (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
      (postcompContinuousMap (A := P') (tA := tP') (tY := (@compactlyGenerated.{u} B (@compactOpen A
        Y tA tY))) (tZ := (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
        (@compactlyGeneratedMap.{u} B B' (@compactOpen A Y tA tY)
          (@compactOpen A' Y' tA' tY')
          (@ContinuousMap.comp B D B' (@compactOpen A Y tA tY)
            (@compactOpen A' Y tA' tY) (@compactOpen A' Y' tA' tY')
            (postcompContinuousMap (A := A') (tA := tA') (tY := tY) (tZ := tY') k)
            (precompContinuousMap (tA := tA) (tB := tA') (Y := Y) (tY := tY) j))))
      (precompContinuousMap (tA := tP) (tB := tP') (Y := B) (tY := (@compactlyGenerated.{u} B
        (@compactOpen A Y tA tY))) f))

/-- The uncurried action retains its whole pre/postcomposition formula. -/
theorem compactlyGeneratedUncurriedMap_apply
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y')) (h : (@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)) :
    compactlyGeneratedUncurriedMap.{u} f j k h =
      @ContinuousMap.comp (P' × A') Y Y' (@compactlyGenerated.{u} (P' × A')
        (@instTopologicalSpaceProd P' A' tP' tA')) tY tY' k
        (@ContinuousMap.comp (P' × A') (P × A) Y (@compactlyGenerated.{u} (P' × A')
          (@instTopologicalSpaceProd P' A' tP' tA')) (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY h
          (@compactlyGeneratedMap.{u} (P' × A') (P × A)
            (@instTopologicalSpaceProd P' A' tP' tA')
            (@instTopologicalSpaceProd P A tP tA)
            (@ContinuousMap.prodMap P' P A' A tP' tP tA' tA f j))) := by
  simp only [compactlyGeneratedUncurriedMap, compactlyGeneratedMap_apply,
    ContinuousMap.comp_apply, postcompContinuousMap_apply, precompContinuousMap_apply]

/-- The curried action retains the whole refined inner action. -/
theorem compactlyGeneratedCurriedMap_apply
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y')) (g : (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) :
    compactlyGeneratedCurriedMap.{u} f j k g =
      @ContinuousMap.comp P' B B' tP' (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))
        (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))
        (@compactlyGeneratedMap.{u} B B' (@compactOpen A Y tA tY)
          (@compactOpen A' Y' tA' tY')
          (@ContinuousMap.comp B D B' (@compactOpen A Y tA tY)
            (@compactOpen A' Y tA' tY) (@compactOpen A' Y' tA' tY')
            (postcompContinuousMap (A := A') (tA := tA') (tY := tY) (tZ := tY') k)
            (precompContinuousMap (tA := tA) (tB := tA') (Y := Y) (tY := tY) j)))
        (@ContinuousMap.comp P' P B tP' tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)) g f)
          := by
  simp only [compactlyGeneratedCurriedMap, compactlyGeneratedMap_apply,
    ContinuousMap.comp_apply, postcompContinuousMap_apply, precompContinuousMap_apply]

/-- Every value of the uncurried three-variable action. -/
@[simp]
theorem compactlyGeneratedUncurriedMap_apply_apply
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y')) (h : (@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)) (p : P') (a : A')
      :
    compactlyGeneratedUncurriedMap.{u} f j k h (p, a) = k (h (f p, j a)) := by
  have hprod : (@ContinuousMap.prodMap P' P A' A tP' tP tA' tA f j) (p, a) =
      (f p, j a) := rfl
  simp only [compactlyGeneratedUncurriedMap_apply, ContinuousMap.comp_apply,
    compactlyGeneratedMap_apply, hprod]

/-- Every value of the curried three-variable action. -/
@[simp]
theorem compactlyGeneratedCurriedMap_apply_apply
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y')) (g : (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) (p : P') (a : A') :
    compactlyGeneratedCurriedMap.{u} f j k g p a = k (g (f p) (j a)) := by
  simp only [compactlyGeneratedCurriedMap_apply, ContinuousMap.comp_apply,
    compactlyGeneratedMap_apply, postcompContinuousMap_apply_apply,
    precompContinuousMap_apply_apply]

/-- The uncurried action of three identities is the whole identity map. -/
@[simp]
theorem compactlyGeneratedUncurriedMap_id :
    compactlyGeneratedUncurriedMap.{u} (@ContinuousMap.id P tP)
        (@ContinuousMap.id A tA) (@ContinuousMap.id Y tY) = @ContinuousMap.id (@ContinuousMap (P ×
          A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)) := by
  have hp : @ContinuousMap.prodMap P P A A tP tP tA tA
      (@ContinuousMap.id P tP) (@ContinuousMap.id A tA) =
      @ContinuousMap.id (P × A) (@instTopologicalSpaceProd P A tP tA) := by
    apply DFunLike.ext
    intro q
    rfl
  unfold compactlyGeneratedUncurriedMap
  rw [hp, compactlyGeneratedMap_id]
  exact @refinedPrePostcomp_id.{u} (P × A) Y (@compactlyGenerated.{u} (P × A)
    (@instTopologicalSpaceProd P A tP tA)) tY

/-- The curried action of three identities is the whole identity map. -/
@[simp]
theorem compactlyGeneratedCurriedMap_id :
    compactlyGeneratedCurriedMap.{u} (@ContinuousMap.id P tP)
        (@ContinuousMap.id A tA) (@ContinuousMap.id Y tY) = @ContinuousMap.id (@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactlyGenerated.{u}
          (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen
          P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) := by
  unfold compactlyGeneratedCurriedMap
  rw [@refinedPrePostcomp_id.{u} A Y tA tY]
  exact @refinedPrePostcomp_id.{u} P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))

variable {P'' : Type p''} {A'' : Type a''} {Y'' : Type y''}
  [tP'' : TopologicalSpace P''] [tA'' : TopologicalSpace A''] [tY'' : TopologicalSpace Y'']

local notation "B''" => @ContinuousMap A'' Y'' tA'' tY''

/-- The uncurried action is contravariant in both factors and covariant in the target. -/
theorem compactlyGeneratedUncurriedMap_comp
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y'))
    (f' : C(P'', P')) (j' : C(A'', A')) (k' : C(Y', Y'')) :
    compactlyGeneratedUncurriedMap.{u}
        (@ContinuousMap.comp P'' P' P tP'' tP' tP f f')
        (@ContinuousMap.comp A'' A' A tA'' tA' tA j j')
        (@ContinuousMap.comp Y Y' Y'' tY tY' tY'' k' k) =
      @ContinuousMap.comp (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
        (@instTopologicalSpaceProd P A tP tA)) tY) (@ContinuousMap (P' × A') Y'
        (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
        (@ContinuousMap (P'' × A'') Y'' (@compactlyGenerated.{u} (P'' × A'')
        (@instTopologicalSpaceProd P'' A'' tP'' tA'')) tY'') (@compactlyGenerated.{u}
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP
        tA)) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd
        P A tP tA)) tY)) (@compactlyGenerated.{u} (@ContinuousMap (P' × A') Y'
        (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
        (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P'
        A' tP' tA')) tY')) (@compactlyGenerated.{u} (@ContinuousMap (P'' × A'') Y''
        (@compactlyGenerated.{u} (P'' × A'') (@instTopologicalSpaceProd P'' A'' tP'' tA'')) tY'')
        (@compactOpen (P'' × A'') Y'' (@compactlyGenerated.{u} (P'' × A'')
        (@instTopologicalSpaceProd P'' A'' tP'' tA'')) tY''))
        (compactlyGeneratedUncurriedMap.{u} f' j' k')
        (compactlyGeneratedUncurriedMap.{u} f j k) := by
  have hp :
      @ContinuousMap.prodMap P'' P A'' A tP'' tP tA'' tA
        (@ContinuousMap.comp P'' P' P tP'' tP' tP f f')
        (@ContinuousMap.comp A'' A' A tA'' tA' tA j j') =
      @ContinuousMap.comp (P'' × A'') (P' × A') (P × A)
        (@instTopologicalSpaceProd P'' A'' tP'' tA'')
        (@instTopologicalSpaceProd P' A' tP' tA') (@instTopologicalSpaceProd P A tP tA)
        (@ContinuousMap.prodMap P' P A' A tP' tP tA' tA f j)
        (@ContinuousMap.prodMap P'' P' A'' A' tP'' tP' tA'' tA' f' j') := by
    apply @ContinuousMap.ext (P'' × A'') (P × A)
      (@instTopologicalSpaceProd P'' A'' tP'' tA'') (@instTopologicalSpaceProd P A tP tA)
    intro q
    have hprod (r : P' × A') :
        (@ContinuousMap.prodMap P' P A' A tP' tP tA' tA f j) r =
          (f r.1, j r.2) := rfl
    have hprod' :
        (@ContinuousMap.prodMap P'' P' A'' A' tP'' tP' tA'' tA' f' j') q =
          (f' q.1, j' q.2) := rfl
    have hprodComp :
        (@ContinuousMap.prodMap P'' P A'' A tP'' tP tA'' tA
          (@ContinuousMap.comp P'' P' P tP'' tP' tP f f')
          (@ContinuousMap.comp A'' A' A tA'' tA' tA j j')) q =
        ((@ContinuousMap.comp P'' P' P tP'' tP' tP f f') q.1,
          (@ContinuousMap.comp A'' A' A tA'' tA' tA j j') q.2) := rfl
    simp only [ContinuousMap.comp_apply, hprod, hprod', hprodComp]
  have hq :
      @compactlyGeneratedMap.{u} (P'' × A'') (P × A)
        (@instTopologicalSpaceProd P'' A'' tP'' tA'') (@instTopologicalSpaceProd P A tP tA)
        (@ContinuousMap.prodMap P'' P A'' A tP'' tP tA'' tA
          (@ContinuousMap.comp P'' P' P tP'' tP' tP f f')
          (@ContinuousMap.comp A'' A' A tA'' tA' tA j j')) =
      @ContinuousMap.comp (P'' × A'') (P' × A') (P × A) (@compactlyGenerated.{u} (P'' × A'')
        (@instTopologicalSpaceProd P'' A'' tP'' tA'')) (@compactlyGenerated.{u} (P' × A')
        (@instTopologicalSpaceProd P' A' tP' tA')) (@compactlyGenerated.{u} (P × A)
        (@instTopologicalSpaceProd P A tP tA))
        (@compactlyGeneratedMap.{u} (P' × A') (P × A)
          (@instTopologicalSpaceProd P' A' tP' tA') (@instTopologicalSpaceProd P A tP tA)
          (@ContinuousMap.prodMap P' P A' A tP' tP tA' tA f j))
        (@compactlyGeneratedMap.{u} (P'' × A'') (P' × A')
          (@instTopologicalSpaceProd P'' A'' tP'' tA'')
          (@instTopologicalSpaceProd P' A' tP' tA')
          (@ContinuousMap.prodMap P'' P' A'' A' tP'' tP' tA'' tA' f' j')) := by
    rw [hp]
    apply compactlyGeneratedMap_comp
  unfold compactlyGeneratedUncurriedMap
  rw [hq]
  exact @refinedPrePostcomp_comp.{u} (P × A) (P' × A') (P'' × A'') Y Y' Y''
    (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) (@compactlyGenerated.{u}
      (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) (@compactlyGenerated.{u} (P'' × A'')
      (@instTopologicalSpaceProd P'' A'' tP'' tA'')) tY tY' tY''
    (@compactlyGeneratedMap.{u} (P' × A') (P × A)
      (@instTopologicalSpaceProd P' A' tP' tA') (@instTopologicalSpaceProd P A tP tA)
      (@ContinuousMap.prodMap P' P A' A tP' tP tA' tA f j))
    (@compactlyGeneratedMap.{u} (P'' × A'') (P' × A')
      (@instTopologicalSpaceProd P'' A'' tP'' tA'')
      (@instTopologicalSpaceProd P' A' tP' tA')
      (@ContinuousMap.prodMap P'' P' A'' A' tP'' tP' tA'' tA' f' j')) k k'

/-- The curried action has the same simultaneous composition coherence. -/
theorem compactlyGeneratedCurriedMap_comp
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y'))
    (f' : C(P'', P')) (j' : C(A'', A')) (k' : C(Y', Y'')) :
    compactlyGeneratedCurriedMap.{u}
        (@ContinuousMap.comp P'' P' P tP'' tP' tP f f')
        (@ContinuousMap.comp A'' A' A tA'' tA' tA j j')
        (@ContinuousMap.comp Y Y' Y'' tY tY' tY'' k' k) =
      @ContinuousMap.comp (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
        tY))) (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
        (@ContinuousMap P'' B'' tP'' (@compactlyGenerated.{u} B'' (@compactOpen A'' Y'' tA'' tY'')))
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
        tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
        (@compactlyGenerated.{u} (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen
        A' Y' tA' tY'))) (@compactOpen P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA'
        tY')))) (@compactlyGenerated.{u} (@ContinuousMap P'' B'' tP'' (@compactlyGenerated.{u} B''
        (@compactOpen A'' Y'' tA'' tY''))) (@compactOpen P'' B'' tP'' (@compactlyGenerated.{u} B''
        (@compactOpen A'' Y'' tA'' tY''))))
        (compactlyGeneratedCurriedMap.{u} f' j' k')
        (compactlyGeneratedCurriedMap.{u} f j k) := by
  unfold compactlyGeneratedCurriedMap
  rw [@refinedPrePostcomp_comp.{u} A A' A'' Y Y' Y'' tA tA' tA'' tY tY' tY'' j j' k k']
  exact @refinedPrePostcomp_comp.{u} P P' P'' B B' B'' tP tP' tP'' (@compactlyGenerated.{u} B
    (@compactOpen A Y tA tY)) (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))
    (@compactlyGenerated.{u} B'' (@compactOpen A'' Y'' tA'' tY'')) f f'
    (@compactlyGeneratedMap.{u} B B' (@compactOpen A Y tA tY)
      (@compactOpen A' Y' tA' tY')
      (@ContinuousMap.comp B D B' (@compactOpen A Y tA tY)
        (@compactOpen A' Y tA' tY) (@compactOpen A' Y' tA' tY')
        (postcompContinuousMap (A := A') (tA := tA') (tY := tY) (tZ := tY') k)
        (precompContinuousMap (tA := tA) (tB := tA') (Y := Y) (tY := tY) j)))
    (@compactlyGeneratedMap.{u} B' B'' (@compactOpen A' Y' tA' tY')
      (@compactOpen A'' Y'' tA'' tY'')
      (@ContinuousMap.comp B' (@ContinuousMap A'' Y' tA'' tY') B''
        (@compactOpen A' Y' tA' tY') (@compactOpen A'' Y' tA'' tY')
        (@compactOpen A'' Y'' tA'' tY'')
        (postcompContinuousMap (A := A'') (tA := tA'') (tY := tY') (tZ := tY'') k')
        (precompContinuousMap (tA := tA') (tB := tA'') (Y := Y') (tY := tY') j')))

variable [UCompactlyGeneratedSpace.{u} P] [UCompactlyGeneratedSpace.{u} A]
  [UCompactlyGeneratedSpace.{u} P'] [UCompactlyGeneratedSpace.{u} A']

/-- Currying intertwines the three simultaneous bundled actions. -/
theorem compactlyGeneratedCurry_naturality
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y')) :
    @ContinuousMap.comp (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      (@instTopologicalSpaceProd P A tP tA)) tY) (@ContinuousMap (P' × A') Y'
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
      (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
      (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P
      × A) (@instTopologicalSpaceProd P A tP tA)) tY)) (@compactlyGenerated.{u} (@ContinuousMap (P'
      × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
      (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A'
      tP' tA')) tY')) (@compactlyGenerated.{u} (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B'
      (@compactOpen A' Y' tA' tY'))) (@compactOpen P' B' tP' (@compactlyGenerated.{u} B'
      (@compactOpen A' Y' tA' tY')))) (@ContinuousMap.mk (@ContinuousMap (P' × A') Y'
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
      (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
      (@compactlyGenerated.{u} (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@compactOpen (P' × A') Y'
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY'))
      (@compactlyGenerated.{u} (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen
      A' Y' tA' tY'))) (@compactOpen P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA'
      tY')))) (@Homeomorph.toEquiv (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@ContinuousMap P' B' tP'
      (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))) (@compactlyGenerated.{u}
      (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P'
      A' tP' tA')) tY') (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY')) (@compactlyGenerated.{u} (@ContinuousMap P'
      B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))) (@compactOpen P' B' tP'
      (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))))
      (@Homeomorph.compactlyGeneratedCurry.{u} P' A' Y' tP' tA' tY' inferInstance inferInstance))
      (@Homeomorph.continuous_toFun (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@ContinuousMap P' B' tP'
      (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))) (@compactlyGenerated.{u}
      (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P'
      A' tP' tA')) tY') (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY')) (@compactlyGenerated.{u} (@ContinuousMap P'
      B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))) (@compactOpen P' B' tP'
      (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))))
      (@Homeomorph.compactlyGeneratedCurry.{u} P' A' Y' tP' tA' tY' inferInstance inferInstance)))
        (compactlyGeneratedUncurriedMap.{u} f j k) =
      @ContinuousMap.comp (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
        (@instTopologicalSpaceProd P A tP tA)) tY) (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@compactOpen A Y tA tY))) (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B'
        (@compactOpen A' Y' tA' tY'))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
        (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P
        × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY))
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
        tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
        (@compactlyGenerated.{u} (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen
        A' Y' tA' tY'))) (@compactOpen P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA'
        tY'))))
        (compactlyGeneratedCurriedMap.{u} f j k) (@ContinuousMap.mk (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)
          (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY))
          (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
          Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
          (@Homeomorph.toEquiv (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY) (@ContinuousMap P B tP (@compactlyGenerated.{u}
          B (@compactOpen A Y tA tY))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen
          (P × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY))
          (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
          Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
          (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY inferInstance inferInstance))
          (@Homeomorph.continuous_toFun (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY) (@ContinuousMap P B tP (@compactlyGenerated.{u}
          B (@compactOpen A Y tA tY))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen
          (P × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY))
          (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
          Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
          (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY inferInstance inferInstance))) :=
          by
  apply @ContinuousMap.ext (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
    (@instTopologicalSpaceProd P A tP tA)) tY) (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B'
    (@compactOpen A' Y' tA' tY'))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
    (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P ×
    A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY))
    (@compactlyGenerated.{u} (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A'
    Y' tA' tY'))) (@compactOpen P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA'
    tY'))))
  intro h
  apply @ContinuousMap.ext P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))
  intro p
  apply @ContinuousMap.ext A' Y' tA' tY'
  intro a
  change Homeomorph.compactlyGeneratedCurry.{u} P' A' Y'
      (compactlyGeneratedUncurriedMap.{u} f j k h) p a =
    compactlyGeneratedCurriedMap.{u} f j k
      (Homeomorph.compactlyGeneratedCurry.{u} P A Y h) p a
  rw [Homeomorph.compactlyGeneratedCurry_apply_apply.{u},
    compactlyGeneratedUncurriedMap_apply_apply.{u}, compactlyGeneratedCurriedMap_apply_apply.{u},
    Homeomorph.compactlyGeneratedCurry_apply_apply.{u}]

/-- Uncurrying intertwines the same three simultaneous bundled actions. -/
theorem compactlyGeneratedCurry_symm_naturality
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y')) :
    @ContinuousMap.comp (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
      (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
      (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P'
      A' tP' tA')) tY') (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
      tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B'
      (@compactOpen A' Y' tA' tY'))) (@compactOpen P' B' tP' (@compactlyGenerated.{u} B'
      (@compactOpen A' Y' tA' tY')))) (@compactlyGenerated.{u} (@ContinuousMap (P' × A') Y'
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
      (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A'
      tP' tA')) tY')) (@ContinuousMap.mk (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B'
      (@compactOpen A' Y' tA' tY'))) (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@compactlyGenerated.{u} (@ContinuousMap P' B'
      tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))) (@compactOpen P' B' tP'
      (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))) (@compactlyGenerated.{u}
      (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P'
      A' tP' tA')) tY') (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY')) (@Homeomorph.toEquiv (@ContinuousMap P' B'
      tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))) (@ContinuousMap (P' × A') Y'
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
      (@compactlyGenerated.{u} (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen
      A' Y' tA' tY'))) (@compactOpen P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA'
      tY')))) (@compactlyGenerated.{u} (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' ×
      A') (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@compactOpen (P' × A') Y'
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY'))
      (@Homeomorph.symm (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@ContinuousMap P' B' tP'
      (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))) (@compactlyGenerated.{u}
      (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P'
      A' tP' tA')) tY') (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY')) (@compactlyGenerated.{u} (@ContinuousMap P'
      B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))) (@compactOpen P' B' tP'
      (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))))
      (@Homeomorph.compactlyGeneratedCurry.{u} P' A' Y' tP' tA' tY' inferInstance inferInstance)))
      (@Homeomorph.continuous_toFun (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B'
      (@compactOpen A' Y' tA' tY'))) (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@compactlyGenerated.{u} (@ContinuousMap P' B'
      tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY'))) (@compactOpen P' B' tP'
      (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))) (@compactlyGenerated.{u}
      (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P'
      A' tP' tA')) tY') (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY')) (@Homeomorph.symm (@ContinuousMap (P' × A')
      Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
      (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA' tY')))
      (@compactlyGenerated.{u} (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
      (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@compactOpen (P' × A') Y'
      (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY'))
      (@compactlyGenerated.{u} (@ContinuousMap P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen
      A' Y' tA' tY'))) (@compactOpen P' B' tP' (@compactlyGenerated.{u} B' (@compactOpen A' Y' tA'
      tY')))) (@Homeomorph.compactlyGeneratedCurry.{u} P' A' Y' tP' tA' tY' inferInstance
      inferInstance))))
        (compactlyGeneratedCurriedMap.{u} f j k) =
      @ContinuousMap.comp (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
        tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd
        P A tP tA)) tY) (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
        (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@compactlyGenerated.{u} (@ContinuousMap P B
        tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
        (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP
        tA)) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd
        P A tP tA)) tY)) (@compactlyGenerated.{u} (@ContinuousMap (P' × A') Y'
        (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY')
        (@compactOpen (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P'
        A' tP' tA')) tY'))
        (compactlyGeneratedUncurriedMap.{u} f j k) (@ContinuousMap.mk (@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)
          (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
          Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY))
          (@Homeomorph.toEquiv (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
          tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
          (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
          (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A
          tP tA)) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY)) (@Homeomorph.symm (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)
          (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY))
          (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
          Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
          (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY inferInstance inferInstance)))
          (@Homeomorph.continuous_toFun (@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
          (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
          (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A
          tP tA)) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY)) (@Homeomorph.symm (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY)
          (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A tP tA)) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY))
          (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
          Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
          (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY inferInstance inferInstance)))) :=
          by
  apply @ContinuousMap.ext (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
    tY))) (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd
    P' A' tP' tA')) tY') (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
    (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
    tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
    (@instTopologicalSpaceProd P' A' tP' tA')) tY') (@compactOpen (P' × A') Y'
    (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY'))
  intro g
  apply @ContinuousMap.ext (P' × A') Y' (@compactlyGenerated.{u} (P' × A')
    (@instTopologicalSpaceProd P' A' tP' tA')) tY'
  rintro ⟨p, a⟩
  change (@ContinuousMap.compactlyGeneratedCurryEquiv.{u} P' A' Y' tP' tA' tY'
      inferInstance inferInstance).symm (compactlyGeneratedCurriedMap.{u} f j k g) (p, a) =
    compactlyGeneratedUncurriedMap.{u} f j k
      ((@ContinuousMap.compactlyGeneratedCurryEquiv.{u} P A Y tP tA tY
        inferInstance inferInstance).symm g) (p, a)
  rw [ContinuousMap.compactlyGeneratedCurryEquiv_symm_apply_apply.{u},
    compactlyGeneratedCurriedMap_apply_apply.{u}, compactlyGeneratedUncurriedMap_apply_apply.{u},
    ContinuousMap.compactlyGeneratedCurryEquiv_symm_apply_apply.{u}]

end Actions

end ContinuousMap

namespace ContinuousMap

section Evaluation

variable (P : Type p) (A : Type a) (Y : Type y)
  [tP : TopologicalSpace P] [tA : TopologicalSpace A] [tY : TopologicalSpace Y]

local notation "τPA" => @instTopologicalSpaceProd P A tP tA

local notation "B" => @ContinuousMap A Y tA tY

/-- Flat evaluation of maps on the refined original product. Its domain is the
refinement of the product of the refined operator space and the original product. -/
def compactlyGeneratedCurryEval : @ContinuousMap ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u}
  (P × A) τPA) tY) × (P × A)) Y (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y
  (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P
  × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap
  (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
  (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA)) tY := by
  let τQ := @compactlyGenerated.{u} (P × A) τPA
  let F := @ContinuousMap (P × A) Y τQ tY
  let τF₀ := @compactOpen (P × A) Y τQ tY
  let τF := @compactlyGenerated.{u} F τF₀
  let τD := @compactlyGenerated.{u} (F × (P × A))
    (@instTopologicalSpaceProd F (P × A) τF τPA)
  let τR := @compactlyGenerated.{u} (F × (P × A))
    (@instTopologicalSpaceProd F (P × A) τF τQ)
  let τE := @compactlyGenerated.{u} (F × (P × A))
    (@instTopologicalSpaceProd F (P × A) τF₀ τQ)
  let r : @Homeomorph (F × (P × A)) (F × (P × A)) τR τD :=
    @Homeomorph.compactlyGeneratedProdRightComparison.{u} F (P × A) τF τPA
  let rInv : @ContinuousMap (F × (P × A)) (F × (P × A)) τD τR :=
    @ContinuousMap.mk (F × (P × A)) (F × (P × A)) τD τR
      (@Homeomorph.toEquiv (F × (P × A)) (F × (P × A)) τR τD r).symm
      (@Homeomorph.continuous_invFun (F × (P × A)) (F × (P × A)) τR τD r)
  let l : @Homeomorph (F × (P × A)) (F × (P × A)) τR τE :=
    @Homeomorph.compactlyGeneratedProdLeftComparison.{u} F (P × A) τF₀ τQ
  let lMap : @ContinuousMap (F × (P × A)) (F × (P × A)) τR τE :=
    @ContinuousMap.mk (F × (P × A)) (F × (P × A)) τR τE
      (@Homeomorph.toEquiv (F × (P × A)) (F × (P × A)) τR τE l)
      (@Homeomorph.continuous_toFun (F × (P × A)) (F × (P × A)) τR τE l)
  let e₀ : @ContinuousMap (F × (P × A)) Y τE tY :=
    @evalOfCompactlyGenerated.{u} (P × A) Y τQ tY
  let e : @ContinuousMap (F × (P × A)) Y τR tY :=
    @ContinuousMap.comp (F × (P × A)) (F × (P × A)) Y τR τE tY e₀ lMap
  let v : @ContinuousMap (F × (P × A)) Y τD tY :=
    @ContinuousMap.comp (F × (P × A)) (F × (P × A)) Y τD τR tY e rInv
  refine @ContinuousMap.mk (F × (P × A)) Y τD tY (fun q => q.1 q.2) ?_
  have hv : @ContinuousMap.toFun (F × (P × A)) Y τD tY v =
      (fun q => q.1 q.2) := by
    funext q
    have he (s : F × (P × A)) : e s = s.1 s.2 := by
      calc
        e s = e₀ (lMap s) := by rfl
        _ = e₀ s := congrArg (@ContinuousMap.toFun (F × (P × A)) Y τE tY e₀)
          (@Homeomorph.compactlyGeneratedProdLeftComparison_apply.{u}
            F (P × A) τF₀ τQ s)
        _ = s.1 s.2 := by rfl
    calc
      v q = e (rInv q) := by rfl
      _ = e q := congrArg (@ContinuousMap.toFun (F × (P × A)) Y τR tY e)
        (@Homeomorph.compactlyGeneratedProdRightComparison_symm_apply.{u}
          F (P × A) τF τPA q)
      _ = q.1 q.2 := he q
  exact Eq.mp (congrArg (@Continuous (F × (P × A)) Y τD tY) hv)
    (@ContinuousMap.continuous (F × (P × A)) Y τD tY v)

/-- Nested evaluation, constructed by evaluating the family and then its value.
Neither evaluation is asserted continuous on an unrefined ordinary product. -/
def compactlyGeneratedUncurryEval : @ContinuousMap ((@ContinuousMap P B tP (@compactlyGenerated.{u}
  B (@compactOpen A Y tA tY))) × (P × A)) Y (@compactlyGenerated.{u} ((@ContinuousMap P B tP
  (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd
  (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A)
  (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
  tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)) tY := by
  let τB₀ := @compactOpen A Y tA tY
  let τB := @compactlyGenerated.{u} B τB₀
  let F := @ContinuousMap P B tP τB
  let τF₀ := @compactOpen P B tP τB
  let τF := @compactlyGenerated.{u} F τF₀
  let τQ := @compactlyGenerated.{u} (P × A) τPA
  let τFP := @compactlyGenerated.{u} (F × P)
    (@instTopologicalSpaceProd F P τF tP)
  let τFP₀ := @compactlyGenerated.{u} (F × P)
    (@instTopologicalSpaceProd F P τF₀ tP)
  let τT := @compactlyGenerated.{u} ((F × P) × A)
    (@instTopologicalSpaceProd (F × P) A τFP tA)
  let τR := @compactlyGenerated.{u} (F × (P × A))
    (@instTopologicalSpaceProd F (P × A) τF τQ)
  let τD := @compactlyGenerated.{u} (F × (P × A))
    (@instTopologicalSpaceProd F (P × A) τF τPA)
  let τBA := @compactlyGenerated.{u} (B × A)
    (@instTopologicalSpaceProd B A τB tA)
  let τBA₀ := @compactlyGenerated.{u} (B × A)
    (@instTopologicalSpaceProd B A τB₀ tA)
  let lV : @Homeomorph (F × P) (F × P) τFP τFP₀ :=
    @Homeomorph.compactlyGeneratedProdLeftComparison.{u} F P τF₀ tP
  let lVMap : @ContinuousMap (F × P) (F × P) τFP τFP₀ :=
    @ContinuousMap.mk (F × P) (F × P) τFP τFP₀
      (@Homeomorph.toEquiv (F × P) (F × P) τFP τFP₀ lV)
      (@Homeomorph.continuous_toFun (F × P) (F × P) τFP τFP₀ lV)
  let v₀ : @ContinuousMap (F × P) B τFP₀ τB :=
    @evalOfCompactlyGenerated.{u} P B tP τB
  let v : @ContinuousMap (F × P) B τFP τB :=
    @ContinuousMap.comp (F × P) (F × P) B τFP τFP₀ τB v₀ lVMap
  let va : @ContinuousMap ((F × P) × A) (B × A) τT τBA :=
    @compactlyGeneratedMap.{u} ((F × P) × A) (B × A)
      (@instTopologicalSpaceProd (F × P) A τFP tA)
      (@instTopologicalSpaceProd B A τB tA)
      (@ContinuousMap.prodMap (F × P) B A A τFP τB tA tA v
        (@ContinuousMap.id A tA))
  let r : @Homeomorph ((F × P) × A) (F × (P × A)) τT τR :=
    @Homeomorph.compactlyGeneratedProdAssoc.{u} F P A τF tP tA
  let c : @Homeomorph (F × (P × A)) (F × (P × A)) τR τD :=
    @Homeomorph.compactlyGeneratedProdRightComparison.{u} F (P × A) τF τPA
  let rInv : @ContinuousMap (F × (P × A)) ((F × P) × A) τR τT :=
    @ContinuousMap.mk (F × (P × A)) ((F × P) × A) τR τT
      (@Homeomorph.toEquiv ((F × P) × A) (F × (P × A)) τT τR r).symm
      (@Homeomorph.continuous_invFun ((F × P) × A) (F × (P × A)) τT τR r)
  let cInv : @ContinuousMap (F × (P × A)) (F × (P × A)) τD τR :=
    @ContinuousMap.mk (F × (P × A)) (F × (P × A)) τD τR
      (@Homeomorph.toEquiv (F × (P × A)) (F × (P × A)) τR τD c).symm
      (@Homeomorph.continuous_invFun (F × (P × A)) (F × (P × A)) τR τD c)
  let reassoc : @ContinuousMap (F × (P × A)) ((F × P) × A) τD τT :=
    @ContinuousMap.comp (F × (P × A)) (F × (P × A)) ((F × P) × A)
      τD τR τT rInv cInv
  let lE : @Homeomorph (B × A) (B × A) τBA τBA₀ :=
    @Homeomorph.compactlyGeneratedProdLeftComparison.{u} B A τB₀ tA
  let lEMap : @ContinuousMap (B × A) (B × A) τBA τBA₀ :=
    @ContinuousMap.mk (B × A) (B × A) τBA τBA₀
      (@Homeomorph.toEquiv (B × A) (B × A) τBA τBA₀ lE)
      (@Homeomorph.continuous_toFun (B × A) (B × A) τBA τBA₀ lE)
  let e₀ : @ContinuousMap (B × A) Y τBA₀ tY :=
    @evalOfCompactlyGenerated.{u} A Y tA tY
  let e : @ContinuousMap (B × A) Y τBA tY :=
    @ContinuousMap.comp (B × A) (B × A) Y τBA τBA₀ tY e₀ lEMap
  let w : @ContinuousMap (F × (P × A)) Y τD tY :=
    @ContinuousMap.comp (F × (P × A)) (B × A) Y τD τBA tY e
      (@ContinuousMap.comp (F × (P × A)) ((F × P) × A) (B × A)
        τD τT τBA va reassoc)
  refine @ContinuousMap.mk (F × (P × A)) Y τD tY (fun q => q.1 q.2.1 q.2.2) ?_
  have hw : @ContinuousMap.toFun (F × (P × A)) Y τD tY w =
      (fun q => q.1 q.2.1 q.2.2) := by
    funext q
    have hv (s : F × P) : v s = s.1 s.2 := by
      calc
        v s = v₀ (lVMap s) := by rfl
        _ = v₀ s := congrArg (@ContinuousMap.toFun (F × P) B τFP₀ τB v₀)
          (@Homeomorph.compactlyGeneratedProdLeftComparison_apply.{u} F P τF₀ tP s)
        _ = s.1 s.2 := by rfl
    have he (s : B × A) : e s = s.1 s.2 := by
      calc
        e s = e₀ (lEMap s) := by rfl
        _ = e₀ s := congrArg (@ContinuousMap.toFun (B × A) Y τBA₀ tY e₀)
          (@Homeomorph.compactlyGeneratedProdLeftComparison_apply.{u} B A τB₀ tA s)
        _ = s.1 s.2 := by rfl
    have hback : @ContinuousMap.toFun (F × (P × A)) ((F × P) × A)
        τD τT reassoc q = ((q.1, q.2.1), q.2.2) := by
      change (@Homeomorph.toEquiv ((F × P) × A) (F × (P × A)) τT τR r).symm
        ((@Homeomorph.toEquiv (F × (P × A)) (F × (P × A)) τR τD c).symm q) =
          ((q.1, q.2.1), q.2.2)
      exact (congrArg
        (fun s : F × (P × A) =>
          (@Homeomorph.toEquiv ((F × P) × A) (F × (P × A)) τT τR r).symm s)
        (@Homeomorph.compactlyGeneratedProdRightComparison_symm_apply.{u}
          F (P × A) τF τPA q)).trans
        (@Homeomorph.compactlyGeneratedProdAssoc_symm_apply.{u}
          F P A τF tP tA q)
    have hva (s : (F × P) × A) :
        @ContinuousMap.toFun ((F × P) × A) (B × A) τT τBA va s =
          (v s.1, s.2) := by
      have hprod : (@ContinuousMap.prodMap (F × P) B A A τFP τB tA tA v
          (@ContinuousMap.id A tA)) s = (v s.1, s.2) := rfl
      calc
        @ContinuousMap.toFun ((F × P) × A) (B × A) τT τBA va s =
            @ContinuousMap.toFun ((F × P) × A) (B × A)
              (@instTopologicalSpaceProd (F × P) A τFP tA)
              (@instTopologicalSpaceProd B A τB tA)
              (@ContinuousMap.prodMap (F × P) B A A τFP τB tA tA v
                (@ContinuousMap.id A tA)) s := by rfl
        _ = (v s.1, s.2) := hprod
    calc
      w q = e (va (reassoc q)) := by rfl
      _ = e (va ((q.1, q.2.1), q.2.2)) :=
        congrArg (fun s : (F × P) × A => e (va s)) hback
      _ = e (v (q.1, q.2.1), q.2.2) :=
        congrArg (@ContinuousMap.toFun (B × A) Y τBA tY e) (hva _)
      _ = (v (q.1, q.2.1)) q.2.2 := he _
      _ = q.1 q.2.1 q.2.2 :=
        congrArg (fun b : B => b q.2.2) (hv (q.1, q.2.1))
  exact Eq.mp (congrArg (@Continuous (F × (P × A)) Y τD tY) hw)
    (@ContinuousMap.continuous (F × (P × A)) Y τD tY w)

/-- Flat evaluation preserves every original product value. -/
@[simp]
theorem compactlyGeneratedCurryEval_apply (q : (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
  × A) τPA) tY) × (P × A)) :
    compactlyGeneratedCurryEval.{u} P A Y q = q.1 q.2 := by
  rfl

/-- Nested evaluation preserves every value of every family. -/
@[simp]
theorem compactlyGeneratedUncurryEval_apply (q : (@ContinuousMap P B tP (@compactlyGenerated.{u} B
  (@compactOpen A Y tA tY))) × (P × A)) :
    compactlyGeneratedUncurryEval.{u} P A Y q = q.1 q.2.1 q.2.2 := by
  rfl

/-- The whole flat evaluation function on its refined product domain. -/
theorem coe_compactlyGeneratedCurryEval :
    ⇑(compactlyGeneratedCurryEval.{u} P A Y) = fun q => q.1 q.2 := by
  funext q
  exact compactlyGeneratedCurryEval_apply.{u} P A Y q

/-- The whole nested evaluation function on its refined product domain. -/
theorem coe_compactlyGeneratedUncurryEval :
    ⇑(compactlyGeneratedUncurryEval.{u} P A Y) = fun q => q.1 q.2.1 q.2.2 := by
  funext q
  exact compactlyGeneratedUncurryEval_apply.{u} P A Y q

/-- After the partial product comparison, flat evaluation is scalar uncurrying
of the identity of the refined uncurried mapping space. -/
theorem compactlyGeneratedCurryEval_scalar :
    @ContinuousMap.comp ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P ×
      A)) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A)) Y
      (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
      A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P
      × A) τPA) tY)) (@compactlyGenerated.{u} (P × A) τPA))) (@compactlyGenerated.{u}
      ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
      (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA)) tY
        (compactlyGeneratedCurryEval.{u} P A Y) (@ContinuousMap.mk ((@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A)) ((@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A)) (@compactlyGenerated.{u}
          ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
          (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P
          × A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
          (@compactlyGenerated.{u} (P × A) τPA))) (@compactlyGenerated.{u} ((@ContinuousMap (P × A)
          Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A)) (@instTopologicalSpaceProd
          (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A)
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA))
          (@Homeomorph.toEquiv ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
          × (P × A)) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
          (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u} (P × A) τPA)))
          (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA))
          (@Homeomorph.compactlyGeneratedProdRightComparison.{u} (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA)) (@Homeomorph.continuous_toFun
          ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
          ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
          (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u} (P × A) τPA)))
          (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA))
          (@Homeomorph.compactlyGeneratedProdRightComparison.{u} (@ContinuousMap (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap
          (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
          (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA))) =
      (@compactlyGeneratedCurryEquiv.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
        τPA) tY) (P × A) Y
        (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
          (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
          (@compactlyGenerated.{u} (P × A) τPA) tY inferInstance inferInstance).symm
          (@ContinuousMap.id (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))) := by
  apply @ContinuousMap.ext ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P
    × A)) Y (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
    τPA) tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y
    (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P ×
    A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u}
    (P × A) τPA) tY)) (@compactlyGenerated.{u} (P × A) τPA))) tY
  rintro ⟨h, p, a⟩
  let τQ := @compactlyGenerated.{u} (P × A) τPA
  let F := @ContinuousMap (P × A) Y τQ tY
  let τF := @compactlyGenerated.{u} F (@compactOpen (P × A) Y τQ tY)
  let τR := @compactlyGenerated.{u} (F × (P × A))
    (@instTopologicalSpaceProd F (P × A) τF τQ)
  let τD := @compactlyGenerated.{u} (F × (P × A))
    (@instTopologicalSpaceProd F (P × A) τF τPA)
  let r : @Homeomorph (F × (P × A)) (F × (P × A)) τR τD :=
    @Homeomorph.compactlyGeneratedProdRightComparison.{u} F (P × A) τF τPA
  change compactlyGeneratedCurryEval.{u} P A Y
    ((@Homeomorph.toEquiv (F × (P × A)) (F × (P × A)) τR τD r) (h, (p, a))) = _
  calc
    _ = compactlyGeneratedCurryEval.{u} P A Y (h, (p, a)) :=
      congrArg (fun q : F × (P × A) => compactlyGeneratedCurryEval.{u} P A Y q)
        (@Homeomorph.compactlyGeneratedProdRightComparison_apply.{u}
          F (P × A) τF τPA (h, (p, a)))
    _ = h (p, a) := compactlyGeneratedCurryEval_apply.{u} P A Y (h, (p, a))
    _ = _ :=
      (@compactlyGeneratedCurryEquiv_symm_apply_apply.{u} F (P × A) Y
        τF τQ tY inferInstance inferInstance (@ContinuousMap.id F τF) h (p, a)).symm

variable [hP : UCompactlyGeneratedSpace.{u} P] [hA : UCompactlyGeneratedSpace.{u} A]

/-- On the refined triple product, canonical nested evaluation is double scalar
uncurrying of the identity. All the intermediate product refinements are retained. -/
theorem compactlyGeneratedUncurryEval_assoc :
    @ContinuousMap.comp (((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
      tY))) × P) × A) ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
      × (P × A)) Y (@compactlyGenerated.{u} (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@compactOpen A Y tA tY))) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u}
      ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P)
      (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
      tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
      tA tY)))) tP)) tA)) (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u}
      B (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B
      tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)) tY
        (compactlyGeneratedUncurryEval.{u} P A Y)
        (@ContinuousMap.comp (((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
          tA tY))) × P) × A) ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
          tY))) × (P × A)) ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
          tY))) × (P × A))
          (@compactlyGenerated.{u} (((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY))) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u}
            ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P)
            (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) tP)) tA))
            (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
            (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            (@compactlyGenerated.{u} (P × A) τPA))) (@compactlyGenerated.{u} ((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A))
            (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)) (@ContinuousMap.mk
            ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A))
            ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A))
            (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
            (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            (@compactlyGenerated.{u} (P × A) τPA))) (@compactlyGenerated.{u} ((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A))
            (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)) (@Homeomorph.toEquiv
            ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A))
            ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A))
            (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
            (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            (@compactlyGenerated.{u} (P × A) τPA))) (@compactlyGenerated.{u} ((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A))
            (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA))
            (@Homeomorph.compactlyGeneratedProdRightComparison.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
            (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA))
            (@Homeomorph.continuous_toFun ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × (P × A)) ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × (P × A)) (@compactlyGenerated.{u} ((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A))
            (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) (@compactlyGenerated.{u} (P × A)
            τPA))) (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
            (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA))
            (@Homeomorph.compactlyGeneratedProdRightComparison.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
            (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)))
            (@ContinuousMap.mk (((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
            tA tY))) × P) × A) ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
            tA tY))) × (P × A)) (@compactlyGenerated.{u} (((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P) × A)
            (@instTopologicalSpaceProd ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u} ((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P) (@instTopologicalSpaceProd
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) P
            (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            tP)) tA)) (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
            (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            (@compactlyGenerated.{u} (P × A) τPA))) (@Homeomorph.toEquiv (((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P) × A) ((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A))
            (@compactlyGenerated.{u} (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u}
            ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P)
            (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) tP)) tA))
            (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
            (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            (@compactlyGenerated.{u} (P × A) τPA))) (@Homeomorph.compactlyGeneratedProdAssoc.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) P A
            (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            tP tA)) (@Homeomorph.continuous_toFun (((@ContinuousMap P B tP (@compactlyGenerated.{u}
            B (@compactOpen A Y tA tY))) × P) × A) ((@ContinuousMap P B tP (@compactlyGenerated.{u}
            B (@compactOpen A Y tA tY))) × (P × A)) (@compactlyGenerated.{u} (((@ContinuousMap P B
            tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P) × A)
            (@instTopologicalSpaceProd ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u} ((@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P) (@instTopologicalSpaceProd
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) P
            (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            tP)) tA)) (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
            (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            (@compactlyGenerated.{u} (P × A) τPA))) (@Homeomorph.compactlyGeneratedProdAssoc.{u}
            (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) P A
            (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            tP tA)))) =
      (@compactlyGeneratedCurryEquiv.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@compactOpen A Y tA tY))) × P) A Y
        (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
          Y tA tY))) × P) (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u}
          B (@compactOpen A Y tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP
          (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
          (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) tP)) tA tY inferInstance hA).symm
        ((@compactlyGeneratedCurryEquiv.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
          (@compactOpen A Y tA tY))) P B
          (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
            Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)) inferInstance hP).symm
            (@ContinuousMap.id (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
            tA tY))) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY)))))) := by
  apply @ContinuousMap.ext (((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
    tY))) × P) × A) Y (@compactlyGenerated.{u} (((@ContinuousMap P B tP (@compactlyGenerated.{u} B
    (@compactOpen A Y tA tY))) × P) × A) (@instTopologicalSpaceProd ((@ContinuousMap P B tP
    (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P) A (@compactlyGenerated.{u}
    ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × P)
    (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
    tA tY))) P (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
    (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
    tY)))) tP)) tA)) tY
  rintro ⟨⟨g, p⟩, a⟩
  let τB := @compactlyGenerated.{u} B (@compactOpen A Y tA tY)
  let F := @ContinuousMap P B tP τB
  let τF := @compactlyGenerated.{u} F (@compactOpen P B tP τB)
  let τQ := @compactlyGenerated.{u} (P × A) τPA
  let τFP := @compactlyGenerated.{u} (F × P)
    (@instTopologicalSpaceProd F P τF tP)
  let τT := @compactlyGenerated.{u} ((F × P) × A)
    (@instTopologicalSpaceProd (F × P) A τFP tA)
  let τR := @compactlyGenerated.{u} (F × (P × A))
    (@instTopologicalSpaceProd F (P × A) τF τQ)
  let τD := @compactlyGenerated.{u} (F × (P × A))
    (@instTopologicalSpaceProd F (P × A) τF τPA)
  let r : @Homeomorph ((F × P) × A) (F × (P × A)) τT τR :=
    @Homeomorph.compactlyGeneratedProdAssoc.{u} F P A τF tP tA
  let c : @Homeomorph (F × (P × A)) (F × (P × A)) τR τD :=
    @Homeomorph.compactlyGeneratedProdRightComparison.{u} F (P × A) τF τPA
  let v : @ContinuousMap (F × P) B τFP τB :=
    (@compactlyGeneratedCurryEquiv.{u} F P B τF tP τB inferInstance hP).symm
      (@ContinuousMap.id F τF)
  have hv : v (g, p) = g p :=
    @compactlyGeneratedCurryEquiv_symm_apply_apply.{u} F P B τF tP τB
      inferInstance hP (@ContinuousMap.id F τF) g p
  have hw :
      (@compactlyGeneratedCurryEquiv.{u} (F × P) A Y τFP tA tY inferInstance hA).symm
        v ((g, p), a) = v (g, p) a :=
    @compactlyGeneratedCurryEquiv_symm_apply_apply.{u} (F × P) A Y τFP tA tY
      inferInstance hA v (g, p) a
  change compactlyGeneratedUncurryEval.{u} P A Y
    ((@Homeomorph.toEquiv (F × (P × A)) (F × (P × A)) τR τD c)
      ((@Homeomorph.toEquiv ((F × P) × A) (F × (P × A)) τT τR r) ((g, p), a))) = _
  calc
    _ = compactlyGeneratedUncurryEval.{u} P A Y (g, (p, a)) :=
      congrArg (fun q : F × (P × A) => compactlyGeneratedUncurryEval.{u} P A Y q)
        ((@Homeomorph.compactlyGeneratedProdRightComparison_apply.{u}
          F (P × A) τF τPA
          ((@Homeomorph.toEquiv ((F × P) × A) (F × (P × A)) τT τR r)
            ((g, p), a))).trans
          (@Homeomorph.compactlyGeneratedProdAssoc_apply.{u} F P A τF tP tA
            ((g, p), a)))
    _ = g p a := compactlyGeneratedUncurryEval_apply.{u} P A Y (g, (p, a))
    _ = _ := (hw.trans (congrArg (fun b : B => b a) hv)).symm

/-- Currying intertwines canonical flat and nested evaluation as whole continuous
maps on the refinement of the product with the original pair of arguments. -/
theorem compactlyGeneratedCurry_eval :
    @ContinuousMap.comp ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P ×
      A)) ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) × (P × A)) Y
      (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
      A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P
      × A) τPA) tY)) τPA)) (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u}
      B (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B
      tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)) tY
        (compactlyGeneratedUncurryEval.{u} P A Y)
        (@compactlyGeneratedMap.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) × (P × A)) ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
          tY))) × (P × A))
          (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
            tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u}
            (P × A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA)
          (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY))) (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)
          (@ContinuousMap.prodMap (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
            tY) (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A)
            (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
            A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
            (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
            τPA τPA
            (@ContinuousMap.mk (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
              (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
              (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
              τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
              (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
              (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B
              (@compactOpen A Y tA tY)))) (@Homeomorph.toEquiv (@ContinuousMap (P × A) Y
              (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
              (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactlyGenerated.{u}
              (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P ×
              A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u}
              (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
              (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
              (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))
              (@Homeomorph.continuous_toFun (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
              A) τPA) tY) (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
              tY))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P ×
              A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
              (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
              (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B
              (@compactOpen A Y tA tY)))) (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP
              hA))) (@ContinuousMap.id (P × A) τPA))) =
      compactlyGeneratedCurryEval.{u} P A Y := by
  apply @ContinuousMap.ext ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P
    × A)) Y (@compactlyGenerated.{u} ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
    τPA) tY) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y
    (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P ×
    A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u}
    (P × A) τPA) tY)) τPA)) tY
  rintro ⟨h, p, a⟩
  have hp : (@ContinuousMap.prodMap (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
    tY) (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (P × A)
    (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
    (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u}
    (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B
    tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA τPA
      (@ContinuousMap.mk (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
        (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u}
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P
        B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) (@Homeomorph.toEquiv
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactlyGenerated.{u}
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u} (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
        (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
        (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))
        (@Homeomorph.continuous_toFun (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
        τPA) tY) (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
        (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u}
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P
        B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
        (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA))) (@ContinuousMap.id (P × A)
        τPA)) (h, (p, a)) =
        ((@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA) h, (p, a)) := rfl
  simpa only [ContinuousMap.comp_apply, compactlyGeneratedMap_apply, hp,
    compactlyGeneratedUncurryEval_apply, compactlyGeneratedCurryEval_apply] using
    (@Homeomorph.compactlyGeneratedCurry_apply_apply.{u} P A Y tP tA tY hP hA h p a)

/-- Uncurrying satisfies the inverse whole evaluation square on the corresponding
refined product domain. -/
theorem compactlyGeneratedCurry_symm_eval :
    @ContinuousMap.comp ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
      tY))) × (P × A)) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P ×
      A)) Y (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
      (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
      (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
      (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B
      tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)) (@compactlyGenerated.{u}
      ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) × (P × A))
      (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
      (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
      τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA)) tY
        (compactlyGeneratedCurryEval.{u} P A Y)
        (@compactlyGeneratedMap.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
          A Y tA tY))) × (P × A)) ((@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) × (P × A))
          (@instTopologicalSpaceProd (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY))) (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
            (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)
          (@instTopologicalSpaceProd (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
            tY) (P × A) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u}
            (P × A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA)
          (@ContinuousMap.prodMap (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
            Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A)
            (P × A) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
            (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen
            A Y tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
            (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
            (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA τPA
            (@ContinuousMap.mk (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
              tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
              (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
              (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B
              (@compactOpen A Y tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
              (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
              (@compactlyGenerated.{u} (P × A) τPA) tY)) (@Homeomorph.toEquiv (@ContinuousMap P B tP
              (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y
              (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap P B
              tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
              (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
              (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P ×
              A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) (@Homeomorph.symm (@ContinuousMap (P ×
              A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
              (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactlyGenerated.{u}
              (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P ×
              A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u}
              (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
              (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
              (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)))
              (@Homeomorph.continuous_toFun (@ContinuousMap P B tP (@compactlyGenerated.{u} B
              (@compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A)
              τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
              (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B
              (@compactOpen A Y tA tY)))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
              (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
              (@compactlyGenerated.{u} (P × A) τPA) tY)) (@Homeomorph.symm (@ContinuousMap (P × A) Y
              (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
              (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactlyGenerated.{u}
              (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P ×
              A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u}
              (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
              (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
              (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)))) (@ContinuousMap.id
              (P × A) τPA))) =
      compactlyGeneratedUncurryEval.{u} P A Y := by
  apply @ContinuousMap.ext ((@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
    tY))) × (P × A)) Y (@compactlyGenerated.{u} ((@ContinuousMap P B tP (@compactlyGenerated.{u} B
    (@compactOpen A Y tA tY))) × (P × A)) (@instTopologicalSpaceProd (@ContinuousMap P B tP
    (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (P × A) (@compactlyGenerated.{u}
    (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B
    tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) τPA)) tY
  rintro ⟨g, p, a⟩
  have hp : (@ContinuousMap.prodMap (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
    A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (P × A) (P × A)
    (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
    tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
    (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
    (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) τPA τPA
      (@ContinuousMap.mk (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA
        tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
        tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
        (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) (@Homeomorph.toEquiv
        (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@ContinuousMap
        (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactlyGenerated.{u} (@ContinuousMap
        P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
        (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))) (@compactlyGenerated.{u}
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY)) (@Homeomorph.symm (@ContinuousMap (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@compactOpen A Y tA tY))) (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u}
        (P × A) τPA) tY)) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@compactOpen A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y
        tA tY)))) (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)))
        (@Homeomorph.continuous_toFun (@ContinuousMap P B tP (@compactlyGenerated.{u} B
        (@compactOpen A Y tA tY))) (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
        tY) (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen
        A Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
        (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
        (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)) (@Homeomorph.symm
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactlyGenerated.{u}
        (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY) (@compactOpen (P × A) Y
        (@compactlyGenerated.{u} (P × A) τPA) tY)) (@compactlyGenerated.{u} (@ContinuousMap P B tP
        (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))) (@compactOpen P B tP
        (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
        (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)))) (@ContinuousMap.id (P × A)
        τPA)) (g, (p, a)) =
        ((@Homeomorph.symm (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY)
          (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY)))
          (@compactlyGenerated.{u} (@ContinuousMap (P × A) Y (@compactlyGenerated.{u} (P × A) τPA)
          tY) (@compactOpen (P × A) Y (@compactlyGenerated.{u} (P × A) τPA) tY))
          (@compactlyGenerated.{u} (@ContinuousMap P B tP (@compactlyGenerated.{u} B (@compactOpen A
          Y tA tY))) (@compactOpen P B tP (@compactlyGenerated.{u} B (@compactOpen A Y tA tY))))
          (@Homeomorph.compactlyGeneratedCurry.{u} P A Y tP tA tY hP hA)) g, (p, a)) := rfl
  simpa only [ContinuousMap.comp_apply, compactlyGeneratedMap_apply, hp,
    compactlyGeneratedCurryEval_apply, compactlyGeneratedUncurryEval_apply] using
    (@Homeomorph.compactlyGeneratedCurry_symm_apply_apply.{u}
      P A Y tP tA tY hP hA g p a)

end Evaluation

end ContinuousMap
