/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.CompactOpen.GeneratedByNaturality
public import FundamentalGroupoids.Topology.Convenient.CompactlyGenerated.Prod
public import FundamentalGroupoids.Topology.CompactOpen.CompactlyGenerated

/-!
# Currying from a compactly generated product

For original compactly generated spaces `P` and `A`, currying identifies continuous
maps from the compactly generated refinement of their original product with
continuous maps from `P` into the compactly generated ordinary compact-open space
`C(A, Y)`. The topology of `Y` is arbitrary. The compact-probe universe is independent
of all three carrier universes.

The construction uses the generated-map currying equivalence, with an
explicit interchange of the two product factors. The generated mapping-space
comparison supplies the compact-open topology. The existing whole compact-open
target-refinement homeomorphism removes the intermediate refinement of `Y`.
Neither an ordinary-product generatedness assertion nor local compactness of
`P` or `A` is needed. This is an equivalence of continuous-map carriers, not a
homeomorphism between spaces of currying operators.

## References

The exponential-law construction uses `Topology.ContinuousMapGeneratedBy.curryEquiv`
from Joël Riou's Mathlib [generated mapping spaces](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/HomSpace.lean) and [generated maps](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/ContinuousMapGeneratedBy.lean)
formalizations, together with Mathlib's ordinary compact-open and evaluation APIs.
The probe refinement uses [generated-by topology](https://github.com/leanprover-community/mathlib4/blob/83abb3e776bdefcbc447a1e44d0debe4010039e5/Mathlib/Topology/Convenient/GeneratedBy.lean), by Joël Riou, Dagur Asgeirsson and
Ben Eltschig. The mathematical setting is the compactly generated-space
exponential law discussed in J. Peter May, *A Concise Course in Algebraic Topology*
(revised author PDF); the present statement retains arbitrary original target
topology and an independent compact-probe universe.
-/

public section

noncomputable section

universe u p a y p' a' y'

open TopologicalSpace Topology

namespace ContinuousMap

-- These two adapters use the point laws of the generated-by refinement. In
-- particular, no identification of its type synonym with the original type is used.
private def refinedToGenerated {S : Type p} {T : Type y}
    [tS : TopologicalSpace S] [tT : TopologicalSpace T]
    (h : @ContinuousMap S T (@compactlyGenerated.{u} S tS) tT) :
    ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) S T := by
  let W := WithGeneratedByTopology (fun K : CompHaus.{u} => K) S
  let τW : TopologicalSpace W := tS.generatedBy (fun K : CompHaus.{u} => K)
  let e := @Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} S tS
  let e' := @Homeomorph.symm S W (@compactlyGenerated.{u} S tS) τW e
  let k : @ContinuousMap W T τW tT :=
    @ContinuousMap.comp W S T τW (@compactlyGenerated.{u} S tS) tT h
      (@ContinuousMap.mk W S τW (@compactlyGenerated.{u} S tS)
        (@Homeomorph.toEquiv W S τW (@compactlyGenerated.{u} S tS) e')
        (@Homeomorph.continuous_toFun W S τW (@compactlyGenerated.{u} S tS) e'))
  exact @ContinuousMapGeneratedBy.comp (CompHaus.{u}) (fun K : CompHaus.{u} => K)
    inferInstance W τW T tT S tS
    (ContinuousMapGeneratedBy.ofContinuousMap (fun K : CompHaus.{u} => K)
      (A := W) (Y := T) (tA := τW) (tY := tT) k)
    (@WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy (CompHaus.{u})
      (fun K : CompHaus.{u} => K) inferInstance S tS)

private theorem refinedToGenerated_apply {S : Type p} {T : Type y}
    [tS : TopologicalSpace S] [tT : TopologicalSpace T]
    (h : @ContinuousMap S T (@compactlyGenerated.{u} S tS) tT) (s : S) :
    refinedToGenerated.{u} h s = h s := by
  change h ((@Homeomorph.toEquiv
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S) S
    (tS.generatedBy (fun K : CompHaus.{u} => K)) (@compactlyGenerated.{u} S tS)
    (@Homeomorph.symm S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
      (@compactlyGenerated.{u} S tS) (tS.generatedBy (fun K : CompHaus.{u} => K))
      (@Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} S tS)))
    (WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy
      (fun K : CompHaus.{u} => K) S s)) = h s
  rw [WithGeneratedByTopology.equivSymmAsContinuousMapGeneratedBy_coe,
    Homeomorph.compactlyGeneratedToGeneratedByCompHaus_symm_apply,
    Equiv.apply_symm_apply]

private def generatedToRefined {S : Type p} {T : Type y}
    [tS : TopologicalSpace S] [tT : TopologicalSpace T]
    (r : ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) S T) :
    @ContinuousMap S T (@compactlyGenerated.{u} S tS) tT := by
  have hr : ContinuousGeneratedBy (fun K : CompHaus.{u} => K) (r : S → T) := by
    apply (@continuousGeneratedBy_def (CompHaus.{u}) (fun K : CompHaus.{u} => K)
      inferInstance S tS T tT (r : S → T)).2
    intro K f
    rw [← @ContinuousMapGeneratedBy.precomp_apply (CompHaus.{u})
      (fun K : CompHaus.{u} => K) inferInstance S tS T tT K f r]
    exact @ContinuousMap.continuous K T inferInstance tT
      (@ContinuousMapGeneratedBy.precomp (CompHaus.{u}) (fun K : CompHaus.{u} => K)
        inferInstance S tS T tT K f r)
  let WS := WithGeneratedByTopology (fun K : CompHaus.{u} => K) S
  let WT := WithGeneratedByTopology (fun K : CompHaus.{u} => K) T
  let τS : TopologicalSpace WS := tS.generatedBy (fun K : CompHaus.{u} => K)
  let τT : TopologicalSpace WT := tT.generatedBy (fun K : CompHaus.{u} => K)
  let e := @Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} S tS
  let k : @ContinuousMap WS T τS tT :=
    @ContinuousMap.comp WS WT T τS τT tT
      (@WithGeneratedByTopology.counitContinuousMap (CompHaus.{u})
        (fun K : CompHaus.{u} => K) inferInstance T tT)
      (@ContinuousGeneratedBy.continuousMap (CompHaus.{u}) (fun K : CompHaus.{u} => K)
        inferInstance S tS T tT (r : S → T) hr)
  exact @ContinuousMap.comp S WS T (@compactlyGenerated.{u} S tS) τS tT k
    (@ContinuousMap.mk S WS (@compactlyGenerated.{u} S tS) τS
      (@Homeomorph.toEquiv S WS (@compactlyGenerated.{u} S tS) τS e)
      (@Homeomorph.continuous_toFun S WS (@compactlyGenerated.{u} S tS) τS e))

private theorem generatedToRefined_apply {S : Type p} {T : Type y}
    [tS : TopologicalSpace S] [tT : TopologicalSpace T]
    (r : ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) S T) (s : S) :
    generatedToRefined.{u} r s = r s := by
  have hr : ContinuousGeneratedBy (fun K : CompHaus.{u} => K) (r : S → T) := by
    apply (@continuousGeneratedBy_def (CompHaus.{u}) (fun K : CompHaus.{u} => K)
      inferInstance S tS T tT (r : S → T)).2
    intro K f
    rw [← @ContinuousMapGeneratedBy.precomp_apply (CompHaus.{u})
      (fun K : CompHaus.{u} => K) inferInstance S tS T tT K f r]
    exact @ContinuousMap.continuous K T inferInstance tT
      (@ContinuousMapGeneratedBy.precomp (CompHaus.{u}) (fun K : CompHaus.{u} => K)
        inferInstance S tS T tT K f r)
  change WithGeneratedByTopology.equiv
    ((@ContinuousGeneratedBy.continuousMap (CompHaus.{u}) (fun K : CompHaus.{u} => K)
      inferInstance S tS T tT (r : S → T) hr)
      (@Homeomorph.toEquiv S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
        (@compactlyGenerated.{u} S tS) (tS.generatedBy (fun K : CompHaus.{u} => K))
        (@Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} S tS) s)) = r s
  rw [ContinuousGeneratedBy.continuousMap_coe, Function.comp_apply, Function.comp_apply,
    Equiv.apply_symm_apply, Homeomorph.compactlyGeneratedToGeneratedByCompHaus_apply]

-- The generic comparison is used once, specialized to the canonical fixed-u
-- compact Hausdorff family. Its carrier equivalence preserves every original value.
private def refinedGeneratedCompactOpen (A : Type a) (T : Type y)
    [tA : TopologicalSpace A] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} A] :
    @Homeomorph (ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) A T)
      (@ContinuousMap A T tA tT)
      (compactlyGenerated.{u}
        (ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) A T))
      (@compactlyGenerated.{u} (@ContinuousMap A T tA tT) (@compactOpen A T tA tT)) := by
  letI : IsGeneratedBy (fun K : CompHaus.{u} => K) A :=
    (uCompactlyGeneratedSpace_iff_isGeneratedBy_compHaus A).1 inferInstance
  letI : ∀ K L : CompHaus.{u},
      IsGeneratedBy (fun K : CompHaus.{u} => K) (K × L) := fun K L =>
    (uCompactlyGeneratedSpace_iff_isGeneratedBy_compHaus (K × L)).1 inferInstance
  letI : ∀ K : CompHaus.{u},
      IsGeneratedBy (fun K : CompHaus.{u} => K) (K × A) := fun K =>
    IsGeneratedBy.probe_prod (fun K : CompHaus.{u} => K) (A := A) K
  let R := ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) A T
  let τR : TopologicalSpace R := inferInstance
  let τC : TopologicalSpace (@ContinuousMap A T tA tT) := @compactOpen A T tA tT
  refine @Homeomorph.mk R (@ContinuousMap A T tA tT)
    (@compactlyGenerated.{u} R τR)
    (@compactlyGenerated.{u} (@ContinuousMap A T tA tT) τC)
    (ContinuousMapGeneratedBy.equivContinuousMap (fun K : CompHaus.{u} => K)
      (A := A) (Y := T) (tA := tA) (tY := tT)) ?_ ?_
  · rw [compactlyGenerated_eq_generatedBy_compHaus,
      compactlyGenerated_eq_generatedBy_compHaus]
    exact @Homeomorph.continuous_toFun R (@ContinuousMap A T tA tT)
      (τR.generatedBy (fun K : CompHaus.{u} => K))
      (τC.generatedBy (fun K : CompHaus.{u} => K))
      (Homeomorph.generatedByCompactOpen (fun K : CompHaus.{u} => K) A T)
  · rw [compactlyGenerated_eq_generatedBy_compHaus,
      compactlyGenerated_eq_generatedBy_compHaus]
    exact @Homeomorph.continuous_invFun R (@ContinuousMap A T tA tT)
      (τR.generatedBy (fun K : CompHaus.{u} => K))
      (τC.generatedBy (fun K : CompHaus.{u} => K))
      (Homeomorph.generatedByCompactOpen (fun K : CompHaus.{u} => K) A T)

private theorem refinedGeneratedCompactOpen_apply_apply
    (A : Type a) (T : Type y) [tA : TopologicalSpace A] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} A]
    (r : ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) A T) (a : A) :
    refinedGeneratedCompactOpen.{u} A T r a = r a := rfl

private theorem refinedGeneratedCompactOpen_symm_apply_apply
    (A : Type a) (T : Type y) [tA : TopologicalSpace A] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} A] (f : C(A, T)) (a : A) :
    (@Homeomorph.symm (ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) A T)
      (@ContinuousMap A T tA tT)
      (compactlyGenerated.{u}
        (ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) A T))
      (@compactlyGenerated.{u} (@ContinuousMap A T tA tT) (@compactOpen A T tA tT))
      (refinedGeneratedCompactOpen.{u} A T)) f a = f a := rfl

-- Currying with a fixed target dictionary. The public construction below applies
-- this to κY, then uses the existing whole target-refinement homeomorphism.
private def curryRefinedTarget (P : Type p) (A : Type a) (T : Type y)
    [tP : TopologicalSpace P] [tA : TopologicalSpace A] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} P] [UCompactlyGeneratedSpace.{u} A]
    (h : @ContinuousMap (P × A) T (compactlyGenerated.{u} (P × A)) tT) :
    @ContinuousMap P C(A, T) tP (compactlyGenerated.{u} C(A, T)) := by
  letI : IsGeneratedBy (fun K : CompHaus.{u} => K) P :=
    (uCompactlyGeneratedSpace_iff_isGeneratedBy_compHaus P).1 inferInstance
  letI : ∀ K L : CompHaus.{u},
      IsGeneratedBy (fun K : CompHaus.{u} => K) (K × L) := fun K L =>
    (uCompactlyGeneratedSpace_iff_isGeneratedBy_compHaus (K × L)).1 inferInstance
  let e := Homeomorph.prodComm A P
  let flip : C(A × P, P × A) :=
    @ContinuousMap.mk (A × P) (P × A) (@instTopologicalSpaceProd A P tA tP)
      (@instTopologicalSpaceProd P A tP tA)
      (@Homeomorph.toEquiv (A × P) (P × A) (@instTopologicalSpaceProd A P tA tP)
        (@instTopologicalSpaceProd P A tP tA) e)
      (@Homeomorph.continuous_toFun (A × P) (P × A)
        (@instTopologicalSpaceProd A P tA tP) (@instTopologicalSpaceProd P A tP tA) e)
  let r := (refinedToGenerated.{u} h).comp
    (ContinuousMapGeneratedBy.ofContinuousMap (fun K : CompHaus.{u} => K) flip)
  let R := ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) A T
  let τR : TopologicalSpace R := inferInstance
  let τC : TopologicalSpace C(A, T) := @compactOpen A T tA tT
  let c : @ContinuousMap P R tP τR :=
    ContinuousMapGeneratedBy.toContinuousMap (fun K : CompHaus.{u} => K)
      (ContinuousMapGeneratedBy.curryEquiv r)
  let c' : @ContinuousMap P R tP (@compactlyGenerated.{u} R τR) :=
    @ContinuousMap.mk P R tP (@compactlyGenerated.{u} R τR)
      (@ContinuousMap.toFun P R tP τR c)
      ((continuous_to_compactlyGenerated_iff (tZ := tP) (tX := τR)
        (@ContinuousMap.toFun P R tP τR c)).2 (@ContinuousMap.continuous P R tP τR c))
  let d := refinedGeneratedCompactOpen.{u} A T
  exact @ContinuousMap.comp P R C(A, T) tP (@compactlyGenerated.{u} R τR)
    (@compactlyGenerated.{u} C(A, T) τC)
    (@ContinuousMap.mk R C(A, T) (@compactlyGenerated.{u} R τR)
      (@compactlyGenerated.{u} C(A, T) τC)
      (@Homeomorph.toEquiv R C(A, T) (@compactlyGenerated.{u} R τR)
        (@compactlyGenerated.{u} C(A, T) τC) d)
      (@Homeomorph.continuous_toFun R C(A, T) (@compactlyGenerated.{u} R τR)
        (@compactlyGenerated.{u} C(A, T) τC) d)) c'

private theorem curryRefinedTarget_apply
    (P : Type p) (A : Type a) (T : Type y)
    [tP : TopologicalSpace P] [tA : TopologicalSpace A] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} P] [UCompactlyGeneratedSpace.{u} A]
    (h : @ContinuousMap (P × A) T (compactlyGenerated.{u} (P × A)) tT)
    (p : P) (a : A) : curryRefinedTarget.{u} P A T h p a = h (p, a) := by
  let : IsGeneratedBy (fun K : CompHaus.{u} => K) P :=
    (uCompactlyGeneratedSpace_iff_isGeneratedBy_compHaus P).1 inferInstance
  let : ∀ K L : CompHaus.{u},
      IsGeneratedBy (fun K : CompHaus.{u} => K) (K × L) := fun K L =>
    (uCompactlyGeneratedSpace_iff_isGeneratedBy_compHaus (K × L)).1 inferInstance
  let e := Homeomorph.prodComm A P
  let flip : C(A × P, P × A) :=
    @ContinuousMap.mk (A × P) (P × A) (@instTopologicalSpaceProd A P tA tP)
      (@instTopologicalSpaceProd P A tP tA)
      (@Homeomorph.toEquiv (A × P) (P × A) (@instTopologicalSpaceProd A P tA tP)
        (@instTopologicalSpaceProd P A tP tA) e)
      (@Homeomorph.continuous_toFun (A × P) (P × A)
        (@instTopologicalSpaceProd A P tA tP) (@instTopologicalSpaceProd P A tP tA) e)
  let r := (refinedToGenerated.{u} h).comp
    (ContinuousMapGeneratedBy.ofContinuousMap (fun K : CompHaus.{u} => K) flip)
  change refinedGeneratedCompactOpen.{u} A T
    (ContinuousMapGeneratedBy.toContinuousMap (fun K : CompHaus.{u} => K)
      (ContinuousMapGeneratedBy.curryEquiv r) p) a = h (p, a)
  rw [refinedGeneratedCompactOpen_apply_apply, ContinuousMapGeneratedBy.toContinuousMap_apply,
    ContinuousMapGeneratedBy.curryEquiv_apply_apply]
  change refinedToGenerated.{u} h ((Homeomorph.prodComm A P) (a, p)) = h (p, a)
  rw [Homeomorph.coe_prodComm]
  exact refinedToGenerated_apply h (p, a)

private def uncurryRefinedTarget (P : Type p) (A : Type a) (T : Type y)
    [tP : TopologicalSpace P] [tA : TopologicalSpace A] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} A]
    (g : @ContinuousMap P C(A, T) tP (compactlyGenerated.{u} C(A, T))) :
    @ContinuousMap (P × A) T (compactlyGenerated.{u} (P × A)) tT := by
  letI : ∀ K L : CompHaus.{u},
      IsGeneratedBy (fun K : CompHaus.{u} => K) (K × L) := fun K L =>
    (uCompactlyGeneratedSpace_iff_isGeneratedBy_compHaus (K × L)).1 inferInstance
  let R := ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) A T
  let τR : TopologicalSpace R := inferInstance
  let τC : TopologicalSpace C(A, T) := @compactOpen A T tA tT
  let d := @Homeomorph.symm R C(A, T) (@compactlyGenerated.{u} R τR)
    (@compactlyGenerated.{u} C(A, T) τC) (refinedGeneratedCompactOpen.{u} A T)
  let c' : @ContinuousMap P R tP (@compactlyGenerated.{u} R τR) :=
    @ContinuousMap.comp P C(A, T) R tP (@compactlyGenerated.{u} C(A, T) τC)
      (@compactlyGenerated.{u} R τR)
      (@ContinuousMap.mk C(A, T) R (@compactlyGenerated.{u} C(A, T) τC)
        (@compactlyGenerated.{u} R τR)
        (@Homeomorph.toEquiv C(A, T) R (@compactlyGenerated.{u} C(A, T) τC)
          (@compactlyGenerated.{u} R τR) d)
        (@Homeomorph.continuous_toFun C(A, T) R (@compactlyGenerated.{u} C(A, T) τC)
          (@compactlyGenerated.{u} R τR) d)) g
  let c : @ContinuousMap P R tP τR :=
    @ContinuousMap.comp P R R tP (@compactlyGenerated.{u} R τR) τR
      (@compactlyGeneratedCounit.{u} R τR) c'
  let r := ContinuousMapGeneratedBy.curryEquiv.symm
    (ContinuousMapGeneratedBy.ofContinuousMap (fun K : CompHaus.{u} => K) c)
  let e := @Homeomorph.symm (A × P) (P × A) (@instTopologicalSpaceProd A P tA tP)
    (@instTopologicalSpaceProd P A tP tA) (Homeomorph.prodComm A P)
  let flip : C(P × A, A × P) :=
    @ContinuousMap.mk (P × A) (A × P) (@instTopologicalSpaceProd P A tP tA)
      (@instTopologicalSpaceProd A P tA tP)
      (@Homeomorph.toEquiv (P × A) (A × P) (@instTopologicalSpaceProd P A tP tA)
        (@instTopologicalSpaceProd A P tA tP) e)
      (@Homeomorph.continuous_toFun (P × A) (A × P)
        (@instTopologicalSpaceProd P A tP tA) (@instTopologicalSpaceProd A P tA tP) e)
  exact generatedToRefined.{u}
    (r.comp (ContinuousMapGeneratedBy.ofContinuousMap (fun K : CompHaus.{u} => K) flip))

private theorem uncurryRefinedTarget_apply
    (P : Type p) (A : Type a) (T : Type y)
    [tP : TopologicalSpace P] [tA : TopologicalSpace A] [tT : TopologicalSpace T]
    [UCompactlyGeneratedSpace.{u} A]
    (g : @ContinuousMap P C(A, T) tP (compactlyGenerated.{u} C(A, T)))
    (p : P) (a : A) : uncurryRefinedTarget.{u} P A T g (p, a) = g p a := by
  let : ∀ K L : CompHaus.{u},
      IsGeneratedBy (fun K : CompHaus.{u} => K) (K × L) := fun K L =>
    (uCompactlyGeneratedSpace_iff_isGeneratedBy_compHaus (K × L)).1 inferInstance
  let R := ContinuousMapGeneratedBy (fun K : CompHaus.{u} => K) A T
  let τR : TopologicalSpace R := inferInstance
  let τC : TopologicalSpace C(A, T) := @compactOpen A T tA tT
  let d := @Homeomorph.symm R C(A, T) (@compactlyGenerated.{u} R τR)
    (@compactlyGenerated.{u} C(A, T) τC) (refinedGeneratedCompactOpen.{u} A T)
  change generatedToRefined.{u} _ (p, a) = g p a
  rw [generatedToRefined_apply]
  change ContinuousMapGeneratedBy.curryEquiv.symm
    (ContinuousMapGeneratedBy.ofContinuousMap (fun K : CompHaus.{u} => K)
      (@ContinuousMap.comp P R R tP (@compactlyGenerated.{u} R τR) τR
        (@compactlyGeneratedCounit.{u} R τR)
        (@ContinuousMap.comp P C(A, T) R tP (@compactlyGenerated.{u} C(A, T) τC)
          (@compactlyGenerated.{u} R τR)
          (@ContinuousMap.mk C(A, T) R (@compactlyGenerated.{u} C(A, T) τC)
            (@compactlyGenerated.{u} R τR)
            (@Homeomorph.toEquiv C(A, T) R (@compactlyGenerated.{u} C(A, T) τC)
              (@compactlyGenerated.{u} R τR) d)
            (@Homeomorph.continuous_toFun C(A, T) R
              (@compactlyGenerated.{u} C(A, T) τC) (@compactlyGenerated.{u} R τR) d)) g)))
      ((Homeomorph.prodComm A P).symm (p, a)) = g p a
  rw [Homeomorph.prodComm_symm, Homeomorph.coe_prodComm,
    ContinuousMapGeneratedBy.curryEquiv_symm_apply]
  change (@compactlyGeneratedCounit.{u} R τR)
    (@Homeomorph.toEquiv C(A, T) R (@compactlyGenerated.{u} C(A, T) τC)
      (@compactlyGenerated.{u} R τR) d (g p)) a = g p a
  rw [compactlyGeneratedCounit_apply]
  exact refinedGeneratedCompactOpen_symm_apply_apply A T (g p) a

variable (P : Type p) (A : Type a) (Y : Type y)
  [tP : TopologicalSpace P] [tA : TopologicalSpace A] [tY : TopologicalSpace Y]
  [UCompactlyGeneratedSpace.{u} P] [UCompactlyGeneratedSpace.{u} A]

/-- Curry a map from the refinement of the original product into the refinement
of the ordinary compact-open space, retaining the original target topology. -/
def compactlyGeneratedCurry
    (h : @ContinuousMap (P × A) Y (compactlyGenerated.{u} (P × A)) tY) :
    @ContinuousMap P (@ContinuousMap A Y tA tY) tP
      (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY)) := by
  let τPA := @compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)
  let τY := @compactlyGenerated.{u} Y tY
  let Cκ := @ContinuousMap A Y tA τY
  let C₀ := @ContinuousMap A Y tA tY
  let τκ := @compactlyGenerated.{u} Cκ (@compactOpen A Y tA τY)
  let τ₀ := @compactlyGenerated.{u} C₀ (@compactOpen A Y tA tY)
  let h' : @ContinuousMap (P × A) Y τPA τY :=
    @ContinuousMap.mk (P × A) Y τPA τY
      (@ContinuousMap.toFun (P × A) Y τPA tY h)
      ((continuous_to_compactlyGenerated_iff (tZ := τPA) (tX := tY)
        (@ContinuousMap.toFun (P × A) Y τPA tY h)).2
          (@ContinuousMap.continuous (P × A) Y τPA tY h))
  let d := @Homeomorph.compactlyGeneratedCompactOpen.{u} A Y tA tY inferInstance
  exact @ContinuousMap.comp P Cκ C₀ tP τκ τ₀
    (@ContinuousMap.mk Cκ C₀ τκ τ₀
      (@Homeomorph.toEquiv Cκ C₀ τκ τ₀ d)
      (@Homeomorph.continuous_toFun Cκ C₀ τκ τ₀ d))
    (@curryRefinedTarget.{u} P A Y tP tA τY inferInstance inferInstance h')

/-- Uncurry a family in the refined ordinary compact-open space to a continuous
map on the refinement of the original product. -/
def compactlyGeneratedUncurry
    (g : @ContinuousMap P (@ContinuousMap A Y tA tY) tP
      (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))) :
    @ContinuousMap (P × A) Y (compactlyGenerated.{u} (P × A)) tY := by
  let τPA := @compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)
  let τY := @compactlyGenerated.{u} Y tY
  let Cκ := @ContinuousMap A Y tA τY
  let C₀ := @ContinuousMap A Y tA tY
  let τκ := @compactlyGenerated.{u} Cκ (@compactOpen A Y tA τY)
  let τ₀ := @compactlyGenerated.{u} C₀ (@compactOpen A Y tA tY)
  let d := @Homeomorph.symm Cκ C₀ τκ τ₀
    (@Homeomorph.compactlyGeneratedCompactOpen.{u} A Y tA tY inferInstance)
  let g' : @ContinuousMap P Cκ tP τκ :=
    @ContinuousMap.comp P C₀ Cκ tP τ₀ τκ
      (@ContinuousMap.mk C₀ Cκ τ₀ τκ
        (@Homeomorph.toEquiv C₀ Cκ τ₀ τκ d)
        (@Homeomorph.continuous_toFun C₀ Cκ τ₀ τκ d)) g
  exact @ContinuousMap.comp (P × A) Y Y τPA τY tY
    (@compactlyGeneratedCounit.{u} Y tY)
    (@uncurryRefinedTarget.{u} P A Y tP tA τY inferInstance g')

/-- Currying preserves every value, for every map and both original arguments. -/
@[simp]
theorem compactlyGeneratedCurry_apply
    (h : @ContinuousMap (P × A) Y (compactlyGenerated.{u} (P × A)) tY)
    (p : P) (a : A) : compactlyGeneratedCurry.{u} P A Y h p a = h (p, a) := by
  let τPA := @compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)
  let τY := @compactlyGenerated.{u} Y tY
  let hκ : @ContinuousMap (P × A) Y τPA τY :=
    @ContinuousMap.mk (P × A) Y τPA τY
      (@ContinuousMap.toFun (P × A) Y τPA tY h)
      ((continuous_to_compactlyGenerated_iff (tZ := τPA) (tX := tY)
        (@ContinuousMap.toFun (P × A) Y τPA tY h)).2
          (@ContinuousMap.continuous (P × A) Y τPA tY h))
  change (@Homeomorph.compactlyGeneratedCompactOpen.{u} A Y tA tY inferInstance)
    (@curryRefinedTarget.{u} P A Y tP tA τY inferInstance inferInstance hκ p) a = h (p, a)
  calc
    _ = hκ (p, a) := by
      rw [Homeomorph.compactlyGeneratedCompactOpen_apply_apply, curryRefinedTarget_apply]
    _ = h (p, a) := rfl

omit [UCompactlyGeneratedSpace P] in
/-- Uncurrying preserves every value, for every family and both original arguments. -/
@[simp]
theorem compactlyGeneratedUncurry_apply
    (g : @ContinuousMap P (@ContinuousMap A Y tA tY) tP
      (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY)))
    (p : P) (a : A) : compactlyGeneratedUncurry.{u} P A Y g (p, a) = g p a := by
  let τY := @compactlyGenerated.{u} Y tY
  let Cκ := @ContinuousMap A Y tA τY
  let C₀ := @ContinuousMap A Y tA tY
  let τκ := @compactlyGenerated.{u} Cκ (@compactOpen A Y tA τY)
  let τ₀ := @compactlyGenerated.{u} C₀ (@compactOpen A Y tA tY)
  let d := @Homeomorph.symm Cκ C₀ τκ τ₀
    (@Homeomorph.compactlyGeneratedCompactOpen.{u} A Y tA tY inferInstance)
  let gκ : @ContinuousMap P Cκ tP τκ :=
    @ContinuousMap.comp P C₀ Cκ tP τ₀ τκ
      (@ContinuousMap.mk C₀ Cκ τ₀ τκ
        (@Homeomorph.toEquiv C₀ Cκ τ₀ τκ d)
        (@Homeomorph.continuous_toFun C₀ Cκ τ₀ τκ d)) g
  change (@compactlyGeneratedCounit.{u} Y tY)
    (@uncurryRefinedTarget.{u} P A Y tP tA τY inferInstance gκ (p, a)) = g p a
  calc
    _ = gκ p a := by
      rw [compactlyGeneratedCounit_apply, uncurryRefinedTarget_apply]
    _ = g p a := by
      change d (g p) a = g p a
      rw [Homeomorph.compactlyGeneratedCompactOpen_symm_apply_apply]

/-- Uncurrying after currying recovers the whole map on the refined product. -/
@[simp]
theorem compactlyGeneratedUncurry_curry
    (h : @ContinuousMap (P × A) Y (compactlyGenerated.{u} (P × A)) tY) :
    compactlyGeneratedUncurry.{u} P A Y (compactlyGeneratedCurry.{u} P A Y h) = h := by
  apply @ContinuousMap.ext (P × A) Y
    (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY
  rintro ⟨p, a⟩
  simp only [compactlyGeneratedUncurry_apply, compactlyGeneratedCurry_apply]

/-- Currying after uncurrying recovers the whole continuous family. -/
@[simp]
theorem compactlyGeneratedCurry_uncurry
    (g : @ContinuousMap P (@ContinuousMap A Y tA tY) tP
      (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))) :
    compactlyGeneratedCurry.{u} P A Y (compactlyGeneratedUncurry.{u} P A Y g) = g := by
  apply @ContinuousMap.ext P (@ContinuousMap A Y tA tY) tP
    (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))
  intro p
  apply @ContinuousMap.ext A Y tA tY
  intro a
  simp only [compactlyGeneratedCurry_apply, compactlyGeneratedUncurry_apply]

/-- Currying for original fixed-universe compactly generated parameter and argument
spaces. The source retains the outer refinement of their original product; the
target is the refinement of the ordinary compact-open continuous-map carrier.
There is no generatedness, separation, or local compactness condition on `Y`. -/
@[expose]
def compactlyGeneratedCurryEquiv :
    (@ContinuousMap (P × A) Y
      (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY) ≃
    (@ContinuousMap P (@ContinuousMap A Y tA tY) tP
      (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))) where
  toFun := compactlyGeneratedCurry.{u} P A Y
  invFun := compactlyGeneratedUncurry.{u} P A Y
  left_inv := compactlyGeneratedUncurry_curry.{u} P A Y
  right_inv := compactlyGeneratedCurry_uncurry.{u} P A Y

/-- The whole forward function is the currying construction. -/
theorem coe_compactlyGeneratedCurryEquiv :
    ⇑(compactlyGeneratedCurryEquiv.{u} P A Y) = compactlyGeneratedCurry.{u} P A Y := rfl

/-- The whole inverse function is the uncurrying construction. -/
theorem coe_compactlyGeneratedCurryEquiv_symm :
    ⇑(compactlyGeneratedCurryEquiv.{u} P A Y).symm = compactlyGeneratedUncurry.{u} P A Y := rfl

/-- Applying the equivalence selects the whole currying construction. -/
theorem compactlyGeneratedCurryEquiv_apply
    (h : @ContinuousMap (P × A) Y (compactlyGenerated.{u} (P × A)) tY) :
    compactlyGeneratedCurryEquiv.{u} P A Y h = compactlyGeneratedCurry.{u} P A Y h := rfl

/-- Applying the inverse selects the whole uncurrying construction. -/
theorem compactlyGeneratedCurryEquiv_symm_apply
    (g : @ContinuousMap P (@ContinuousMap A Y tA tY) tP
      (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))) :
    (compactlyGeneratedCurryEquiv.{u} P A Y).symm g =
      compactlyGeneratedUncurry.{u} P A Y g := rfl

/-- The forward equivalence has the currying evaluation law on every input. -/
@[simp]
theorem compactlyGeneratedCurryEquiv_apply_apply
    (h : @ContinuousMap (P × A) Y (compactlyGenerated.{u} (P × A)) tY)
    (p : P) (a : A) : compactlyGeneratedCurryEquiv.{u} P A Y h p a = h (p, a) :=
  compactlyGeneratedCurry_apply.{u} P A Y h p a

/-- The inverse equivalence has the uncurrying evaluation law on every input. -/
@[simp]
theorem compactlyGeneratedCurryEquiv_symm_apply_apply
    (g : @ContinuousMap P (@ContinuousMap A Y tA tY) tP
      (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY)))
    (p : P) (a : A) : (compactlyGeneratedCurryEquiv.{u} P A Y).symm g (p, a) = g p a :=
  compactlyGeneratedUncurry_apply.{u} P A Y g p a

/-- The whole underlying two-variable function of a curried map. -/
theorem coe_compactlyGeneratedCurryEquiv_apply
    (h : @ContinuousMap (P × A) Y (compactlyGenerated.{u} (P × A)) tY) :
    (fun p a => compactlyGeneratedCurryEquiv.{u} P A Y h p a) = fun p a => h (p, a) := by
  funext p a
  exact compactlyGeneratedCurryEquiv_apply_apply.{u} P A Y h p a

/-- The whole underlying function of an uncurried family. -/
theorem coe_compactlyGeneratedCurryEquiv_symm_apply
    (g : @ContinuousMap P (@ContinuousMap A Y tA tY) tP
      (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))) :
    ⇑((compactlyGeneratedCurryEquiv.{u} P A Y).symm g) = fun q => g q.1 q.2 := by
  funext q
  exact compactlyGeneratedCurryEquiv_symm_apply_apply.{u} P A Y g q.1 q.2

/-- Curried maps agree exactly when the original maps agree at every product point. -/
theorem compactlyGeneratedCurryEquiv_eq_iff
    (h k : @ContinuousMap (P × A) Y (compactlyGenerated.{u} (P × A)) tY) :
    compactlyGeneratedCurryEquiv.{u} P A Y h = compactlyGeneratedCurryEquiv.{u} P A Y k ↔
      ∀ p a, h (p, a) = k (p, a) := by
  constructor
  · intro he p a
    simpa only [compactlyGeneratedCurryEquiv_apply_apply] using
      congrArg (fun g : @ContinuousMap P (@ContinuousMap A Y tA tY) tP
        (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY)) =>
          g p a) he
  · intro he
    apply congrArg (compactlyGeneratedCurryEquiv.{u} P A Y)
    apply @ContinuousMap.ext (P × A) Y
      (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY
    rintro ⟨p, a⟩
    exact he p a

/-- On an ordinary continuous product map, currying agrees with ordinary currying
followed by the canonical lift of the continuous family to the refined target.
This compatibility needs no local compactness assumption. -/
theorem compactlyGeneratedCurryEquiv_curry (h : C(P × A, Y)) :
    compactlyGeneratedCurryEquiv.{u} P A Y
        (@ContinuousMap.comp (P × A) (P × A) Y
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA))
          (@instTopologicalSpaceProd P A tP tA) tY h
          (compactlyGeneratedCounit.{u} (P × A))) =
      @ContinuousMap.mk P (@ContinuousMap A Y tA tY) tP
        (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))
        (@ContinuousMap.toFun P (@ContinuousMap A Y tA tY) tP
          (@compactOpen A Y tA tY) h.curry)
        ((continuous_to_compactlyGenerated_iff (tZ := tP)
          (tX := @compactOpen A Y tA tY) h.curry).2 h.curry.continuous) := by
  apply @ContinuousMap.ext P (@ContinuousMap A Y tA tY) tP
    (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))
  intro p
  apply @ContinuousMap.ext A Y tA tY
  intro a
  simp only [compactlyGeneratedCurryEquiv_apply_apply, ContinuousMap.comp_apply,
    compactlyGeneratedCounit_apply]
  rfl

variable {P A Y}

/-- Simultaneous naturality in the parameter, argument, and original target.
Both sides are whole continuous families, and the source product map is refined
before precomposition. -/
theorem compactlyGeneratedCurryEquiv_naturality
    {P' : Type p'} {A' : Type a'} {Y' : Type y'}
    [tP' : TopologicalSpace P'] [tA' : TopologicalSpace A'] [tY' : TopologicalSpace Y']
    [UCompactlyGeneratedSpace.{u} P'] [UCompactlyGeneratedSpace.{u} A']
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y'))
    (h : @ContinuousMap (P × A) Y (compactlyGenerated.{u} (P × A)) tY) :
    compactlyGeneratedCurryEquiv.{u} P' A' Y'
        (@ContinuousMap.comp (P' × A') Y Y'
          (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA'))
          tY tY' k
          (@ContinuousMap.comp (P' × A') (P × A) Y
            (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA'))
            (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY h
            (compactlyGeneratedMap.{u} (f.prodMap j)))) =
      @ContinuousMap.comp P' (@ContinuousMap A Y tA tY) (@ContinuousMap A' Y' tA' tY')
        tP' (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))
        (@compactlyGenerated.{u} (@ContinuousMap A' Y' tA' tY') (@compactOpen A' Y' tA' tY'))
        (compactlyGeneratedMap.{u}
          ((postcompContinuousMap (A := A') k).comp
            (precompContinuousMap (Y := Y) j)))
        (@ContinuousMap.comp P' P (@ContinuousMap A Y tA tY) tP' tP
          (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))
          (compactlyGeneratedCurryEquiv.{u} P A Y h) f) := by
  apply @ContinuousMap.ext P' (@ContinuousMap A' Y' tA' tY') tP'
    (@compactlyGenerated.{u} (@ContinuousMap A' Y' tA' tY') (@compactOpen A' Y' tA' tY'))
  intro p
  apply @ContinuousMap.ext A' Y' tA' tY'
  intro a
  have hprod : (f.prodMap j) (p, a) = (f p, j a) := rfl
  simp only [compactlyGeneratedCurryEquiv_apply_apply, ContinuousMap.comp_apply,
    compactlyGeneratedMap_apply, ContinuousMap.postcompContinuousMap_apply_apply,
    ContinuousMap.precompContinuousMap_apply_apply, hprod]

/-- The inverse equivalence is natural in all three original spaces as well. -/
theorem compactlyGeneratedCurryEquiv_symm_naturality
    {P' : Type p'} {A' : Type a'} {Y' : Type y'}
    [tP' : TopologicalSpace P'] [tA' : TopologicalSpace A'] [tY' : TopologicalSpace Y']
    [UCompactlyGeneratedSpace.{u} P'] [UCompactlyGeneratedSpace.{u} A']
    (f : C(P', P)) (j : C(A', A)) (k : C(Y, Y'))
    (g : @ContinuousMap P (@ContinuousMap A Y tA tY) tP
      (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))) :
    (compactlyGeneratedCurryEquiv.{u} P' A' Y').symm
        (@ContinuousMap.comp P' (@ContinuousMap A Y tA tY) (@ContinuousMap A' Y' tA' tY')
          tP' (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY))
          (@compactlyGenerated.{u} (@ContinuousMap A' Y' tA' tY') (@compactOpen A' Y' tA' tY'))
          (compactlyGeneratedMap.{u}
            ((postcompContinuousMap (A := A') k).comp
              (precompContinuousMap (Y := Y) j)))
          (@ContinuousMap.comp P' P (@ContinuousMap A Y tA tY) tP' tP
            (@compactlyGenerated.{u} (@ContinuousMap A Y tA tY) (@compactOpen A Y tA tY)) g f)) =
      @ContinuousMap.comp (P' × A') Y Y'
        (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY tY' k
        (@ContinuousMap.comp (P' × A') (P × A) Y
          (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA'))
          (@compactlyGenerated.{u} (P × A) (@instTopologicalSpaceProd P A tP tA)) tY
          ((compactlyGeneratedCurryEquiv.{u} P A Y).symm g)
          (compactlyGeneratedMap.{u} (f.prodMap j))) := by
  apply @ContinuousMap.ext (P' × A') Y'
    (@compactlyGenerated.{u} (P' × A') (@instTopologicalSpaceProd P' A' tP' tA')) tY'
  rintro ⟨p, a⟩
  have hprod : (f.prodMap j) (p, a) = (f p, j a) := rfl
  simp only [compactlyGeneratedCurryEquiv_symm_apply_apply, ContinuousMap.comp_apply,
    compactlyGeneratedMap_apply, ContinuousMap.postcompContinuousMap_apply_apply,
    ContinuousMap.precompContinuousMap_apply_apply, hprod]

end ContinuousMap
