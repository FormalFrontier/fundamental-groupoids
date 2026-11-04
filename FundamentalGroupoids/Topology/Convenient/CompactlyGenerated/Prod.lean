/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Convenient.CompactlyGenerated
public import FundamentalGroupoids.Topology.Convenient.GeneratedBy.Prod

/-!
# Products refined by compact Hausdorff probes

The two factors are arbitrary original spaces. The compact Hausdorff probe universe
is fixed independently of both carrier universes. The canonical comparison refines
the product of the two counits; its inverse lifts the pair of refined projections.

The compact Hausdorff family identifies these constructions with the general
stock generated-by product comparison. The locally compact generated first-factor
comparison is recovered as an agreement of continuous maps.

The carriers are unchanged by compact generation. Topology-sensitive combinators
therefore receive the original and refined topologies as explicit arguments.
-/

@[expose] public section

noncomputable section

universe u v w v' w'

open TopologicalSpace Topology

namespace ContinuousMap

/-- Refine the product of the two counits, using the original product as target. -/
def compactlyGeneratedProdForward (X : Type v) (Y : Type w)
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] :
    @ContinuousMap (X × Y) (X × Y)
      (@compactlyGenerated.{u} (X × Y)
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y)))
      (compactlyGenerated.{u} (X × Y)) :=
  @compactlyGeneratedMap.{u} (X × Y) (X × Y)
    (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
      (compactlyGenerated.{u} Y))
    (@instTopologicalSpaceProd X Y tX tY)
    (@ContinuousMap.prodMap X X Y Y (compactlyGenerated.{u} X) tX
      (compactlyGenerated.{u} Y) tY
      (@compactlyGeneratedCounit.{u} X tX) (@compactlyGeneratedCounit.{u} Y tY))

/-- Lift the pair of refined original projections from their already generated source. -/
def compactlyGeneratedProdBackward (X : Type v) (Y : Type w)
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] :
    @ContinuousMap (X × Y) (X × Y) (compactlyGenerated.{u} (X × Y))
      (@compactlyGenerated.{u} (X × Y)
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y))) :=
  toCompactlyGenerated.{u}
    (tZ := compactlyGenerated.{u} (X × Y))
    (tX := @instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
      (compactlyGenerated.{u} Y))
    (@ContinuousMap.prodMk (X × Y) (compactlyGenerated.{u} (X × Y)) X Y
      (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y)
      (@compactlyGeneratedMap.{u} (X × Y) X
        (@instTopologicalSpaceProd X Y tX tY) tX (@fst X Y tX tY))
      (@compactlyGeneratedMap.{u} (X × Y) Y
        (@instTopologicalSpaceProd X Y tX tY) tY (@snd X Y tX tY)))

variable (X : Type v) (Y : Type w)
variable [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

@[simp]
theorem compactlyGeneratedProdForward_apply (p : X × Y) :
    compactlyGeneratedProdForward.{u} X Y p = p := by
  rfl

@[simp]
theorem compactlyGeneratedProdBackward_apply (p : X × Y) :
    compactlyGeneratedProdBackward.{u} X Y p = p := by
  rfl

/-- The refined first projection of the forward map is the counit's first coordinate. -/
theorem compactlyGeneratedProdForward_fst :
    @ContinuousMap.comp (X × Y) (X × Y) X
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y)) (compactlyGenerated.{u} X)
        (@compactlyGeneratedMap.{u} (X × Y) X
          (@instTopologicalSpaceProd X Y tX tY) tX (@fst X Y tX tY))
        (compactlyGeneratedProdForward.{u} X Y) =
      @ContinuousMap.comp (X × Y) (X × Y) X
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y)) (compactlyGenerated.{u} X)
        (@fst X Y (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y))
        (@compactlyGeneratedCounit.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y))) := by
  apply DFunLike.ext
  intro p
  rfl

/-- The refined second projection of the forward map is the counit's second coordinate. -/
theorem compactlyGeneratedProdForward_snd :
    @ContinuousMap.comp (X × Y) (X × Y) Y
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y)) (compactlyGenerated.{u} Y)
        (@compactlyGeneratedMap.{u} (X × Y) Y
          (@instTopologicalSpaceProd X Y tX tY) tY (@snd X Y tX tY))
        (compactlyGeneratedProdForward.{u} X Y) =
      @ContinuousMap.comp (X × Y) (X × Y) Y
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y)) (compactlyGenerated.{u} Y)
        (@snd X Y (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y))
        (@compactlyGeneratedCounit.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y))) := by
  apply DFunLike.ext
  intro p
  rfl

/-- The forward comparison is the refinement of the product of the two counits. -/
theorem compactlyGeneratedProdForward_counit :
    @ContinuousMap.comp (X × Y) (X × Y) (X × Y)
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y)) (@instTopologicalSpaceProd X Y tX tY)
        (@compactlyGeneratedCounit.{u} (X × Y) (@instTopologicalSpaceProd X Y tX tY))
        (compactlyGeneratedProdForward.{u} X Y) =
      @ContinuousMap.comp (X × Y) (X × Y) (X × Y)
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y)) (@instTopologicalSpaceProd X Y tX tY)
        (@ContinuousMap.prodMap X X Y Y (compactlyGenerated.{u} X) tX
          (compactlyGenerated.{u} Y) tY
          (@compactlyGeneratedCounit.{u} X tX) (@compactlyGeneratedCounit.{u} Y tY))
        (@compactlyGeneratedCounit.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y))) := by
  apply DFunLike.ext
  intro p
  rfl

/-- Forgetting the final lift gives precisely the pair of refined projections. -/
theorem compactlyGeneratedProdBackward_counit :
    @ContinuousMap.comp (X × Y) (X × Y) (X × Y)
        (compactlyGenerated.{u} (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y))
        (@compactlyGeneratedCounit.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGeneratedProdBackward.{u} X Y) =
      @ContinuousMap.prodMk (X × Y) (compactlyGenerated.{u} (X × Y)) X Y
        (compactlyGenerated.{u} X) (compactlyGenerated.{u} Y)
        (@compactlyGeneratedMap.{u} (X × Y) X
          (@instTopologicalSpaceProd X Y tX tY) tX (@fst X Y tX tY))
        (@compactlyGeneratedMap.{u} (X × Y) Y
          (@instTopologicalSpaceProd X Y tX tY) tY (@snd X Y tX tY)) := by
  apply DFunLike.ext
  intro p
  rfl

private def compactlyGeneratedCompHausTransport (S : Type v) [tS : TopologicalSpace S] :
    @ContinuousMap S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
      (compactlyGenerated.{u} S) (tS.generatedBy (fun K : CompHaus.{u} => K)) :=
  @ContinuousMap.mk S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
    (compactlyGenerated.{u} S) (tS.generatedBy (fun K : CompHaus.{u} => K))
    (WithGeneratedByTopology.equiv
      (X := fun K : CompHaus.{u} => K) (Y := S)).symm
    (by
      change @Continuous S S (compactlyGenerated.{u} S)
        (tS.generatedBy (fun K : CompHaus.{u} => K)) id
      rw [TopologicalSpace.compactlyGenerated_eq_generatedBy_compHaus]
      exact @continuous_id S (tS.generatedBy (fun K : CompHaus.{u} => K)))

-- Point views retain the topologies of the bundled transports when taking their functions.
private def compactlyGeneratedCompHausPoint (S : Type v) [tS : TopologicalSpace S] :
    S → WithGeneratedByTopology (fun K : CompHaus.{u} => K) S :=
  @ContinuousMap.toFun S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
    (compactlyGenerated.{u} S) (tS.generatedBy (fun K : CompHaus.{u} => K))
    (compactlyGeneratedCompHausTransport.{u} S)

private theorem compactlyGeneratedCompHausPoint_apply
    (S : Type v) [TopologicalSpace S] (s : S) :
    compactlyGeneratedCompHausPoint.{u} S s =
      (WithGeneratedByTopology.equiv
        (X := fun K : CompHaus.{u} => K) (Y := S)).symm s := by
  rfl

private theorem compactlyGeneratedCompHausPoint_injective
    (S : Type v) [TopologicalSpace S] :
    Function.Injective (compactlyGeneratedCompHausPoint.{u} S) := by
  intro p q h
  apply (WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := S)).symm.injective
  exact (compactlyGeneratedCompHausPoint_apply.{u} S p).symm.trans
    (h.trans (compactlyGeneratedCompHausPoint_apply.{u} S q))

-- Transport the refinement of the refined-factor product, retaining the outer refinement.
private def compactlyGeneratedProdCompHausTransport :
    @ContinuousMap (X × Y)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
          WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y))
      (@compactlyGenerated.{u} (X × Y)
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y)))
      ((@instTopologicalSpaceProd
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
        (tX.generatedBy (fun K : CompHaus.{u} => K))
        (tY.generatedBy (fun K : CompHaus.{u} => K))).generatedBy
          (fun K : CompHaus.{u} => K)) :=
  @ContinuousMap.comp (X × Y)
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
        WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y))
    (@compactlyGenerated.{u} (X × Y)
      (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y)))
    ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
      (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K))
    ((@instTopologicalSpaceProd
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
      (tX.generatedBy (fun K : CompHaus.{u} => K))
      (tY.generatedBy (fun K : CompHaus.{u} => K))).generatedBy
        (fun K : CompHaus.{u} => K))
    (@WithGeneratedByTopology.mapContinuousMap _ (fun K : CompHaus.{u} => K)
      (fun _ => inferInstance) (X × Y)
      (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y))
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
        WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
      (@instTopologicalSpaceProd
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
        (tX.generatedBy (fun K : CompHaus.{u} => K))
        (tY.generatedBy (fun K : CompHaus.{u} => K)))
      (@ContinuousMap.prodMap X
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X) Y
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
        (compactlyGenerated.{u} X) (tX.generatedBy (fun K : CompHaus.{u} => K))
        (compactlyGenerated.{u} Y) (tY.generatedBy (fun K : CompHaus.{u} => K))
        (compactlyGeneratedCompHausTransport.{u} X)
        (compactlyGeneratedCompHausTransport.{u} Y)))
    (@compactlyGeneratedCompHausTransport.{u} (X × Y)
      (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y)))

private def compactlyGeneratedProdCompHausPoint :
    (X × Y) → WithGeneratedByTopology (fun K : CompHaus.{u} => K)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
        WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y) :=
  @ContinuousMap.toFun (X × Y)
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
        WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y))
    (@compactlyGenerated.{u} (X × Y)
      (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y)))
    ((@instTopologicalSpaceProd
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
      (tX.generatedBy (fun K : CompHaus.{u} => K))
      (tY.generatedBy (fun K : CompHaus.{u} => K))).generatedBy
        (fun K : CompHaus.{u} => K))
    (compactlyGeneratedProdCompHausTransport.{u} X Y)

private theorem compactlyGeneratedProdCompHausPoint_equiv (p : X × Y) :
    WithGeneratedByTopology.equiv
        (X := fun K : CompHaus.{u} => K)
        (Y := WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
          WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
        (compactlyGeneratedProdCompHausPoint.{u} X Y p) =
      (compactlyGeneratedCompHausPoint.{u} X p.1,
       compactlyGeneratedCompHausPoint.{u} Y p.2) := by
  let r := @ContinuousMap.prodMap X
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X) Y
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
    (compactlyGenerated.{u} X) (tX.generatedBy (fun K : CompHaus.{u} => K))
    (compactlyGenerated.{u} Y) (tY.generatedBy (fun K : CompHaus.{u} => K))
    (compactlyGeneratedCompHausTransport.{u} X)
    (compactlyGeneratedCompHausTransport.{u} Y)
  exact (@WithGeneratedByTopology.equiv_mapContinuousMap _
    (fun K : CompHaus.{u} => K) (fun K => inferInstance) (X × Y)
    (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
      (compactlyGenerated.{u} Y))
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
      WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
    (@instTopologicalSpaceProd
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
      (tX.generatedBy (fun K : CompHaus.{u} => K))
      (tY.generatedBy (fun K : CompHaus.{u} => K))) r
    ((WithGeneratedByTopology.equiv
      (X := fun K : CompHaus.{u} => K) (Y := X × Y)).symm p)).trans
    (congrArg
      (fun q : X × Y => (compactlyGeneratedCompHausPoint.{u} X q.1,
        compactlyGeneratedCompHausPoint.{u} Y q.2))
      (Equiv.apply_symm_apply
        (WithGeneratedByTopology.equiv
          (X := fun K : CompHaus.{u} => K) (Y := X × Y)) p))

private theorem compactlyGeneratedProdCompHausPoint_injective :
    Function.Injective (compactlyGeneratedProdCompHausPoint.{u} X Y) := by
  intro p q hpq
  have h := congrArg
    (WithGeneratedByTopology.equiv
      (X := fun K : CompHaus.{u} => K)
      (Y := WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
        WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)) hpq
  rw [compactlyGeneratedProdCompHausPoint_equiv,
    compactlyGeneratedProdCompHausPoint_equiv] at h
  apply Prod.ext
  · apply compactlyGeneratedCompHausPoint_injective.{u} X
    exact congrArg Prod.fst h
  · apply compactlyGeneratedCompHausPoint_injective.{u} Y
    exact congrArg Prod.snd h

private theorem compactlyGeneratedProdForward_compHaus (p : X × Y) :
    compactlyGeneratedCompHausPoint.{u} (X × Y)
        (compactlyGeneratedProdForward.{u} X Y p) =
      WithGeneratedByTopology.prodForward (fun K : CompHaus.{u} => K) X Y
        (compactlyGeneratedProdCompHausPoint.{u} X Y p) := by
  let eO := WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := X × Y)
  let eX := WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := X)
  let eY := WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := Y)
  let eQ := WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K)
    (Y := WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
      WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
  apply eO.injective
  calc
    eO (compactlyGeneratedCompHausPoint.{u} (X × Y)
        (compactlyGeneratedProdForward.{u} X Y p)) =
        compactlyGeneratedProdForward.{u} X Y p := Equiv.apply_symm_apply eO _
    _ = p := compactlyGeneratedProdForward_apply.{u} X Y p
    _ = (eX (compactlyGeneratedCompHausPoint.{u} X p.1),
        eY (compactlyGeneratedCompHausPoint.{u} Y p.2)) :=
      (Prod.ext (Equiv.apply_symm_apply eX p.1)
        (Equiv.apply_symm_apply eY p.2)).symm
    _ = (eX (eQ (compactlyGeneratedProdCompHausPoint.{u} X Y p)).1,
        eY (eQ (compactlyGeneratedProdCompHausPoint.{u} X Y p)).2) :=
      congrArg
        (fun q : WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
            WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y =>
          (eX q.1, eY q.2))
        (compactlyGeneratedProdCompHausPoint_equiv.{u} X Y p).symm
    _ = eO (WithGeneratedByTopology.prodForward (fun K : CompHaus.{u} => K) X Y
        (compactlyGeneratedProdCompHausPoint.{u} X Y p)) :=
      ((congrArg eO (WithGeneratedByTopology.prodForward_apply
        (fun K : CompHaus.{u} => K) X Y
        (compactlyGeneratedProdCompHausPoint.{u} X Y p))).trans
          (Equiv.apply_symm_apply eO _)).symm

private theorem compactlyGeneratedProdBackward_compHaus (p : X × Y) :
    compactlyGeneratedProdCompHausPoint.{u} X Y
        (compactlyGeneratedProdBackward.{u} X Y p) =
      WithGeneratedByTopology.prodBackward (fun K : CompHaus.{u} => K) X Y
        (compactlyGeneratedCompHausPoint.{u} (X × Y) p) := by
  let eO := WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := X × Y)
  let eX := WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := X)
  let eY := WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := Y)
  let eQ := WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K)
    (Y := WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
      WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
  have hfst : WithGeneratedByTopology.mapContinuousMap (fun K : CompHaus.{u} => K)
      (@fst X Y tX tY) (compactlyGeneratedCompHausPoint.{u} (X × Y) p) =
      compactlyGeneratedCompHausPoint.{u} X p.1 :=
    (WithGeneratedByTopology.mapContinuousMap_apply (fun K : CompHaus.{u} => K)
      (@fst X Y tX tY) (compactlyGeneratedCompHausPoint.{u} (X × Y) p)).trans
        (congrArg (fun q : X × Y => eX.symm q.1) (Equiv.apply_symm_apply eO p))
  have hsnd : WithGeneratedByTopology.mapContinuousMap (fun K : CompHaus.{u} => K)
      (@snd X Y tX tY) (compactlyGeneratedCompHausPoint.{u} (X × Y) p) =
      compactlyGeneratedCompHausPoint.{u} Y p.2 :=
    (WithGeneratedByTopology.mapContinuousMap_apply (fun K : CompHaus.{u} => K)
      (@snd X Y tX tY) (compactlyGeneratedCompHausPoint.{u} (X × Y) p)).trans
        (congrArg (fun q : X × Y => eY.symm q.2) (Equiv.apply_symm_apply eO p))
  apply eQ.injective
  calc
    eQ (compactlyGeneratedProdCompHausPoint.{u} X Y
        (compactlyGeneratedProdBackward.{u} X Y p)) =
        (compactlyGeneratedCompHausPoint.{u} X
          (compactlyGeneratedProdBackward.{u} X Y p).1,
         compactlyGeneratedCompHausPoint.{u} Y
          (compactlyGeneratedProdBackward.{u} X Y p).2) :=
      compactlyGeneratedProdCompHausPoint_equiv.{u} X Y _
    _ = (compactlyGeneratedCompHausPoint.{u} X p.1,
        compactlyGeneratedCompHausPoint.{u} Y p.2) :=
      congrArg (fun q : X × Y => (compactlyGeneratedCompHausPoint.{u} X q.1,
        compactlyGeneratedCompHausPoint.{u} Y q.2))
        (compactlyGeneratedProdBackward_apply.{u} X Y p)
    _ = (WithGeneratedByTopology.mapContinuousMap (fun K : CompHaus.{u} => K)
          (@fst X Y tX tY) (compactlyGeneratedCompHausPoint.{u} (X × Y) p),
        WithGeneratedByTopology.mapContinuousMap (fun K : CompHaus.{u} => K)
          (@snd X Y tX tY) (compactlyGeneratedCompHausPoint.{u} (X × Y) p)) :=
      (Prod.ext hfst hsnd).symm
    _ = eQ (WithGeneratedByTopology.prodBackward (fun K : CompHaus.{u} => K) X Y
        (compactlyGeneratedCompHausPoint.{u} (X × Y) p)) :=
      ((congrArg eQ (WithGeneratedByTopology.prodBackward_apply
        (fun K : CompHaus.{u} => K) X Y
        (compactlyGeneratedCompHausPoint.{u} (X × Y) p))).trans
          (Equiv.apply_symm_apply eQ _)).symm

/-- The canonical backward map is a left inverse of the forward map. -/
theorem compactlyGeneratedProdBackward_comp_forward :
    @ContinuousMap.comp (X × Y) (X × Y) (X × Y)
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGeneratedProdBackward.{u} X Y)
        (compactlyGeneratedProdForward.{u} X Y) =
      @ContinuousMap.id (X × Y)
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y))) := by
  apply @ContinuousMap.ext (X × Y) (X × Y)
    (@compactlyGenerated.{u} (X × Y)
      (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y)))
    (@compactlyGenerated.{u} (X × Y)
      (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y)))
  intro p
  apply compactlyGeneratedProdCompHausPoint_injective.{u} X Y
  change compactlyGeneratedProdCompHausPoint.{u} X Y
      (compactlyGeneratedProdBackward.{u} X Y
        (compactlyGeneratedProdForward.{u} X Y p)) =
    compactlyGeneratedProdCompHausPoint.{u} X Y p
  exact (compactlyGeneratedProdBackward_compHaus.{u} X Y
      (compactlyGeneratedProdForward.{u} X Y p)).trans
    ((congrArg
      (fun q : WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y) =>
        WithGeneratedByTopology.prodBackward (fun K : CompHaus.{u} => K) X Y q)
      (compactlyGeneratedProdForward_compHaus.{u} X Y p)).trans
        (DFunLike.congr_fun
          (WithGeneratedByTopology.prodBackward_comp_prodForward
            (fun K : CompHaus.{u} => K) X Y)
          (compactlyGeneratedProdCompHausPoint.{u} X Y p)))

/-- The canonical forward map is a left inverse of the backward map. -/
theorem compactlyGeneratedProdForward_comp_backward :
    @ContinuousMap.comp (X × Y) (X × Y) (X × Y)
        (compactlyGenerated.{u} (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y))
        (compactlyGeneratedProdForward.{u} X Y)
        (compactlyGeneratedProdBackward.{u} X Y) =
      @ContinuousMap.id (X × Y) (compactlyGenerated.{u} (X × Y)) := by
  apply @ContinuousMap.ext (X × Y) (X × Y)
    (compactlyGenerated.{u} (X × Y)) (compactlyGenerated.{u} (X × Y))
  intro p
  apply compactlyGeneratedCompHausPoint_injective.{u} (X × Y)
  change compactlyGeneratedCompHausPoint.{u} (X × Y)
      (compactlyGeneratedProdForward.{u} X Y
        (compactlyGeneratedProdBackward.{u} X Y p)) =
    compactlyGeneratedCompHausPoint.{u} (X × Y) p
  exact (compactlyGeneratedProdForward_compHaus.{u} X Y
      (compactlyGeneratedProdBackward.{u} X Y p)).trans
    ((congrArg
      (fun q : WithGeneratedByTopology (fun K : CompHaus.{u} => K)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
            WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y) =>
        WithGeneratedByTopology.prodForward (fun K : CompHaus.{u} => K) X Y q)
      (compactlyGeneratedProdBackward_compHaus.{u} X Y p)).trans
        (DFunLike.congr_fun
          (WithGeneratedByTopology.prodForward_comp_prodBackward
            (fun K : CompHaus.{u} => K) X Y)
          (compactlyGeneratedCompHausPoint.{u} (X × Y) p)))

variable {X Y}
variable {X' : Type v'} {Y' : Type w'}
variable [tX' : TopologicalSpace X'] [tY' : TopologicalSpace Y']

/-- Naturality in both original factors, with the same compact probe universe. -/
theorem compactlyGeneratedProdForward_naturality (f : C(X, X')) (g : C(Y, Y')) :
    @ContinuousMap.comp (X × Y) (X' × Y') (X' × Y')
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (@compactlyGenerated.{u} (X' × Y')
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y')))
        (compactlyGenerated.{u} (X' × Y'))
        (compactlyGeneratedProdForward.{u} X' Y')
        (@compactlyGeneratedMap.{u} (X × Y) (X' × Y')
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y))
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y'))
          (@ContinuousMap.prodMap X X' Y Y'
            (compactlyGenerated.{u} X) (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y) (compactlyGenerated.{u} Y')
            (@compactlyGeneratedMap.{u} X X' tX tX' f)
            (@compactlyGeneratedMap.{u} Y Y' tY tY' g))) =
      @ContinuousMap.comp (X × Y) (X × Y) (X' × Y')
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y)) (compactlyGenerated.{u} (X' × Y'))
        (@compactlyGeneratedMap.{u} (X × Y) (X' × Y')
          (@instTopologicalSpaceProd X Y tX tY) (@instTopologicalSpaceProd X' Y' tX' tY')
          (@ContinuousMap.prodMap X X' Y Y' tX tX' tY tY' f g))
        (compactlyGeneratedProdForward.{u} X Y) := by
  apply @ContinuousMap.ext (X × Y) (X' × Y')
    (@compactlyGenerated.{u} (X × Y)
      (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y)))
    (compactlyGenerated.{u} (X' × Y'))
  intro p
  rfl

/-- The lifted projection pair is natural in both original factors. -/
theorem compactlyGeneratedProdBackward_naturality (f : C(X, X')) (g : C(Y, Y')) :
    @ContinuousMap.comp (X × Y) (X' × Y') (X' × Y')
        (compactlyGenerated.{u} (X × Y)) (compactlyGenerated.{u} (X' × Y'))
        (@compactlyGenerated.{u} (X' × Y')
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y')))
        (compactlyGeneratedProdBackward.{u} X' Y')
        (@compactlyGeneratedMap.{u} (X × Y) (X' × Y')
          (@instTopologicalSpaceProd X Y tX tY) (@instTopologicalSpaceProd X' Y' tX' tY')
          (@ContinuousMap.prodMap X X' Y Y' tX tX' tY tY' f g)) =
      @ContinuousMap.comp (X × Y) (X × Y) (X' × Y')
        (compactlyGenerated.{u} (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (@compactlyGenerated.{u} (X' × Y')
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y')))
        (@compactlyGeneratedMap.{u} (X × Y) (X' × Y')
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y))
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y'))
          (@ContinuousMap.prodMap X X' Y Y'
            (compactlyGenerated.{u} X) (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y) (compactlyGenerated.{u} Y')
            (@compactlyGeneratedMap.{u} X X' tX tX' f)
            (@compactlyGeneratedMap.{u} Y Y' tY tY' g)))
        (compactlyGeneratedProdBackward.{u} X Y) := by
  apply @ContinuousMap.ext (X × Y) (X' × Y')
    (compactlyGenerated.{u} (X × Y))
    (@compactlyGenerated.{u} (X' × Y')
      (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
        (compactlyGenerated.{u} Y')))
  intro p
  rfl

end ContinuousMap

namespace Homeomorph

/-- The canonical comparison of the two refined products of arbitrary original spaces. -/
def compactlyGeneratedProdComparison (X : Type v) (Y : Type w)
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] :
    @Homeomorph (X × Y) (X × Y)
      (@compactlyGenerated.{u} (X × Y)
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y)))
      (compactlyGenerated.{u} (X × Y)) :=
  @Homeomorph.mk (X × Y) (X × Y)
    (@compactlyGenerated.{u} (X × Y)
      (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y)))
    (compactlyGenerated.{u} (X × Y))
    { toFun := ContinuousMap.compactlyGeneratedProdForward.{u} X Y
      invFun := ContinuousMap.compactlyGeneratedProdBackward.{u} X Y
      left_inv := fun p => DFunLike.congr_fun
        (ContinuousMap.compactlyGeneratedProdBackward_comp_forward.{u} X Y) p
      right_inv := fun p => DFunLike.congr_fun
        (ContinuousMap.compactlyGeneratedProdForward_comp_backward.{u} X Y) p }
    (@ContinuousMap.continuous (X × Y) (X × Y)
      (@compactlyGenerated.{u} (X × Y)
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y)))
      (compactlyGenerated.{u} (X × Y))
      (ContinuousMap.compactlyGeneratedProdForward.{u} X Y))
    (@ContinuousMap.continuous (X × Y) (X × Y)
      (compactlyGenerated.{u} (X × Y))
      (@compactlyGenerated.{u} (X × Y)
        (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
          (compactlyGenerated.{u} Y)))
      (ContinuousMap.compactlyGeneratedProdBackward.{u} X Y))

variable (X : Type v) (Y : Type w)
variable [tX : TopologicalSpace X] [tY : TopologicalSpace Y]

/-- The homeomorphism uses exactly the refined product of the two counits. -/
theorem compactlyGeneratedProdComparison_toContinuousMap :
    (show @ContinuousMap (X × Y) (X × Y)
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y)) from
      let e := (compactlyGeneratedProdComparison.{u} X Y)
      @ContinuousMap.mk (X × Y) (X × Y)
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y))
        (@Homeomorph.toEquiv (X × Y) (X × Y)
          (@compactlyGenerated.{u} (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y)))
          (compactlyGenerated.{u} (X × Y)) e)
        (@Homeomorph.continuous_toFun (X × Y) (X × Y)
          (@compactlyGenerated.{u} (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y)))
          (compactlyGenerated.{u} (X × Y)) e)) =
      ContinuousMap.compactlyGeneratedProdForward.{u} X Y := by
  rfl

/-- The inverse homeomorphism uses exactly the lifted pair of refined projections. -/
theorem compactlyGeneratedProdComparison_symm_toContinuousMap :
    (show @ContinuousMap (X × Y) (X × Y)
        (compactlyGenerated.{u} (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y))) from
      let e := (@Homeomorph.symm (X × Y) (X × Y)
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y)) (compactlyGeneratedProdComparison.{u} X Y))
      @ContinuousMap.mk (X × Y) (X × Y)
        (compactlyGenerated.{u} (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (@Homeomorph.toEquiv (X × Y) (X × Y)
          (compactlyGenerated.{u} (X × Y))
          (@compactlyGenerated.{u} (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y))) e)
        (@Homeomorph.continuous_toFun (X × Y) (X × Y)
          (compactlyGenerated.{u} (X × Y))
          (@compactlyGenerated.{u} (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y))) e)) =
      ContinuousMap.compactlyGeneratedProdBackward.{u} X Y := by
  rfl

@[simp]
theorem compactlyGeneratedProdComparison_apply (p : X × Y) :
    compactlyGeneratedProdComparison.{u} X Y p = p := by
  exact ContinuousMap.compactlyGeneratedProdForward_apply.{u} X Y p

@[simp]
theorem compactlyGeneratedProdComparison_symm_apply (p : X × Y) :
    @Homeomorph.symm (X × Y) (X × Y)
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y)) (compactlyGeneratedProdComparison.{u} X Y) p = p := by
  exact ContinuousMap.compactlyGeneratedProdBackward_apply.{u} X Y p

variable {X Y}
variable {X' : Type v'} {Y' : Type w'}
variable [tX' : TopologicalSpace X'] [tY' : TopologicalSpace Y']

/-- The comparison homeomorphism is natural in both original spaces. -/
theorem compactlyGeneratedProdComparison_naturality (f : C(X, X')) (g : C(Y, Y')) :
    @ContinuousMap.comp (X × Y) (X' × Y') (X' × Y')
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (@compactlyGenerated.{u} (X' × Y')
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y')))
        (compactlyGenerated.{u} (X' × Y'))
        (show @ContinuousMap (X' × Y') (X' × Y')
          (@compactlyGenerated.{u} (X' × Y')
            (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
              (compactlyGenerated.{u} Y')))
          (compactlyGenerated.{u} (X' × Y')) from
          let e := (compactlyGeneratedProdComparison.{u} X' Y')
          @ContinuousMap.mk (X' × Y') (X' × Y')
            (@compactlyGenerated.{u} (X' × Y')
              (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
                (compactlyGenerated.{u} Y')))
            (compactlyGenerated.{u} (X' × Y'))
            (@Homeomorph.toEquiv (X' × Y') (X' × Y')
              (@compactlyGenerated.{u} (X' × Y')
                (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
                  (compactlyGenerated.{u} Y')))
              (compactlyGenerated.{u} (X' × Y')) e)
            (@Homeomorph.continuous_toFun (X' × Y') (X' × Y')
              (@compactlyGenerated.{u} (X' × Y')
                (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
                  (compactlyGenerated.{u} Y')))
              (compactlyGenerated.{u} (X' × Y')) e))
        (@ContinuousMap.compactlyGeneratedMap.{u} (X × Y) (X' × Y')
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y))
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y'))
          (@ContinuousMap.prodMap X X' Y Y'
            (compactlyGenerated.{u} X) (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y) (compactlyGenerated.{u} Y')
            (@ContinuousMap.compactlyGeneratedMap.{u} X X' tX tX' f)
            (@ContinuousMap.compactlyGeneratedMap.{u} Y Y' tY tY' g))) =
      @ContinuousMap.comp (X × Y) (X × Y) (X' × Y')
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y)) (compactlyGenerated.{u} (X' × Y'))
        (@ContinuousMap.compactlyGeneratedMap.{u} (X × Y) (X' × Y')
          (@instTopologicalSpaceProd X Y tX tY) (@instTopologicalSpaceProd X' Y' tX' tY')
          (@ContinuousMap.prodMap X X' Y Y' tX tX' tY tY' f g))
        (show @ContinuousMap (X × Y) (X × Y)
          (@compactlyGenerated.{u} (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y)))
          (compactlyGenerated.{u} (X × Y)) from
          let e := (compactlyGeneratedProdComparison.{u} X Y)
          @ContinuousMap.mk (X × Y) (X × Y)
            (@compactlyGenerated.{u} (X × Y)
              (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                (compactlyGenerated.{u} Y)))
            (compactlyGenerated.{u} (X × Y))
            (@Homeomorph.toEquiv (X × Y) (X × Y)
              (@compactlyGenerated.{u} (X × Y)
                (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y)))
              (compactlyGenerated.{u} (X × Y)) e)
            (@Homeomorph.continuous_toFun (X × Y) (X × Y)
              (@compactlyGenerated.{u} (X × Y)
                (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y)))
              (compactlyGenerated.{u} (X × Y)) e)) := by
  exact ContinuousMap.compactlyGeneratedProdForward_naturality.{u} f g

/-- The inverse comparison homeomorphism is natural in both original spaces. -/
theorem compactlyGeneratedProdComparison_symm_naturality (f : C(X, X')) (g : C(Y, Y')) :
    @ContinuousMap.comp (X × Y) (X' × Y') (X' × Y')
        (compactlyGenerated.{u} (X × Y)) (compactlyGenerated.{u} (X' × Y'))
        (@compactlyGenerated.{u} (X' × Y')
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y')))
        (show @ContinuousMap (X' × Y') (X' × Y')
          (compactlyGenerated.{u} (X' × Y'))
          (@compactlyGenerated.{u} (X' × Y')
            (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
              (compactlyGenerated.{u} Y'))) from
          let e := (@Homeomorph.symm (X' × Y') (X' × Y')
            (@compactlyGenerated.{u} (X' × Y')
              (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
                (compactlyGenerated.{u} Y')))
            (compactlyGenerated.{u} (X' × Y')) (compactlyGeneratedProdComparison.{u} X' Y'))
          @ContinuousMap.mk (X' × Y') (X' × Y')
            (compactlyGenerated.{u} (X' × Y'))
            (@compactlyGenerated.{u} (X' × Y')
              (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
                (compactlyGenerated.{u} Y')))
            (@Homeomorph.toEquiv (X' × Y') (X' × Y')
              (compactlyGenerated.{u} (X' × Y'))
              (@compactlyGenerated.{u} (X' × Y')
                (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
                  (compactlyGenerated.{u} Y'))) e)
            (@Homeomorph.continuous_toFun (X' × Y') (X' × Y')
              (compactlyGenerated.{u} (X' × Y'))
              (@compactlyGenerated.{u} (X' × Y')
                (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
                  (compactlyGenerated.{u} Y'))) e))
        (@ContinuousMap.compactlyGeneratedMap.{u} (X × Y) (X' × Y')
          (@instTopologicalSpaceProd X Y tX tY) (@instTopologicalSpaceProd X' Y' tX' tY')
          (@ContinuousMap.prodMap X X' Y Y' tX tX' tY tY' f g)) =
      @ContinuousMap.comp (X × Y) (X × Y) (X' × Y')
        (compactlyGenerated.{u} (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (@compactlyGenerated.{u} (X' × Y')
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y')))
        (@ContinuousMap.compactlyGeneratedMap.{u} (X × Y) (X' × Y')
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y))
          (@instTopologicalSpaceProd X' Y' (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y'))
          (@ContinuousMap.prodMap X X' Y Y'
            (compactlyGenerated.{u} X) (compactlyGenerated.{u} X')
            (compactlyGenerated.{u} Y) (compactlyGenerated.{u} Y')
            (@ContinuousMap.compactlyGeneratedMap.{u} X X' tX tX' f)
            (@ContinuousMap.compactlyGeneratedMap.{u} Y Y' tY tY' g)))
        (show @ContinuousMap (X × Y) (X × Y)
          (compactlyGenerated.{u} (X × Y))
          (@compactlyGenerated.{u} (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y))) from
          let e := (@Homeomorph.symm (X × Y) (X × Y)
            (@compactlyGenerated.{u} (X × Y)
              (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                (compactlyGenerated.{u} Y)))
            (compactlyGenerated.{u} (X × Y)) (compactlyGeneratedProdComparison.{u} X Y))
          @ContinuousMap.mk (X × Y) (X × Y)
            (compactlyGenerated.{u} (X × Y))
            (@compactlyGenerated.{u} (X × Y)
              (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                (compactlyGenerated.{u} Y)))
            (@Homeomorph.toEquiv (X × Y) (X × Y)
              (compactlyGenerated.{u} (X × Y))
              (@compactlyGenerated.{u} (X × Y)
                (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y))) e)
            (@Homeomorph.continuous_toFun (X × Y) (X × Y)
              (compactlyGenerated.{u} (X × Y))
              (@compactlyGenerated.{u} (X × Y)
                (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y))) e)) := by
  exact ContinuousMap.compactlyGeneratedProdBackward_naturality.{u} f g

/-- Agreement with the locally compact generated first-factor comparison. -/
theorem compactlyGeneratedProdComparison_symm_comp_counits
    (P : Type v) (A : Type w) [tP : TopologicalSpace P] [tA : TopologicalSpace A]
    [UCompactlyGeneratedSpace.{u} P] [LocallyCompactSpace P] :
    @ContinuousMap.comp (P × A) (P × A) (P × A)
        (compactlyGenerated.{u} (P × A))
        (@compactlyGenerated.{u} (P × A)
          (@instTopologicalSpaceProd P A (compactlyGenerated.{u} P)
            (compactlyGenerated.{u} A)))
        (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
        (@ContinuousMap.comp (P × A) (P × A) (P × A)
          (@compactlyGenerated.{u} (P × A)
            (@instTopologicalSpaceProd P A (compactlyGenerated.{u} P)
              (compactlyGenerated.{u} A)))
          (@instTopologicalSpaceProd P A (compactlyGenerated.{u} P)
            (compactlyGenerated.{u} A))
          (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
          (@ContinuousMap.prodMap P P A A (compactlyGenerated.{u} P) tP
            (compactlyGenerated.{u} A) (compactlyGenerated.{u} A)
            (@ContinuousMap.compactlyGeneratedCounit.{u} P tP)
            (@ContinuousMap.id A (compactlyGenerated.{u} A)))
          (@ContinuousMap.compactlyGeneratedCounit.{u} (P × A)
            (@instTopologicalSpaceProd P A (compactlyGenerated.{u} P)
              (compactlyGenerated.{u} A))))
        (show @ContinuousMap (P × A) (P × A)
          (compactlyGenerated.{u} (P × A))
          (@compactlyGenerated.{u} (P × A)
            (@instTopologicalSpaceProd P A (compactlyGenerated.{u} P)
              (compactlyGenerated.{u} A))) from
          let e := (@Homeomorph.symm (P × A) (P × A)
            (@compactlyGenerated.{u} (P × A)
              (@instTopologicalSpaceProd P A (compactlyGenerated.{u} P)
                (compactlyGenerated.{u} A)))
            (compactlyGenerated.{u} (P × A)) (compactlyGeneratedProdComparison.{u} P A))
          @ContinuousMap.mk (P × A) (P × A)
            (compactlyGenerated.{u} (P × A))
            (@compactlyGenerated.{u} (P × A)
              (@instTopologicalSpaceProd P A (compactlyGenerated.{u} P)
                (compactlyGenerated.{u} A)))
            (@Homeomorph.toEquiv (P × A) (P × A)
              (compactlyGenerated.{u} (P × A))
              (@compactlyGenerated.{u} (P × A)
                (@instTopologicalSpaceProd P A (compactlyGenerated.{u} P)
                  (compactlyGenerated.{u} A))) e)
            (@Homeomorph.continuous_toFun (P × A) (P × A)
              (compactlyGenerated.{u} (P × A))
              (@compactlyGenerated.{u} (P × A)
                (@instTopologicalSpaceProd P A (compactlyGenerated.{u} P)
                  (compactlyGenerated.{u} A))) e)) =
      (show @ContinuousMap (P × A) (P × A)
        (compactlyGenerated.{u} (P × A))
        (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A)) from
        let e := (compactlyGeneratedProd.{u} P A)
        @ContinuousMap.mk (P × A) (P × A)
          (compactlyGenerated.{u} (P × A))
          (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
          (@Homeomorph.toEquiv (P × A) (P × A)
            (compactlyGenerated.{u} (P × A))
            (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A)) e)
          (@Homeomorph.continuous_toFun (P × A) (P × A)
            (compactlyGenerated.{u} (P × A))
            (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A)) e)) := by
  apply @ContinuousMap.ext (P × A) (P × A)
    (compactlyGenerated.{u} (P × A))
    (@instTopologicalSpaceProd P A tP (compactlyGenerated.{u} A))
  intro p
  change p = compactlyGeneratedProd.{u} P A p
  exact (compactlyGeneratedProd_apply.{u} P A p).symm

/-- Transport the fixed-universe compactly generated topology to the stock compact-probe family. -/
def compactlyGeneratedToGeneratedByCompHaus (X : Type v) [tX : TopologicalSpace X] :
    @Homeomorph X (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
      (compactlyGenerated.{u} X) (tX.generatedBy (fun K : CompHaus.{u} => K)) :=
  @Homeomorph.mk X (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
    (compactlyGenerated.{u} X) (tX.generatedBy (fun K : CompHaus.{u} => K))
    ((WithGeneratedByTopology.equiv
      (X := fun K : CompHaus.{u} => K) (Y := X)).symm)
    (by
      change @Continuous X X (compactlyGenerated.{u} X)
        (tX.generatedBy (fun K : CompHaus.{u} => K)) id
      rw [TopologicalSpace.compactlyGenerated_eq_generatedBy_compHaus]
      exact @continuous_id X (tX.generatedBy (fun K : CompHaus.{u} => K)))
    (by
      change @Continuous X X (tX.generatedBy (fun K : CompHaus.{u} => K))
        (compactlyGenerated.{u} X) id
      rw [TopologicalSpace.compactlyGenerated_eq_generatedBy_compHaus]
      exact @continuous_id X (tX.generatedBy (fun K : CompHaus.{u} => K)))

@[simp]
theorem compactlyGeneratedToGeneratedByCompHaus_apply (X : Type v) [TopologicalSpace X] (x : X) :
    WithGeneratedByTopology.equiv
      (X := fun K : CompHaus.{u} => K) (Y := X)
      (@Homeomorph.toEquiv X (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
        (compactlyGenerated.{u} X)
        ((inferInstance : TopologicalSpace X).generatedBy (fun K : CompHaus.{u} => K))
        (compactlyGeneratedToGeneratedByCompHaus.{u} X) x) = x := by
  exact Equiv.apply_symm_apply _ x

@[simp]
theorem compactlyGeneratedToGeneratedByCompHaus_symm_apply
    (X : Type v) [tX : TopologicalSpace X]
    (x : WithGeneratedByTopology (fun K : CompHaus.{u} => K) X) :
    @Homeomorph.toEquiv (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X) X
        (tX.generatedBy (fun K : CompHaus.{u} => K)) (compactlyGenerated.{u} X)
        (@Homeomorph.symm X (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
          (compactlyGenerated.{u} X) (tX.generatedBy (fun K : CompHaus.{u} => K))
          (compactlyGeneratedToGeneratedByCompHaus.{u} X)) x =
      WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} => K) (Y := X) x := by
  rfl

end Homeomorph

namespace ContinuousMap

/-- The fixed-universe forward map is the compact Hausdorff specialization of the
stock family comparison, after the canonical topology transports. -/
theorem compactlyGeneratedProdForward_generatedBy (X : Type v) (Y : Type w)
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] :
    @ContinuousMap.comp (X × Y) (X × Y)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        (compactlyGenerated.{u} (X × Y))
        ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K))
        (show @ContinuousMap (X × Y)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
          (compactlyGenerated.{u} (X × Y))
          ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K)) from
          let e := (Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (X × Y))
          @ContinuousMap.mk (X × Y) (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
            (compactlyGenerated.{u} (X × Y))
            ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K))
            (@Homeomorph.toEquiv (X × Y)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
              (compactlyGenerated.{u} (X × Y))
              ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K)) e)
            (@Homeomorph.continuous_toFun (X × Y)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
              (compactlyGenerated.{u} (X × Y))
              ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K)) e))
        (compactlyGeneratedProdForward.{u} X Y) =
      @ContinuousMap.comp (X × Y)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
            WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y))
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        ((@instTopologicalSpaceProd
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
          (tX.generatedBy (fun K : CompHaus.{u} => K))
          (tY.generatedBy (fun K : CompHaus.{u} => K))).generatedBy
            (fun K : CompHaus.{u} => K))
        ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K))
        (WithGeneratedByTopology.prodForward (fun K : CompHaus.{u} => K) X Y)
        (@ContinuousMap.comp (X × Y)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
              WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y))
          (@compactlyGenerated.{u} (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y)))
          ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K))
          ((@instTopologicalSpaceProd
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
            (tX.generatedBy (fun K : CompHaus.{u} => K))
            (tY.generatedBy (fun K : CompHaus.{u} => K))).generatedBy
              (fun K : CompHaus.{u} => K))
          (@WithGeneratedByTopology.mapContinuousMap _ (fun K : CompHaus.{u} => K)
            (fun _ => inferInstance) (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y))
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
              WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
            (@instTopologicalSpaceProd
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
              (tX.generatedBy (fun K : CompHaus.{u} => K))
              (tY.generatedBy (fun K : CompHaus.{u} => K)))
            (@ContinuousMap.prodMap X
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X) Y
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
              (compactlyGenerated.{u} X) (tX.generatedBy (fun K : CompHaus.{u} => K))
              (compactlyGenerated.{u} Y) (tY.generatedBy (fun K : CompHaus.{u} => K))
              (show @ContinuousMap X
                (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
                (compactlyGenerated.{u} X) (tX.generatedBy (fun K : CompHaus.{u} => K)) from
                let e := (Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} X)
                @ContinuousMap.mk X (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
                  (compactlyGenerated.{u} X)
                  (tX.generatedBy (fun K : CompHaus.{u} => K))
                  (@Homeomorph.toEquiv X (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
                    (compactlyGenerated.{u} X)
                    (tX.generatedBy (fun K : CompHaus.{u} => K)) e)
                  (@Homeomorph.continuous_toFun X
                    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
                    (compactlyGenerated.{u} X)
                    (tX.generatedBy (fun K : CompHaus.{u} => K)) e))
              (show @ContinuousMap Y
                (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
                (compactlyGenerated.{u} Y) (tY.generatedBy (fun K : CompHaus.{u} => K)) from
                let e := (Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} Y)
                @ContinuousMap.mk Y (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
                  (compactlyGenerated.{u} Y)
                  (tY.generatedBy (fun K : CompHaus.{u} => K))
                  (@Homeomorph.toEquiv Y (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
                    (compactlyGenerated.{u} Y)
                    (tY.generatedBy (fun K : CompHaus.{u} => K)) e)
                  (@Homeomorph.continuous_toFun Y
                    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
                    (compactlyGenerated.{u} Y)
                    (tY.generatedBy (fun K : CompHaus.{u} => K)) e))))
          (show @ContinuousMap (X × Y)
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
            (@compactlyGenerated.{u} (X × Y)
              (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                (compactlyGenerated.{u} Y)))
            ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K)) from
            let e := (@Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (X × Y)
              (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                (compactlyGenerated.{u} Y)))
            @ContinuousMap.mk (X × Y) (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
              (@compactlyGenerated.{u} (X × Y)
                (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y)))
              ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K))
              (@Homeomorph.toEquiv (X × Y)
                (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
                (@compactlyGenerated.{u} (X × Y)
                  (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                    (compactlyGenerated.{u} Y)))
                ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K)) e)
              (@Homeomorph.continuous_toFun (X × Y)
                (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
                (@compactlyGenerated.{u} (X × Y)
                  (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                    (compactlyGenerated.{u} Y)))
                ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K)) e))) := by
  apply @ContinuousMap.ext (X × Y)
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
    (@compactlyGenerated.{u} (X × Y)
      (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
        (compactlyGenerated.{u} Y)))
    ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K))
  intro p
  exact compactlyGeneratedProdForward_compHaus.{u} X Y p

/-- The fixed-universe lifted projection pair is the corresponding stock compact-probe
backward map, under the same canonical topology transports. -/
theorem compactlyGeneratedProdBackward_generatedBy (X : Type v) (Y : Type w)
    [tX : TopologicalSpace X] [tY : TopologicalSpace Y] :
    @ContinuousMap.comp (X × Y) (X × Y)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
            WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y))
        (compactlyGenerated.{u} (X × Y))
        (@compactlyGenerated.{u} (X × Y)
          (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)))
        ((@instTopologicalSpaceProd
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
          (tX.generatedBy (fun K : CompHaus.{u} => K))
          (tY.generatedBy (fun K : CompHaus.{u} => K))).generatedBy
            (fun K : CompHaus.{u} => K))
        (@ContinuousMap.comp (X × Y)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
              WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y))
          (@compactlyGenerated.{u} (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y)))
          ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
            (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K))
          ((@instTopologicalSpaceProd
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
            (tX.generatedBy (fun K : CompHaus.{u} => K))
            (tY.generatedBy (fun K : CompHaus.{u} => K))).generatedBy
              (fun K : CompHaus.{u} => K))
          (@WithGeneratedByTopology.mapContinuousMap _ (fun K : CompHaus.{u} => K)
            (fun _ => inferInstance) (X × Y)
            (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y))
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
              WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
            (@instTopologicalSpaceProd
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
              (tX.generatedBy (fun K : CompHaus.{u} => K))
              (tY.generatedBy (fun K : CompHaus.{u} => K)))
            (@ContinuousMap.prodMap X
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X) Y
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
              (compactlyGenerated.{u} X) (tX.generatedBy (fun K : CompHaus.{u} => K))
              (compactlyGenerated.{u} Y) (tY.generatedBy (fun K : CompHaus.{u} => K))
              (show @ContinuousMap X
                (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
                (compactlyGenerated.{u} X) (tX.generatedBy (fun K : CompHaus.{u} => K)) from
                let e := (Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} X)
                @ContinuousMap.mk X (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
                  (compactlyGenerated.{u} X)
                  (tX.generatedBy (fun K : CompHaus.{u} => K))
                  (@Homeomorph.toEquiv X (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
                    (compactlyGenerated.{u} X)
                    (tX.generatedBy (fun K : CompHaus.{u} => K)) e)
                  (@Homeomorph.continuous_toFun X
                    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
                    (compactlyGenerated.{u} X)
                    (tX.generatedBy (fun K : CompHaus.{u} => K)) e))
              (show @ContinuousMap Y
                (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
                (compactlyGenerated.{u} Y) (tY.generatedBy (fun K : CompHaus.{u} => K)) from
                let e := (Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} Y)
                @ContinuousMap.mk Y (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
                  (compactlyGenerated.{u} Y)
                  (tY.generatedBy (fun K : CompHaus.{u} => K))
                  (@Homeomorph.toEquiv Y (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
                    (compactlyGenerated.{u} Y)
                    (tY.generatedBy (fun K : CompHaus.{u} => K)) e)
                  (@Homeomorph.continuous_toFun Y
                    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
                    (compactlyGenerated.{u} Y)
                    (tY.generatedBy (fun K : CompHaus.{u} => K)) e))))
          (show @ContinuousMap (X × Y)
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
            (@compactlyGenerated.{u} (X × Y)
              (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                (compactlyGenerated.{u} Y)))
            ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
              (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K)) from
            let e := (@Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (X × Y)
              (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                (compactlyGenerated.{u} Y)))
            @ContinuousMap.mk (X × Y) (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
              (@compactlyGenerated.{u} (X × Y)
                (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y)))
              ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K))
              (@Homeomorph.toEquiv (X × Y)
                (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
                (@compactlyGenerated.{u} (X × Y)
                  (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                    (compactlyGenerated.{u} Y)))
                ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K)) e)
              (@Homeomorph.continuous_toFun (X × Y)
                (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
                (@compactlyGenerated.{u} (X × Y)
                  (@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                    (compactlyGenerated.{u} Y)))
                ((@instTopologicalSpaceProd X Y (compactlyGenerated.{u} X)
                  (compactlyGenerated.{u} Y)).generatedBy (fun K : CompHaus.{u} => K)) e)))
        (compactlyGeneratedProdBackward.{u} X Y) =
      @ContinuousMap.comp (X × Y)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
            WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y))
        (compactlyGenerated.{u} (X × Y))
        ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K))
        ((@instTopologicalSpaceProd
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
          (tX.generatedBy (fun K : CompHaus.{u} => K))
          (tY.generatedBy (fun K : CompHaus.{u} => K))).generatedBy
            (fun K : CompHaus.{u} => K))
        (WithGeneratedByTopology.prodBackward (fun K : CompHaus.{u} => K) X Y)
        (show @ContinuousMap (X × Y)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
          (compactlyGenerated.{u} (X × Y))
          ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K)) from
          let e := (Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (X × Y))
          @ContinuousMap.mk (X × Y) (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
            (compactlyGenerated.{u} (X × Y))
            ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K))
            (@Homeomorph.toEquiv (X × Y)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
              (compactlyGenerated.{u} (X × Y))
              ((@instTopologicalSpaceProd X Y tX tY).generatedBy (fun K : CompHaus.{u} => K)) e)
            (@Homeomorph.continuous_toFun (X × Y)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X × Y))
              (compactlyGenerated.{u} (X × Y))
              ((@instTopologicalSpaceProd X Y tX tY).generatedBy
                (fun K : CompHaus.{u} => K)) e)) := by
  apply @ContinuousMap.ext (X × Y)
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X ×
        WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y))
    (compactlyGenerated.{u} (X × Y))
    ((@instTopologicalSpaceProd
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) X)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) Y)
      (tX.generatedBy (fun K : CompHaus.{u} => K))
      (tY.generatedBy (fun K : CompHaus.{u} => K))).generatedBy
        (fun K : CompHaus.{u} => K))
  intro p
  exact compactlyGeneratedProdBackward_compHaus.{u} X Y p

end ContinuousMap
