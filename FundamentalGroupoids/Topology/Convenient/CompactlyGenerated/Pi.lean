/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Convenient.CompactlyGenerated.Prod
public import FundamentalGroupoids.Topology.Convenient.GeneratedBy.Pi

/-!
# Dependent products refined by compact Hausdorff probes

For an arbitrary family of original spaces, compact generation of the product of
its compactly generated factors is canonically homeomorphic to compact generation
of the original product. The probe universe is independent of the index and carrier
universes. Both outer refinements are retained; no generatedness of an ordinary
product is asserted.

The forward map refines the family of counits. The reverse map lifts the family of
refined original evaluations from its generated source. The inverse laws are
transported from the generated-by comparison using the compact Hausdorff family.
Pair evaluations relate the comparison to the binary comparison.
-/

@[expose] public section

noncomputable section

universe u t v w

open TopologicalSpace Topology

namespace ContinuousMap

variable {I : Type t}

/-- Refine the family of counits into the original dependent product. -/
def compactlyGeneratedPiForward (X : I → Type v) [tX : ∀ i, TopologicalSpace (X i)] :
    @ContinuousMap (∀ i, X i) (∀ i, X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i)) :=
  @compactlyGeneratedMap.{u} (∀ i, X i) (∀ i, X i)
    (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
    (@Pi.topologicalSpace I X tX)
    (@ContinuousMap.piMap I X X (fun i => compactlyGenerated.{u} (X i)) tX
      (fun i => compactlyGeneratedCounit.{u} (X i)))

/-- Lift the family of refined original evaluations from its generated source. -/
def compactlyGeneratedPiBackward (X : I → Type v) [tX : ∀ i, TopologicalSpace (X i)] :
    @ContinuousMap (∀ i, X i) (∀ i, X i)
      (compactlyGenerated.{u} (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) :=
  toCompactlyGenerated.{u}
    (tZ := compactlyGenerated.{u} (∀ i, X i))
    (tX := @Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
    (@ContinuousMap.pi I (∀ i, X i) X
      (compactlyGenerated.{u} (∀ i, X i))
      (fun i => compactlyGenerated.{u} (X i))
      (fun i => @compactlyGeneratedMap.{u} (∀ i, X i) (X i)
        (@Pi.topologicalSpace I X tX) (tX i) (@ContinuousMap.eval I X tX i)))

variable (X : I → Type v) [tX : ∀ i, TopologicalSpace (X i)]

@[simp]
theorem compactlyGeneratedPiForward_apply (x : ∀ i, X i) :
    compactlyGeneratedPiForward.{u} X x = x := rfl

@[simp]
theorem compactlyGeneratedPiBackward_apply (x : ∀ i, X i) :
    compactlyGeneratedPiBackward.{u} X x = x := rfl

/-- Each coordinate of the forward comparison is the original coordinate. -/
theorem compactlyGeneratedPiForward_eval_apply (x : ∀ i, X i) (i : I) :
    compactlyGeneratedPiForward.{u} X x i = x i := by
  rw [compactlyGeneratedPiForward_apply]

/-- Each coordinate of the reverse comparison is the original coordinate. -/
theorem compactlyGeneratedPiBackward_eval_apply (x : ∀ i, X i) (i : I) :
    compactlyGeneratedPiBackward.{u} X x i = x i := by
  rw [compactlyGeneratedPiBackward_apply]

/-- The forward comparison commutes with the original-product counit. -/
theorem compactlyGeneratedPiForward_counit :
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i)) (@Pi.topologicalSpace I X tX)
      (compactlyGeneratedCounit.{u} (∀ i, X i)) (compactlyGeneratedPiForward.{u} X) =
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
      (@Pi.topologicalSpace I X tX)
      (@ContinuousMap.piMap I X X (fun i => compactlyGenerated.{u} (X i)) tX
        (fun i => compactlyGeneratedCounit.{u} (X i)))
      (@compactlyGeneratedCounit.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) := by
  apply DFunLike.ext
  intro x
  rfl

/-- The counit of the reverse comparison is the family of refined evaluations. -/
theorem compactlyGeneratedPiBackward_counit :
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, X i)
      (compactlyGenerated.{u} (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
      (@compactlyGeneratedCounit.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGeneratedPiBackward.{u} X) =
    @ContinuousMap.pi I (∀ i, X i) X
      (compactlyGenerated.{u} (∀ i, X i))
      (fun i => compactlyGenerated.{u} (X i))
      (fun i => @compactlyGeneratedMap.{u} (∀ i, X i) (X i)
        (@Pi.topologicalSpace I X tX) (tX i) (@ContinuousMap.eval I X tX i)) := by
  apply DFunLike.ext
  intro x
  rfl

/-- A refined original evaluation after the forward map is the source evaluation. -/
theorem compactlyGeneratedPiForward_eval (i : I) :
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i)) (compactlyGenerated.{u} (X i))
      (@compactlyGeneratedMap.{u} (∀ i, X i) (X i)
        (@Pi.topologicalSpace I X tX) (tX i) (@ContinuousMap.eval I X tX i))
      (compactlyGeneratedPiForward.{u} X) =
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
      (compactlyGenerated.{u} (X i))
      (@ContinuousMap.eval I X (fun i => compactlyGenerated.{u} (X i)) i)
      (@compactlyGeneratedCounit.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) := by
  apply DFunLike.ext
  intro x
  rfl

/-- Evaluation after the reverse comparison recovers the refined original evaluation. -/
theorem compactlyGeneratedPiBackward_eval (i : I) :
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (X i)
      (compactlyGenerated.{u} (∀ i, X i))
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
      (compactlyGenerated.{u} (X i))
      (@ContinuousMap.eval I X (fun i => compactlyGenerated.{u} (X i)) i)
      (@ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, X i)
        (compactlyGenerated.{u} (∀ i, X i))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
        (@compactlyGeneratedCounit.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        (compactlyGeneratedPiBackward.{u} X)) =
    @compactlyGeneratedMap.{u} (∀ i, X i) (X i)
      (@Pi.topologicalSpace I X tX) (tX i) (@ContinuousMap.eval I X tX i) := by
  apply DFunLike.ext
  intro x
  rfl

variable {X} {Y : I → Type w} [tY : ∀ i, TopologicalSpace (Y i)]

/-- The forward comparison is natural in every coordinate simultaneously. -/
theorem compactlyGeneratedPiForward_naturality (f : ∀ i, C(X i, Y i)) :
    @ContinuousMap.comp (∀ i, X i) (∀ i, Y i) (∀ i, Y i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (@compactlyGenerated.{u} (∀ i, Y i)
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
      (compactlyGenerated.{u} (∀ i, Y i))
      (compactlyGeneratedPiForward.{u} Y)
      (@compactlyGeneratedMap.{u} (∀ i, X i) (∀ i, Y i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i)))
        (@ContinuousMap.piMap I X Y
          (fun i => compactlyGenerated.{u} (X i)) (fun i => compactlyGenerated.{u} (Y i))
          (fun i => compactlyGeneratedMap.{u} (f i)))) =
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, Y i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i)) (compactlyGenerated.{u} (∀ i, Y i))
      (compactlyGeneratedMap.{u} (ContinuousMap.piMap f))
      (compactlyGeneratedPiForward.{u} X) := by
  apply DFunLike.ext
  intro x
  funext i
  simp [ContinuousMap.comp_apply]

/-- The reverse comparison is natural in every coordinate simultaneously. -/
theorem compactlyGeneratedPiBackward_naturality (f : ∀ i, C(X i, Y i)) :
    @ContinuousMap.comp (∀ i, X i) (∀ i, Y i) (∀ i, Y i)
      (compactlyGenerated.{u} (∀ i, X i)) (compactlyGenerated.{u} (∀ i, Y i))
      (@compactlyGenerated.{u} (∀ i, Y i)
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
      (compactlyGeneratedPiBackward.{u} Y)
      (compactlyGeneratedMap.{u} (ContinuousMap.piMap f)) =
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, Y i)
      (compactlyGenerated.{u} (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (@compactlyGenerated.{u} (∀ i, Y i)
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
      (@compactlyGeneratedMap.{u} (∀ i, X i) (∀ i, Y i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i)))
        (@ContinuousMap.piMap I X Y
          (fun i => compactlyGenerated.{u} (X i)) (fun i => compactlyGenerated.{u} (Y i))
          (fun i => compactlyGeneratedMap.{u} (f i))))
      (compactlyGeneratedPiBackward.{u} X) := by
  apply DFunLike.ext
  intro x
  funext i
  simp [ContinuousMap.comp_apply]

variable (X)

/-- Pair evaluations intertwine the forward dependent and binary comparisons. -/
theorem compactlyGeneratedPiForward_pair_eval (i j : I) :
    @ContinuousMap.comp (∀ k, X k) (X i × X j) (X i × X j)
      (@compactlyGenerated.{u} (∀ k, X k)
        (@Pi.topologicalSpace I X (fun k => compactlyGenerated.{u} (X k))))
      (@compactlyGenerated.{u} (X i × X j)
        (@instTopologicalSpaceProd (X i) (X j)
          (compactlyGenerated.{u} (X i)) (compactlyGenerated.{u} (X j))))
      (compactlyGenerated.{u} (X i × X j))
      (compactlyGeneratedProdForward.{u} (X i) (X j))
      (@compactlyGeneratedMap.{u} (∀ k, X k) (X i × X j)
        (@Pi.topologicalSpace I X (fun k => compactlyGenerated.{u} (X k)))
        (@instTopologicalSpaceProd (X i) (X j)
          (compactlyGenerated.{u} (X i)) (compactlyGenerated.{u} (X j)))
        (@ContinuousMap.prodMk (∀ k, X k)
          (@Pi.topologicalSpace I X (fun k => compactlyGenerated.{u} (X k)))
          (X i) (X j) (compactlyGenerated.{u} (X i)) (compactlyGenerated.{u} (X j))
          (@ContinuousMap.eval I X (fun k => compactlyGenerated.{u} (X k)) i)
          (@ContinuousMap.eval I X (fun k => compactlyGenerated.{u} (X k)) j))) =
    @ContinuousMap.comp (∀ k, X k) (∀ k, X k) (X i × X j)
      (@compactlyGenerated.{u} (∀ k, X k)
        (@Pi.topologicalSpace I X (fun k => compactlyGenerated.{u} (X k))))
      (compactlyGenerated.{u} (∀ k, X k)) (compactlyGenerated.{u} (X i × X j))
      (compactlyGeneratedMap.{u}
        ((ContinuousMap.eval i : C(∀ k, X k, X i)).prodMk
          (ContinuousMap.eval j : C(∀ k, X k, X j))))
      (compactlyGeneratedPiForward.{u} X) := by
  apply DFunLike.ext
  intro x
  apply Prod.ext <;> simp [ContinuousMap.comp_apply]

/-- Pair evaluations intertwine the reverse dependent and binary comparisons. -/
theorem compactlyGeneratedPiBackward_pair_eval (i j : I) :
    @ContinuousMap.comp (∀ k, X k) (X i × X j) (X i × X j)
      (compactlyGenerated.{u} (∀ k, X k)) (compactlyGenerated.{u} (X i × X j))
      (@compactlyGenerated.{u} (X i × X j)
        (@instTopologicalSpaceProd (X i) (X j)
          (compactlyGenerated.{u} (X i)) (compactlyGenerated.{u} (X j))))
      (compactlyGeneratedProdBackward.{u} (X i) (X j))
      (compactlyGeneratedMap.{u}
        ((ContinuousMap.eval i : C(∀ k, X k, X i)).prodMk
          (ContinuousMap.eval j : C(∀ k, X k, X j)))) =
    @ContinuousMap.comp (∀ k, X k) (∀ k, X k) (X i × X j)
      (compactlyGenerated.{u} (∀ k, X k))
      (@compactlyGenerated.{u} (∀ k, X k)
        (@Pi.topologicalSpace I X (fun k => compactlyGenerated.{u} (X k))))
      (@compactlyGenerated.{u} (X i × X j)
        (@instTopologicalSpaceProd (X i) (X j)
          (compactlyGenerated.{u} (X i)) (compactlyGenerated.{u} (X j))))
      (@compactlyGeneratedMap.{u} (∀ k, X k) (X i × X j)
        (@Pi.topologicalSpace I X (fun k => compactlyGenerated.{u} (X k)))
        (@instTopologicalSpaceProd (X i) (X j)
          (compactlyGenerated.{u} (X i)) (compactlyGenerated.{u} (X j)))
        (@ContinuousMap.prodMk (∀ k, X k)
          (@Pi.topologicalSpace I X (fun k => compactlyGenerated.{u} (X k)))
          (X i) (X j) (compactlyGenerated.{u} (X i)) (compactlyGenerated.{u} (X j))
          (@ContinuousMap.eval I X (fun k => compactlyGenerated.{u} (X k)) i)
          (@ContinuousMap.eval I X (fun k => compactlyGenerated.{u} (X k)) j)))
      (compactlyGeneratedPiBackward.{u} X) := by
  apply DFunLike.ext
  intro x
  apply Prod.ext <;> simp [ContinuousMap.comp_apply]

private def compactlyGeneratedPiCompHausMap (S : Type v) [tS : TopologicalSpace S] :
    @ContinuousMap S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
      (compactlyGenerated.{u} S) (tS.generatedBy (fun K : CompHaus.{u} => K)) :=
  let h := Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} S
  @ContinuousMap.mk S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
    (compactlyGenerated.{u} S) (tS.generatedBy (fun K : CompHaus.{u} => K))
    (@Homeomorph.toEquiv S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
      (compactlyGenerated.{u} S) (tS.generatedBy (fun K : CompHaus.{u} => K)) h)
    (@Homeomorph.continuous_toFun S
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
      (compactlyGenerated.{u} S) (tS.generatedBy (fun K : CompHaus.{u} => K)) h)

private def compactlyGeneratedPiCompHausPoint (S : Type v) [tS : TopologicalSpace S] :
    S → WithGeneratedByTopology (fun K : CompHaus.{u} => K) S :=
  @ContinuousMap.toFun S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
    (compactlyGenerated.{u} S) (tS.generatedBy (fun K : CompHaus.{u} => K))
    (compactlyGeneratedPiCompHausMap.{u} S)

private theorem compactlyGeneratedPiCompHausMap_apply
    (S : Type v) [TopologicalSpace S] (s : S) :
    WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} => K) (Y := S)
      (compactlyGeneratedPiCompHausPoint.{u} S s) = s :=
  Homeomorph.compactlyGeneratedToGeneratedByCompHaus_apply.{u} S s

private def compactlyGeneratedPiCompHausTransport :
    @ContinuousMap (∀ i, X i)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
        (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      ((@Pi.topologicalSpace I
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
          (fun K : CompHaus.{u} => K)) :=
  @ContinuousMap.comp (∀ i, X i)
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
      (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
    (@compactlyGenerated.{u} (∀ i, X i)
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
    ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
      (fun K : CompHaus.{u} => K))
    ((@Pi.topologicalSpace I
      (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
      (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
        (fun K : CompHaus.{u} => K))
    (@WithGeneratedByTopology.mapContinuousMap _ (fun K : CompHaus.{u} => K)
      (fun _ => inferInstance) (∀ i, X i)
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
      (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
      (@Pi.topologicalSpace I
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K)))
      (@ContinuousMap.piMap I X
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => compactlyGenerated.{u} (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))
        (fun i => compactlyGeneratedPiCompHausMap.{u} (X i))))
    (@compactlyGeneratedPiCompHausMap.{u} (∀ i, X i)
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))

private def compactlyGeneratedPiCompHausTransportPoint :
    (∀ i, X i) → WithGeneratedByTopology (fun K : CompHaus.{u} => K)
      (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)) :=
  @ContinuousMap.toFun (∀ i, X i)
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
      (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
    (@compactlyGenerated.{u} (∀ i, X i)
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
    ((@Pi.topologicalSpace I
      (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
      (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
        (fun K : CompHaus.{u} => K))
    (compactlyGeneratedPiCompHausTransport.{u} X)

private theorem compactlyGeneratedPiCompHausTransport_apply_eval
    (x : ∀ i, X i) (i : I) :
    WithGeneratedByTopology.equiv (X := fun K : CompHaus.{u} => K) (Y := X i)
      ((WithGeneratedByTopology.equiv
        (X := fun K : CompHaus.{u} => K)
        (Y := ∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (compactlyGeneratedPiCompHausTransportPoint.{u} X x)) i) = x i := by
  let r : @ContinuousMap (∀ i, X i)
      (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
      (@Pi.topologicalSpace I
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))) :=
    @ContinuousMap.piMap I X
      (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
      (fun i => compactlyGenerated.{u} (X i))
      (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))
      (fun i => compactlyGeneratedPiCompHausMap.{u} (X i))
  have h := congrArg (fun z => WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := X i) (z i))
    (@WithGeneratedByTopology.equiv_mapContinuousMap _ (fun K : CompHaus.{u} => K)
      (fun _ => inferInstance) (∀ i, X i)
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
      (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
      (@Pi.topologicalSpace I
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))) r
      (@compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))) x))
  change WithGeneratedByTopology.equiv
      (X := fun K : CompHaus.{u} => K) (Y := X i)
      ((WithGeneratedByTopology.equiv
        (X := fun K : CompHaus.{u} => K)
        (Y := ∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (compactlyGeneratedPiCompHausTransportPoint.{u} X x)) i) =
    WithGeneratedByTopology.equiv
      (X := fun K : CompHaus.{u} => K) (Y := X i)
      (compactlyGeneratedPiCompHausPoint.{u} (X i)
        ((WithGeneratedByTopology.equiv
          (X := fun K : CompHaus.{u} => K) (Y := ∀ i, X i)
          (@compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))) x)) i)) at h
  exact h.trans ((compactlyGeneratedPiCompHausMap_apply.{u} (X i) _).trans
    (congrFun (@compactlyGeneratedPiCompHausMap_apply.{u} (∀ i, X i)
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))) x) i))

private theorem compactlyGeneratedPiCompHausTransport_injective :
    Function.Injective (compactlyGeneratedPiCompHausTransportPoint.{u} X) := by
  intro x y h
  funext i
  have hi := congrArg (fun z => WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := X i)
    ((WithGeneratedByTopology.equiv
      (X := fun K : CompHaus.{u} => K)
      (Y := ∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)) z) i)) h
  simpa only [compactlyGeneratedPiCompHausTransport_apply_eval] using hi

/-- The forward comparison agrees with the generated-by comparison under the
compact Hausdorff transports, including refinement of the refined-factor product. -/
theorem compactlyGeneratedPiForward_generatedBy :
    let hO : @ContinuousMap (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (compactlyGenerated.{u} (∀ i, X i))
        ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K)) :=
      let h := Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (∀ i, X i)
      @ContinuousMap.mk (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (compactlyGenerated.{u} (∀ i, X i))
        ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K))
        (@Homeomorph.toEquiv (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
          (compactlyGenerated.{u} (∀ i, X i))
          ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K)) h)
        (@Homeomorph.continuous_toFun (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
          (compactlyGenerated.{u} (∀ i, X i))
          ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K)) h)
    let hP : @ContinuousMap (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
          (fun K : CompHaus.{u} => K)) :=
      let h := @Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
      @ContinuousMap.mk (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
          (fun K : CompHaus.{u} => K))
        (@Homeomorph.toEquiv (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
            (fun K : CompHaus.{u} => K)) h)
        (@Homeomorph.continuous_toFun (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
            (fun K : CompHaus.{u} => K)) h)
    let r : @ContinuousMap (∀ i, X i)
        (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
        (@Pi.topologicalSpace I
          (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
          (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))) :=
      @ContinuousMap.piMap I X
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => compactlyGenerated.{u} (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))
        (fun i =>
          let h := Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (X i)
          @ContinuousMap.mk (X i)
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
            (compactlyGenerated.{u} (X i)) ((tX i).generatedBy (fun K : CompHaus.{u} => K))
            (@Homeomorph.toEquiv (X i)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
              (compactlyGenerated.{u} (X i))
              ((tX i).generatedBy (fun K : CompHaus.{u} => K)) h)
            (@Homeomorph.continuous_toFun (X i)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
              (compactlyGenerated.{u} (X i))
              ((tX i).generatedBy (fun K : CompHaus.{u} => K)) h))
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i))
      ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K))
      hO (compactlyGeneratedPiForward.{u} X) =
    @ContinuousMap.comp (∀ i, X i)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
        (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      ((@Pi.topologicalSpace I
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
          (fun K : CompHaus.{u} => K))
      ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K))
      (WithGeneratedByTopology.piForward (fun K : CompHaus.{u} => K) X)
      (@ContinuousMap.comp (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
          (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
          (fun K : CompHaus.{u} => K))
        ((@Pi.topologicalSpace I
          (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
          (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
            (fun K : CompHaus.{u} => K))
        (@WithGeneratedByTopology.mapContinuousMap _ (fun K : CompHaus.{u} => K)
          (fun _ => inferInstance) (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
          (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
          (@Pi.topologicalSpace I
            (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
            (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))) r) hP) := by
  apply @ContinuousMap.ext (∀ i, X i)
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
    (@compactlyGenerated.{u} (∀ i, X i)
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
    ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K))
  intro x
  change compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i)
      (compactlyGeneratedPiForward.{u} X x) =
    WithGeneratedByTopology.piForward (fun K : CompHaus.{u} => K) X
      (compactlyGeneratedPiCompHausTransportPoint.{u} X x)
  apply (WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := ∀ i, X i)).injective
  funext i
  simpa only [compactlyGeneratedPiCompHausMap_apply, compactlyGeneratedPiForward_apply,
    WithGeneratedByTopology.equiv_piForward_apply] using
    (compactlyGeneratedPiCompHausTransport_apply_eval.{u} X x i).symm

/-- The reverse comparison agrees with the generated-source comparison under the
compact Hausdorff transports, retaining the outer generated-by node on the left. -/
theorem compactlyGeneratedPiBackward_generatedBy :
    let hO : @ContinuousMap (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (compactlyGenerated.{u} (∀ i, X i))
        ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K)) :=
      let h := Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (∀ i, X i)
      @ContinuousMap.mk (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (compactlyGenerated.{u} (∀ i, X i))
        ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K))
        (@Homeomorph.toEquiv (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
          (compactlyGenerated.{u} (∀ i, X i))
          ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K)) h)
        (@Homeomorph.continuous_toFun (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
          (compactlyGenerated.{u} (∀ i, X i))
          ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K)) h)
    let hP : @ContinuousMap (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
          (fun K : CompHaus.{u} => K)) :=
      let h := @Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
      @ContinuousMap.mk (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
          (fun K : CompHaus.{u} => K))
        (@Homeomorph.toEquiv (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
            (fun K : CompHaus.{u} => K)) h)
        (@Homeomorph.continuous_toFun (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
            (fun K : CompHaus.{u} => K)) h)
    let r : @ContinuousMap (∀ i, X i)
        (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
        (@Pi.topologicalSpace I
          (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
          (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))) :=
      @ContinuousMap.piMap I X
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => compactlyGenerated.{u} (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))
        (fun i =>
          let h := Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} (X i)
          @ContinuousMap.mk (X i)
            (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
            (compactlyGenerated.{u} (X i)) ((tX i).generatedBy (fun K : CompHaus.{u} => K))
            (@Homeomorph.toEquiv (X i)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
              (compactlyGenerated.{u} (X i))
              ((tX i).generatedBy (fun K : CompHaus.{u} => K)) h)
            (@Homeomorph.continuous_toFun (X i)
              (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
              (compactlyGenerated.{u} (X i))
              ((tX i).generatedBy (fun K : CompHaus.{u} => K)) h))
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
        (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
      (compactlyGenerated.{u} (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      ((@Pi.topologicalSpace I
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
          (fun K : CompHaus.{u} => K))
      (@ContinuousMap.comp (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
          (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        ((@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))).generatedBy
          (fun K : CompHaus.{u} => K))
        ((@Pi.topologicalSpace I
          (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
          (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
            (fun K : CompHaus.{u} => K))
        (@WithGeneratedByTopology.mapContinuousMap _ (fun K : CompHaus.{u} => K)
          (fun _ => inferInstance) (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
          (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
          (@Pi.topologicalSpace I
            (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
            (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))) r) hP)
      (compactlyGeneratedPiBackward.{u} X) =
    @ContinuousMap.comp (∀ i, X i)
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
      (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
        (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
      (compactlyGenerated.{u} (∀ i, X i))
      ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K))
      ((@Pi.topologicalSpace I
        (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
        (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
          (fun K : CompHaus.{u} => K))
      (WithGeneratedByTopology.piBackward (fun K : CompHaus.{u} => K) X) hO := by
  apply @ContinuousMap.ext (∀ i, X i)
    (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
      (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
    (compactlyGenerated.{u} (∀ i, X i))
    ((@Pi.topologicalSpace I
      (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
      (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
        (fun K : CompHaus.{u} => K))
  intro x
  change compactlyGeneratedPiCompHausTransportPoint.{u} X
      (compactlyGeneratedPiBackward.{u} X x) =
    WithGeneratedByTopology.piBackward (fun K : CompHaus.{u} => K) X
      (compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i) x)
  apply (WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K)
    (Y := ∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))).injective
  funext i
  apply (WithGeneratedByTopology.equiv
    (X := fun K : CompHaus.{u} => K) (Y := X i)).injective
  simp only [compactlyGeneratedPiCompHausTransport_apply_eval, compactlyGeneratedPiBackward_apply,
    WithGeneratedByTopology.equiv_piBackward_eval_apply,
    compactlyGeneratedPiCompHausMap_apply]

private theorem compactlyGeneratedPiCompHausMap_injective
    (S : Type v) [tS : TopologicalSpace S] :
    Function.Injective (compactlyGeneratedPiCompHausPoint.{u} S) := by
  intro x y hxy
  have h := congrArg (fun z =>
    @Homeomorph.toEquiv (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S) S
      (tS.generatedBy (fun K : CompHaus.{u} => K)) (compactlyGenerated.{u} S)
      (@Homeomorph.symm S (WithGeneratedByTopology (fun K : CompHaus.{u} => K) S)
        (compactlyGenerated.{u} S) (tS.generatedBy (fun K : CompHaus.{u} => K))
        (Homeomorph.compactlyGeneratedToGeneratedByCompHaus.{u} S)) z) hxy
  simpa only [Homeomorph.compactlyGeneratedToGeneratedByCompHaus_symm_apply,
    compactlyGeneratedPiCompHausMap_apply] using h

/-- The reverse dependent-product comparison is a left inverse of the forward map. -/
theorem compactlyGeneratedPiBackward_comp_forward :
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGeneratedPiBackward.{u} X) (compactlyGeneratedPiForward.{u} X) =
    @ContinuousMap.id (∀ i, X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) := by
  have hF := compactlyGeneratedPiForward_generatedBy.{u} X
  have hG := compactlyGeneratedPiBackward_generatedBy.{u} X
  apply DFunLike.ext
  intro x
  apply compactlyGeneratedPiCompHausTransport_injective.{u} X
  change compactlyGeneratedPiCompHausTransportPoint.{u} X
      (compactlyGeneratedPiBackward.{u} X (compactlyGeneratedPiForward.{u} X x)) =
    compactlyGeneratedPiCompHausTransportPoint.{u} X x
  calc
    compactlyGeneratedPiCompHausTransportPoint.{u} X
        (compactlyGeneratedPiBackward.{u} X (compactlyGeneratedPiForward.{u} X x)) =
      WithGeneratedByTopology.piBackward (fun K : CompHaus.{u} => K) X
        (compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i)
          (compactlyGeneratedPiForward.{u} X x)) :=
      congrArg (fun f => @ContinuousMap.toFun (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
          (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
        (compactlyGenerated.{u} (∀ i, X i))
        ((@Pi.topologicalSpace I
          (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
          (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
            (fun K : CompHaus.{u} => K)) f (compactlyGeneratedPiForward.{u} X x)) hG
    _ = WithGeneratedByTopology.piBackward (fun K : CompHaus.{u} => K) X
        (WithGeneratedByTopology.piForward (fun K : CompHaus.{u} => K) X
          (compactlyGeneratedPiCompHausTransportPoint.{u} X x)) :=
      congrArg (WithGeneratedByTopology.piBackward (fun K : CompHaus.{u} => K) X)
        (congrArg (fun f => @ContinuousMap.toFun (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K)) f x) hF)
    _ = compactlyGeneratedPiCompHausTransportPoint.{u} X x :=
      DFunLike.congr_fun (WithGeneratedByTopology.piBackward_comp_piForward
        (fun K : CompHaus.{u} => K) X) (compactlyGeneratedPiCompHausTransportPoint.{u} X x)

/-- The forward dependent-product comparison is a left inverse of the reverse map. -/
theorem compactlyGeneratedPiForward_comp_backward :
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, X i)
      (compactlyGenerated.{u} (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i))
      (compactlyGeneratedPiForward.{u} X) (compactlyGeneratedPiBackward.{u} X) =
    @ContinuousMap.id (∀ i, X i) (compactlyGenerated.{u} (∀ i, X i)) := by
  have hF := compactlyGeneratedPiForward_generatedBy.{u} X
  have hG := compactlyGeneratedPiBackward_generatedBy.{u} X
  apply DFunLike.ext
  intro x
  apply compactlyGeneratedPiCompHausMap_injective.{u} (∀ i, X i)
  change compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i)
      (compactlyGeneratedPiForward.{u} X (compactlyGeneratedPiBackward.{u} X x)) =
    compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i) x
  calc
    compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i)
        (compactlyGeneratedPiForward.{u} X (compactlyGeneratedPiBackward.{u} X x)) =
      WithGeneratedByTopology.piForward (fun K : CompHaus.{u} => K) X
        (compactlyGeneratedPiCompHausTransportPoint.{u} X
          (compactlyGeneratedPiBackward.{u} X x)) :=
      congrArg (fun f => @ContinuousMap.toFun (∀ i, X i)
        (WithGeneratedByTopology (fun K : CompHaus.{u} => K) (∀ i, X i))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        ((@Pi.topologicalSpace I X tX).generatedBy (fun K : CompHaus.{u} => K))
        f (compactlyGeneratedPiBackward.{u} X x)) hF
    _ = WithGeneratedByTopology.piForward (fun K : CompHaus.{u} => K) X
        (WithGeneratedByTopology.piBackward (fun K : CompHaus.{u} => K) X
          (compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i) x)) :=
      congrArg (WithGeneratedByTopology.piForward (fun K : CompHaus.{u} => K) X)
        (congrArg (fun f => @ContinuousMap.toFun (∀ i, X i)
          (WithGeneratedByTopology (fun K : CompHaus.{u} => K)
            (∀ i, WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i)))
          (compactlyGenerated.{u} (∀ i, X i))
          ((@Pi.topologicalSpace I
            (fun i => WithGeneratedByTopology (fun K : CompHaus.{u} => K) (X i))
            (fun i => (tX i).generatedBy (fun K : CompHaus.{u} => K))).generatedBy
              (fun K : CompHaus.{u} => K)) f x) hG)
    _ = compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i) x :=
      DFunLike.congr_fun (WithGeneratedByTopology.piForward_comp_piBackward
        (fun K : CompHaus.{u} => K) X) (compactlyGeneratedPiCompHausPoint.{u} (∀ i, X i) x)

end ContinuousMap

namespace Homeomorph

variable {I : Type t}

/-- Compact generation of the product of compactly generated factors is canonically
homeomorphic to compact generation of the original dependent product. -/
def compactlyGeneratedPiComparison (X : I → Type v)
    [tX : ∀ i, TopologicalSpace (X i)] :
    @Homeomorph (∀ i, X i) (∀ i, X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i)) :=
  @Homeomorph.mk (∀ i, X i) (∀ i, X i)
    (@compactlyGenerated.{u} (∀ i, X i)
      (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
    (compactlyGenerated.{u} (∀ i, X i))
    { toFun := ContinuousMap.compactlyGeneratedPiForward.{u} X
      invFun := ContinuousMap.compactlyGeneratedPiBackward.{u} X
      left_inv := fun x => DFunLike.congr_fun
        (ContinuousMap.compactlyGeneratedPiBackward_comp_forward.{u} X) x
      right_inv := fun x => DFunLike.congr_fun
        (ContinuousMap.compactlyGeneratedPiForward_comp_backward.{u} X) x }
    (@ContinuousMap.continuous (∀ i, X i) (∀ i, X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i))
      (ContinuousMap.compactlyGeneratedPiForward.{u} X))
    (@ContinuousMap.continuous (∀ i, X i) (∀ i, X i)
      (compactlyGenerated.{u} (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (ContinuousMap.compactlyGeneratedPiBackward.{u} X))

variable (X : I → Type v) [tX : ∀ i, TopologicalSpace (X i)]

/-- The comparison homeomorphism uses the refinement of the family of counits. -/
theorem compactlyGeneratedPiComparison_toContinuousMap :
    (show @ContinuousMap (∀ i, X i) (∀ i, X i)
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        (compactlyGenerated.{u} (∀ i, X i)) from
      let e := compactlyGeneratedPiComparison.{u} X
      @ContinuousMap.mk (∀ i, X i) (∀ i, X i)
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        (compactlyGenerated.{u} (∀ i, X i))
        (@Homeomorph.toEquiv (∀ i, X i) (∀ i, X i)
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          (compactlyGenerated.{u} (∀ i, X i)) e)
        (@Homeomorph.continuous_toFun (∀ i, X i) (∀ i, X i)
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          (compactlyGenerated.{u} (∀ i, X i)) e)) =
      ContinuousMap.compactlyGeneratedPiForward.{u} X := rfl

/-- The inverse homeomorphism uses the generated-source lift of refined evaluations. -/
theorem compactlyGeneratedPiComparison_symm_toContinuousMap :
    (show @ContinuousMap (∀ i, X i) (∀ i, X i)
        (compactlyGenerated.{u} (∀ i, X i))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) from
      let e := @Homeomorph.symm (∀ i, X i) (∀ i, X i)
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        (compactlyGenerated.{u} (∀ i, X i)) (compactlyGeneratedPiComparison.{u} X)
      @ContinuousMap.mk (∀ i, X i) (∀ i, X i)
        (compactlyGenerated.{u} (∀ i, X i))
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        (@Homeomorph.toEquiv (∀ i, X i) (∀ i, X i)
          (compactlyGenerated.{u} (∀ i, X i))
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) e)
        (@Homeomorph.continuous_toFun (∀ i, X i) (∀ i, X i)
          (compactlyGenerated.{u} (∀ i, X i))
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) e)) =
      ContinuousMap.compactlyGeneratedPiBackward.{u} X := rfl

@[simp]
theorem compactlyGeneratedPiComparison_apply (x : ∀ i, X i) :
    @Homeomorph.toEquiv (∀ i, X i) (∀ i, X i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i)) (compactlyGeneratedPiComparison.{u} X) x = x :=
  ContinuousMap.compactlyGeneratedPiForward_apply.{u} X x

@[simp]
theorem compactlyGeneratedPiComparison_symm_apply (x : ∀ i, X i) :
    @Homeomorph.toEquiv (∀ i, X i) (∀ i, X i)
      (compactlyGenerated.{u} (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (@Homeomorph.symm (∀ i, X i) (∀ i, X i)
        (@compactlyGenerated.{u} (∀ i, X i)
          (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
        (compactlyGenerated.{u} (∀ i, X i)) (compactlyGeneratedPiComparison.{u} X)) x = x :=
  ContinuousMap.compactlyGeneratedPiBackward_apply.{u} X x

variable {X} {Y : I → Type w} [tY : ∀ i, TopologicalSpace (Y i)]

/-- The comparison homeomorphism is natural in the entire original family. -/
theorem compactlyGeneratedPiComparison_naturality (f : ∀ i, C(X i, Y i)) :
    @ContinuousMap.comp (∀ i, X i) (∀ i, Y i) (∀ i, Y i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (@compactlyGenerated.{u} (∀ i, Y i)
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
      (compactlyGenerated.{u} (∀ i, Y i))
      (show @ContinuousMap (∀ i, Y i) (∀ i, Y i)
          (@compactlyGenerated.{u} (∀ i, Y i)
            (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
          (compactlyGenerated.{u} (∀ i, Y i)) from
        let e := compactlyGeneratedPiComparison.{u} Y
        @ContinuousMap.mk (∀ i, Y i) (∀ i, Y i)
          (@compactlyGenerated.{u} (∀ i, Y i)
            (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
          (compactlyGenerated.{u} (∀ i, Y i))
          (@Homeomorph.toEquiv (∀ i, Y i) (∀ i, Y i)
            (@compactlyGenerated.{u} (∀ i, Y i)
              (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
            (compactlyGenerated.{u} (∀ i, Y i)) e)
          (@Homeomorph.continuous_toFun (∀ i, Y i) (∀ i, Y i)
            (@compactlyGenerated.{u} (∀ i, Y i)
              (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
            (compactlyGenerated.{u} (∀ i, Y i)) e))
      (@ContinuousMap.compactlyGeneratedMap.{u} (∀ i, X i) (∀ i, Y i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i)))
        (@ContinuousMap.piMap I X Y
          (fun i => compactlyGenerated.{u} (X i)) (fun i => compactlyGenerated.{u} (Y i))
          (fun i => ContinuousMap.compactlyGeneratedMap.{u} (f i)))) =
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, Y i)
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (compactlyGenerated.{u} (∀ i, X i)) (compactlyGenerated.{u} (∀ i, Y i))
      (ContinuousMap.compactlyGeneratedMap.{u} (ContinuousMap.piMap f))
      (show @ContinuousMap (∀ i, X i) (∀ i, X i)
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          (compactlyGenerated.{u} (∀ i, X i)) from
        let e := compactlyGeneratedPiComparison.{u} X
        @ContinuousMap.mk (∀ i, X i) (∀ i, X i)
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          (compactlyGenerated.{u} (∀ i, X i))
          (@Homeomorph.toEquiv (∀ i, X i) (∀ i, X i)
            (@compactlyGenerated.{u} (∀ i, X i)
              (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
            (compactlyGenerated.{u} (∀ i, X i)) e)
          (@Homeomorph.continuous_toFun (∀ i, X i) (∀ i, X i)
            (@compactlyGenerated.{u} (∀ i, X i)
              (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
            (compactlyGenerated.{u} (∀ i, X i)) e)) := by
  simpa only [compactlyGeneratedPiComparison_toContinuousMap] using
    ContinuousMap.compactlyGeneratedPiForward_naturality.{u} f

/-- The inverse comparison homeomorphism is natural in the entire original family. -/
theorem compactlyGeneratedPiComparison_symm_naturality (f : ∀ i, C(X i, Y i)) :
    @ContinuousMap.comp (∀ i, X i) (∀ i, Y i) (∀ i, Y i)
      (compactlyGenerated.{u} (∀ i, X i)) (compactlyGenerated.{u} (∀ i, Y i))
      (@compactlyGenerated.{u} (∀ i, Y i)
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
      (show @ContinuousMap (∀ i, Y i) (∀ i, Y i)
          (compactlyGenerated.{u} (∀ i, Y i))
          (@compactlyGenerated.{u} (∀ i, Y i)
            (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i)))) from
        let e := @Homeomorph.symm (∀ i, Y i) (∀ i, Y i)
          (@compactlyGenerated.{u} (∀ i, Y i)
            (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
          (compactlyGenerated.{u} (∀ i, Y i)) (compactlyGeneratedPiComparison.{u} Y)
        @ContinuousMap.mk (∀ i, Y i) (∀ i, Y i)
          (compactlyGenerated.{u} (∀ i, Y i))
          (@compactlyGenerated.{u} (∀ i, Y i)
            (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
          (@Homeomorph.toEquiv (∀ i, Y i) (∀ i, Y i)
            (compactlyGenerated.{u} (∀ i, Y i))
            (@compactlyGenerated.{u} (∀ i, Y i)
              (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i)))) e)
          (@Homeomorph.continuous_toFun (∀ i, Y i) (∀ i, Y i)
            (compactlyGenerated.{u} (∀ i, Y i))
            (@compactlyGenerated.{u} (∀ i, Y i)
              (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i)))) e))
      (ContinuousMap.compactlyGeneratedMap.{u} (ContinuousMap.piMap f)) =
    @ContinuousMap.comp (∀ i, X i) (∀ i, X i) (∀ i, Y i)
      (compactlyGenerated.{u} (∀ i, X i))
      (@compactlyGenerated.{u} (∀ i, X i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
      (@compactlyGenerated.{u} (∀ i, Y i)
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i))))
      (@ContinuousMap.compactlyGeneratedMap.{u} (∀ i, X i) (∀ i, Y i)
        (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))
        (@Pi.topologicalSpace I Y (fun i => compactlyGenerated.{u} (Y i)))
        (@ContinuousMap.piMap I X Y
          (fun i => compactlyGenerated.{u} (X i)) (fun i => compactlyGenerated.{u} (Y i))
          (fun i => ContinuousMap.compactlyGeneratedMap.{u} (f i))))
      (show @ContinuousMap (∀ i, X i) (∀ i, X i)
          (compactlyGenerated.{u} (∀ i, X i))
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) from
        let e := @Homeomorph.symm (∀ i, X i) (∀ i, X i)
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          (compactlyGenerated.{u} (∀ i, X i)) (compactlyGeneratedPiComparison.{u} X)
        @ContinuousMap.mk (∀ i, X i) (∀ i, X i)
          (compactlyGenerated.{u} (∀ i, X i))
          (@compactlyGenerated.{u} (∀ i, X i)
            (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i))))
          (@Homeomorph.toEquiv (∀ i, X i) (∀ i, X i)
            (compactlyGenerated.{u} (∀ i, X i))
            (@compactlyGenerated.{u} (∀ i, X i)
              (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) e)
          (@Homeomorph.continuous_toFun (∀ i, X i) (∀ i, X i)
            (compactlyGenerated.{u} (∀ i, X i))
            (@compactlyGenerated.{u} (∀ i, X i)
              (@Pi.topologicalSpace I X (fun i => compactlyGenerated.{u} (X i)))) e)) := by
  simpa only [compactlyGeneratedPiComparison_symm_toContinuousMap] using
    ContinuousMap.compactlyGeneratedPiBackward_naturality.{u} f

end Homeomorph
