/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover
public import GroupTheory.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-!
# Fundamental groups of common-overlap open covers

An open core and a family of open neighborhoods of a common point determine a
`WidePushoutShape` diagram of fundamental groups. Its arrows are induced by the
core-to-chart inclusions, and its ambient cocone consists of the subtype
inclusions. These constructions require only that the core lie in every chart.

When the core and charts are path connected, distinct chart indices intersect
exactly in the core, and the core together with the charts covers the ambient
space, this cocone is a colimit. The raw group colimit is canonically equivalent
to the ambient fundamental group, with both directions preserving every core
and chart leg. The index and space universes are independent: the raw quotient
has carrier universe `max u v`, while the ambient fundamental group remains in
universe `u`.

The chart family may be empty; the core then covers the whole space. Distinct
indices may name the same chart, in which case that chart equals the core.
The core need not be contractible or simply connected. No local
path-connectedness or separation assumption is required.
This is a star diagram, not the induced category retaining every inclusion
between the neighborhoods.

May's based open-cover theorem is stated for the all-inclusions diagram. The
common-core formulation here is its re-presentation after adjoining the core.
The ambient space is arbitrary, generalizing the point-attached wide-pushout
setting of the comparison formalized in Sphere Topology, not May's theorem.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–7,
  printed pp. 16–19: group colimits and the based all-inclusions cover theorem.
* `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover` supplies
  the independent-target common-overlap universal property, and `OpenNhds`
  supplies the inclusion functor and cocone.
* `SphereTopology.Topology.WidePushout.FundamentalGroupColimit`, by Formal
  Frontier Agents, supplies the point-chart comparison and its
  universal-property construction, generalized here to arbitrary ambient spaces.
* `GroupTheory.Category.Grp.Colimits` supplies the existing raw group colimit
  and its descent and extensionality API, using Mathlib's free products,
  normal closures and quotient groups. Mathlib supplies `WidePushoutShape`
  and its star-diagram and cocone constructors.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u v

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- The star diagram of the core and chart fundamental groups, with arrows
induced by the core-to-chart inclusions. No cover or connectedness hypothesis
is needed to construct the diagram. -/
def commonOverlapDiagram
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x)
    (hCU : ∀ i, C ≤ U i) : WidePushoutShape I ⥤ GrpCat.{u} :=
  WidePushoutShape.wideSpan
    ((openNhdsFunctor x).obj C)
    (fun i ↦ (openNhdsFunctor x).obj (U i))
    (fun i ↦ (openNhdsFunctor x).map (homOfLE (hCU i)))

/-- The head object is the fundamental group of the core at the common point. -/
@[simp]
theorem commonOverlapDiagram_obj_none
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i) :
    (commonOverlapDiagram x C U hCU).obj none =
      GrpCat.of (FundamentalGroup C.1 ⟨x, C.2⟩) := rfl

/-- A leg object is the fundamental group of its chart at the common point. -/
@[simp]
theorem commonOverlapDiagram_obj_some
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i) (i : I) :
    (commonOverlapDiagram x C U hCU).obj (some i) =
      GrpCat.of (FundamentalGroup (U i).1 ⟨x, (U i).2⟩) := rfl

/-- A generating arrow is the homomorphism induced by the core inclusion
into the corresponding chart. -/
@[simp]
theorem commonOverlapDiagram_map_init
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i) (i : I) :
    (commonOverlapDiagram x C U hCU).map (WidePushoutShape.Hom.init i) =
      (openNhdsFunctor x).map (homOfLE (hCU i)) := rfl

/-- The subspace inclusions of the core and charts into the ambient space form
a cocone of fundamental groups, without cover or connectedness hypotheses. -/
def commonOverlapCocone
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i) :
    Cocone (commonOverlapDiagram x C U hCU) :=
  WidePushoutShape.mkCocone (F := commonOverlapDiagram x C U hCU)
    ((openNhdsCocone x).ι.app C)
    (fun i ↦ (openNhdsCocone x).ι.app (U i))
    (fun i ↦ (openNhdsCocone x).w (homOfLE (hCU i)))

/-- The cocone vertex is the fundamental group of the ambient space. -/
@[simp]
theorem commonOverlapCocone_pt
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i) :
    (commonOverlapCocone x C U hCU).pt = GrpCat.of (FundamentalGroup X x) := rfl

/-- The head leg is the homomorphism induced by the core inclusion. -/
@[simp]
theorem commonOverlapCocone_ι_app_none
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i) :
    (commonOverlapCocone x C U hCU).ι.app none =
      (openNhdsCocone x).ι.app C := rfl

/-- A chart leg is the homomorphism induced by its inclusion into the ambient space. -/
@[simp]
theorem commonOverlapCocone_ι_app_some
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i) (i : I) :
    (commonOverlapCocone x C U hCU).ι.app (some i) =
      (openNhdsCocone x).ι.app (U i) := rfl

/-- The inclusion cocone of a path-connected common-overlap open cover is a
colimit. The core remains the head when the chart family is empty.

This is the common-core re-presentation of May's based all-inclusions cover
universal property, Chapter 2, §7. -/
def commonOverlapCoconeIsColimit
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i)
    (hinter : ∀ i j, i ≠ j → U i ⊓ U j = C)
    (hcover : IsOpenCover (fun o : Option I => (o.elim C U).1))
    (hpcC : IsPathConnected (C.1 : Set X))
    (hpcU : ∀ i, IsPathConnected ((U i).1 : Set X)) :
    IsColimit (commonOverlapCocone x C U hCU) := by
  classical
  have hup : ∀ s : Cocone (commonOverlapDiagram x C U hCU),
      ∃! ψ : FundamentalGroup X x →* (s.pt : Type u),
        ψ.comp (((openNhdsCocone x).ι.app C).hom) = (s.ι.app none).hom ∧
          ∀ i, ψ.comp (((openNhdsCocone x).ι.app (U i)).hom) =
            (s.ι.app (some i)).hom := by
    intro s
    apply existsUnique_hom_of_isOpenCover_of_commonOverlap x C U hCU hinter
      hcover hpcC hpcU (s.pt : Type u)
      (s.ι.app none).hom (fun i => (s.ι.app (some i)).hom)
    intro i
    have hw := congrArg GrpCat.Hom.hom (s.w (WidePushoutShape.Hom.init i))
    exact hw
  refine
    { desc := fun s => GrpCat.ofHom (Classical.choose (hup s))
      fac := ?_
      uniq := ?_ }
  · intro s o
    apply GrpCat.hom_ext
    cases o with
    | none =>
        exact (Classical.choose_spec (hup s)).1.1
    | some i =>
        exact (Classical.choose_spec (hup s)).1.2 i
  · intro s m hm
    apply GrpCat.hom_ext
    apply (Classical.choose_spec (hup s)).2 m.hom
    constructor
    · have hfac := congrArg GrpCat.Hom.hom (hm none)
      exact hfac
    · intro i
      have hfac := congrArg GrpCat.Hom.hom (hm (some i))
      exact hfac

/-- The raw group colimit of the common-core star is canonically equivalent to
the ambient fundamental group. Both directions preserve every inclusion leg.
The quotient and ambient group may lie in different universes.

This combines the raw group-colimit universal property with the common-core
re-presentation of May's based cover theorem, Chapter 2, §§6–7. -/
def commonOverlapColimitEquiv
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i)
    (hinter : ∀ i j, i ≠ j → U i ⊓ U j = C)
    (hcover : IsOpenCover (fun o : Option I => (o.elim C U).1))
    (hpcC : IsPathConnected (C.1 : Set X))
    (hpcU : ∀ i, IsPathConnected ((U i).1 : Set X)) :
    GrpCat.Colimits.ColimitType (commonOverlapDiagram x C U hCU) ≃*
      FundamentalGroup X x := by
  classical
  let F := commonOverlapDiagram x C U hCU
  let γ := commonOverlapCocone x C U hCU
  have hcompat : ∀ {j k : WidePushoutShape I} (b : j ⟶ k),
      (γ.ι.app k).hom.comp (F.map b).hom = (γ.ι.app j).hom := by
    intro j k b
    exact congrArg GrpCat.Hom.hom (γ.w b)
  let φ : GrpCat.Colimits.ColimitType F →* FundamentalGroup X x :=
    GrpCat.Colimits.desc (H := FundamentalGroup X x) F
      (fun o ↦ (γ.ι.app o).hom) hcompat
  have hφ (o : WidePushoutShape I) :
      φ.comp (GrpCat.Colimits.ι F o) = (γ.ι.app o).hom :=
    GrpCat.Colimits.desc_comp_ι (H := FundamentalGroup X x) F _ hcompat o
  have hι (i : I) :
      (GrpCat.Colimits.ι F (some i)).comp
        (((openNhdsFunctor x).map (homOfLE (hCU i))).hom) =
        GrpCat.Colimits.ι F none :=
    GrpCat.Colimits.ι_comp_map F (WidePushoutShape.Hom.init i)
  -- The raw quotient may be larger than a group bundled in `GrpCat.{u}`.
  let hup := existsUnique_hom_of_isOpenCover_of_commonOverlap
    x C U hCU hinter hcover hpcC hpcU (GrpCat.Colimits.ColimitType F)
    (GrpCat.Colimits.ι F none) (fun i ↦ GrpCat.Colimits.ι F (some i)) hι
  let ψ : FundamentalGroup X x →* GrpCat.Colimits.ColimitType F :=
    Classical.choose hup
  have hψ (o : WidePushoutShape I) :
      ψ.comp (γ.ι.app o).hom = GrpCat.Colimits.ι F o := by
    cases o with
    | none => exact (Classical.choose_spec hup).1.1
    | some i => exact (Classical.choose_spec hup).1.2 i
  have hψφ : ψ.comp φ = MonoidHom.id (GrpCat.Colimits.ColimitType F) := by
    apply GrpCat.Colimits.hom_ext F
    intro o
    apply MonoidHom.ext
    intro a
    exact (congrArg ψ (DFunLike.congr_fun (hφ o) a)).trans
      (DFunLike.congr_fun (hψ o) a)
  have hφψ : φ.comp ψ = MonoidHom.id (FundamentalGroup X x) := by
    apply hom_ext_of_isOpenCover_of_commonOverlap x C U hCU hinter hcover hpcC hpcU
    · apply MonoidHom.ext
      intro a
      exact (congrArg φ (DFunLike.congr_fun (hψ none) a)).trans
        (DFunLike.congr_fun (hφ none) a)
    · intro i
      apply MonoidHom.ext
      intro a
      exact (congrArg φ (DFunLike.congr_fun (hψ (some i)) a)).trans
        (DFunLike.congr_fun (hφ (some i)) a)
  exact φ.toMulEquiv ψ hψφ hφψ

/-- The canonical comparison takes each raw generator map to the corresponding
subspace inclusion, including the core leg at `none`. -/
@[simp]
theorem commonOverlapColimitEquiv_comp_ι
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i)
    (hinter : ∀ i j, i ≠ j → U i ⊓ U j = C)
    (hcover : IsOpenCover (fun o : Option I => (o.elim C U).1))
    (hpcC : IsPathConnected (C.1 : Set X))
    (hpcU : ∀ i, IsPathConnected ((U i).1 : Set X)) (o : WidePushoutShape I) :
    (↑(commonOverlapColimitEquiv x C U hCU hinter hcover hpcC hpcU) :
      GrpCat.Colimits.ColimitType (commonOverlapDiagram x C U hCU) →*
        FundamentalGroup X x).comp
      (GrpCat.Colimits.ι (commonOverlapDiagram x C U hCU) o) =
        ((commonOverlapCocone x C U hCU).ι.app o).hom := by
  let F := commonOverlapDiagram x C U hCU
  let γ := commonOverlapCocone x C U hCU
  have hcompat : ∀ {j k : WidePushoutShape I} (b : j ⟶ k),
      (γ.ι.app k).hom.comp (F.map b).hom = (γ.ι.app j).hom := by
    intro j k b
    exact congrArg GrpCat.Hom.hom (γ.w b)
  change (GrpCat.Colimits.desc (H := FundamentalGroup X x) F
    (fun j ↦ (γ.ι.app j).hom) hcompat).comp
      (GrpCat.Colimits.ι F o) = (γ.ι.app o).hom
  exact GrpCat.Colimits.desc_comp_ι (H := FundamentalGroup X x) F _ hcompat o

/-- The inverse canonical comparison takes each core or chart inclusion
to the corresponding raw-colimit generator map. -/
@[simp]
theorem commonOverlapColimitEquiv_symm_comp_ι
    (x : X) (C : OpenNhds (X := TopCat.of X) x)
    (U : I → OpenNhds (X := TopCat.of X) x) (hCU : ∀ i, C ≤ U i)
    (hinter : ∀ i j, i ≠ j → U i ⊓ U j = C)
    (hcover : IsOpenCover (fun o : Option I => (o.elim C U).1))
    (hpcC : IsPathConnected (C.1 : Set X))
    (hpcU : ∀ i, IsPathConnected ((U i).1 : Set X)) (o : WidePushoutShape I) :
    (↑((commonOverlapColimitEquiv x C U hCU hinter hcover hpcC hpcU).symm) :
      FundamentalGroup X x →*
        GrpCat.Colimits.ColimitType (commonOverlapDiagram x C U hCU)).comp
      ((commonOverlapCocone x C U hCU).ι.app o).hom =
        GrpCat.Colimits.ι (commonOverlapDiagram x C U hCU) o := by
  let e : GrpCat.Colimits.ColimitType (commonOverlapDiagram x C U hCU) ≃*
      FundamentalGroup X x :=
    commonOverlapColimitEquiv x C U hCU hinter hcover hpcC hpcU
  apply MonoidHom.ext
  intro a
  exact (congrArg e.symm
    (DFunLike.congr_fun
      (commonOverlapColimitEquiv_comp_ι x C U hCU hinter hcover hpcC hpcU o) a)).symm.trans
    (e.symm_apply_apply (GrpCat.Colimits.ι (commonOverlapDiagram x C U hCU) o a))

end FundamentalGroup
