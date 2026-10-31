/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover
public import GroupTheory.Category.Grp.Colimits

/-!
# Presentations of fundamental groups from open covers

An intersection-closed cover by path-connected open neighborhoods of a common point
presents the ambient fundamental group as a free product modulo inclusion relations.
The diagram is the existing neighborhood functor restricted along `inducedFunctor`;
it retains all inclusions and repeated presentations of the same neighborhood.

`FundamentalGroup.quotientEquivOfIsOpenCover` compares the arrow-relations quotient
with the ambient fundamental group. Both directions preserve the inclusion legs.
The canonical free-product map is surjective, and its kernel is exactly the normal
closure of the diagram's arrow relators.

The index and space universes are independent. The quotient has carrier universe
`max u v`, whereas the ambient fundamental group has carrier universe `u`. No
smallness hypothesis on the index type is imposed. The comparison uses the
independent-target group universal property of the open cover.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–7,
  printed pp. 16–19: group colimits and the based van Kampen theorem.
* `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenCover` supplies
  the independent-target universal property for intersection-closed covers.
* `GroupTheory.Category.Grp.Colimits` supplies the free-product quotient by
  arrow relations and its descent and extensionality API, using Mathlib's free
  products, normal closures and quotient groups.
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- The arrow-relations quotient of the fundamental groups of an intersection-closed
path-connected open cover is the ambient fundamental group.

The diagram retains every inclusion between the presented neighborhoods. Its quotient
may lie in a larger universe than the ambient fundamental group.

See May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–7. -/
noncomputable def quotientEquivOfIsOpenCover
    (x : X) (U : I → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) :
    GrpCat.Colimits.ColimitType
      (inducedFunctor U ⋙ openNhdsFunctor x) ≃* FundamentalGroup X x := by
  classical
  let F := inducedFunctor U ⋙ openNhdsFunctor x
  have hcompat : ∀ {i j : InducedCategory (OpenNhds (X := TopCat.of X) x) U}
      (a : i ⟶ j),
      (((openNhdsCocone x).ι.app (U j)).hom).comp (F.map a).hom =
        ((openNhdsCocone x).ι.app (U i)).hom := by
    intro i j a
    exact congrArg GrpCat.Hom.hom
      ((openNhdsCocone x).w ((inducedFunctor U).map a))
  let f : GrpCat.Colimits.ColimitType F →* FundamentalGroup X x :=
    GrpCat.Colimits.desc (H := FundamentalGroup X x) F
      (fun i => ((openNhdsCocone x).ι.app (U i)).hom) hcompat
  have hf (i : I) :
      f.comp (GrpCat.Colimits.ι F i) = ((openNhdsCocone x).ι.app (U i)).hom :=
    GrpCat.Colimits.desc_comp_ι (H := FundamentalGroup X x) F _ hcompat i
  have hι : ∀ (i j : I) (hij : U i ≤ U j),
      (GrpCat.Colimits.ι F j).comp (((openNhdsFunctor x).map (homOfLE hij)).hom) =
        GrpCat.Colimits.ι F i := by
    intro i j hij
    exact GrpCat.Colimits.ι_comp_map F (InducedCategory.homMk (homOfLE hij))
  -- The target here is the quotient in universe `max u v`, not a bundled group in `u`.
  let h := existsUnique_hom_of_isOpenCover_of_infClosed x U hcover hpc hclosed
    (GrpCat.Colimits.ColimitType F) (GrpCat.Colimits.ι F) hι
  let g : FundamentalGroup X x →* GrpCat.Colimits.ColimitType F := Classical.choose h
  have hg (i : I) :
      g.comp (((openNhdsCocone x).ι.app (U i)).hom) = GrpCat.Colimits.ι F i :=
    (Classical.choose_spec h).1 i
  have hgf : g.comp f = MonoidHom.id (GrpCat.Colimits.ColimitType F) := by
    apply GrpCat.Colimits.hom_ext F
    intro i
    apply MonoidHom.ext
    intro a
    exact (congrArg g (DFunLike.congr_fun (hf i) a)).trans
      (DFunLike.congr_fun (hg i) a)
  have hfg : f.comp g = MonoidHom.id (FundamentalGroup X x) := by
    apply GrpCat.ofHom_injective
    apply (isColimitOfIsOpenCover x U hcover hpc hclosed).hom_ext
    intro i
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact (congrArg f (DFunLike.congr_fun (hg i) a)).trans
      (DFunLike.congr_fun (hf i) a)
  exact f.toMulEquiv g hgf hfg

/-- The quotient comparison takes each quotient leg to the homomorphism induced
by the inclusion into the ambient space. -/
theorem quotientEquivOfIsOpenCover_comp_ι
    (x : X) (U : I → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) (i : I) :
    (quotientEquivOfIsOpenCover x U hcover hpc hclosed).toMonoidHom.comp
        (GrpCat.Colimits.ι (inducedFunctor U ⋙ openNhdsFunctor x) i) =
      map (ContinuousMap.subtypeVal ((U i).1 : Set X)) ⟨x, (U i).2⟩ := by
  let F := inducedFunctor U ⋙ openNhdsFunctor x
  have hcompat : ∀ {j k : InducedCategory (OpenNhds (X := TopCat.of X) x) U}
      (a : j ⟶ k),
      (((openNhdsCocone x).ι.app (U k)).hom).comp (F.map a).hom =
        ((openNhdsCocone x).ι.app (U j)).hom := by
    intro j k a
    exact congrArg GrpCat.Hom.hom
      ((openNhdsCocone x).w ((inducedFunctor U).map a))
  change (GrpCat.Colimits.desc (H := FundamentalGroup X x) F
    (fun j => ((openNhdsCocone x).ι.app (U j)).hom) hcompat).comp
      (GrpCat.Colimits.ι F i) = ((openNhdsCocone x).ι.app (U i)).hom
  exact GrpCat.Colimits.desc_comp_ι (H := FundamentalGroup X x) F _ hcompat i

/-- The inverse quotient comparison takes each homomorphism induced by inclusion
into the ambient space to the corresponding quotient leg. -/
theorem quotientEquivOfIsOpenCover_symm_comp_inclusion
    (x : X) (U : I → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) (i : I) :
    (quotientEquivOfIsOpenCover x U hcover hpc hclosed).symm.toMonoidHom.comp
        (map (ContinuousMap.subtypeVal ((U i).1 : Set X)) ⟨x, (U i).2⟩) =
      GrpCat.Colimits.ι (inducedFunctor U ⋙ openNhdsFunctor x) i := by
  apply MonoidHom.ext
  intro a
  exact (congrArg (quotientEquivOfIsOpenCover x U hcover hpc hclosed).symm
    (DFunLike.congr_fun
      (quotientEquivOfIsOpenCover_comp_ι x U hcover hpc hclosed i) a)).symm.trans
      ((quotientEquivOfIsOpenCover x U hcover hpc hclosed).symm_apply_apply _)

/-- The quotient comparison sends a generator to its loop class in the ambient space. -/
-- Rewrite the inclusion leg before simplifying its functor-object coercions.
@[simp↓]
theorem quotientEquivOfIsOpenCover_ι
    (x : X) (U : I → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) (i : I)
    (a : FundamentalGroup (U i).1 ⟨x, (U i).2⟩) :
    quotientEquivOfIsOpenCover x U hcover hpc hclosed
        (GrpCat.Colimits.ι (inducedFunctor U ⋙ openNhdsFunctor x) i a) =
      map (ContinuousMap.subtypeVal ((U i).1 : Set X)) ⟨x, (U i).2⟩ a := by
  exact DFunLike.congr_fun
    (quotientEquivOfIsOpenCover_comp_ι x U hcover hpc hclosed i) a

/-- The inverse quotient comparison sends a loop class included from a cover member
to its quotient generator. -/
-- Rewrite the inclusion before `map_apply` expands its action on loop classes.
@[simp↓]
theorem quotientEquivOfIsOpenCover_symm_inclusion
    (x : X) (U : I → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) (i : I)
    (a : FundamentalGroup (U i).1 ⟨x, (U i).2⟩) :
    (quotientEquivOfIsOpenCover x U hcover hpc hclosed).symm
        (map (ContinuousMap.subtypeVal ((U i).1 : Set X)) ⟨x, (U i).2⟩ a) =
      GrpCat.Colimits.ι (inducedFunctor U ⋙ openNhdsFunctor x) i a := by
  exact DFunLike.congr_fun
    (quotientEquivOfIsOpenCover_symm_comp_inclusion x U hcover hpc hclosed i) a

/-- The quotient comparison composed with the quotient projection is the canonical
free-product homomorphism induced by the inclusions into the ambient space. -/
theorem quotientEquivOfIsOpenCover_comp_mk'
    (x : X) (U : I → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) :
    (quotientEquivOfIsOpenCover x U hcover hpc hclosed).toMonoidHom.comp
        (QuotientGroup.mk'
          (Subgroup.normalClosure
            (GrpCat.Colimits.relators (inducedFunctor U ⋙ openNhdsFunctor x)))) =
      Monoid.CoprodI.lift (fun i : I =>
        map (ContinuousMap.subtypeVal ((U i).1 : Set X)) ⟨x, (U i).2⟩) := by
  apply Monoid.CoprodI.ext_hom
  intro i
  apply MonoidHom.ext
  intro a
  exact ((congrArg (quotientEquivOfIsOpenCover x U hcover hpc hclosed)
    (GrpCat.Colimits.ι_apply (inducedFunctor U ⋙ openNhdsFunctor x) i a).symm).trans
      (quotientEquivOfIsOpenCover_ι x U hcover hpc hclosed i a)).trans
        (Monoid.CoprodI.lift_of
          (M := fun j : I => FundamentalGroup (U j).1 ⟨x, (U j).2⟩)
          (N := FundamentalGroup X x)
          (fun j : I => map (ContinuousMap.subtypeVal ((U j).1 : Set X)) ⟨x, (U j).2⟩)
          (i := i) a).symm

/-- The fundamental groups of an intersection-closed path-connected open cover
generate the ambient fundamental group through their inclusion-induced maps.

See May, *A Concise Course in Algebraic Topology*, Chapter 2, §§6–7. -/
theorem surjective_lift_of_isOpenCover_of_infClosed
    (x : X) (U : I → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) :
    Function.Surjective
      (Monoid.CoprodI.lift
        (M := fun i : I => FundamentalGroup (U i).1 ⟨x, (U i).2⟩)
        (N := FundamentalGroup X x)
        (fun i : I => map (ContinuousMap.subtypeVal ((U i).1 : Set X)) ⟨x, (U i).2⟩)) := by
  have hsurj := (quotientEquivOfIsOpenCover x U hcover hpc hclosed).surjective.comp
    (QuotientGroup.mk'_surjective
      (Subgroup.normalClosure
        (GrpCat.Colimits.relators (inducedFunctor U ⋙ openNhdsFunctor x))))
  intro a
  obtain ⟨b, hb⟩ := hsurj a
  exact ⟨b, (DFunLike.congr_fun
    (quotientEquivOfIsOpenCover_comp_mk' x U hcover hpc hclosed) b).symm.trans hb⟩

/-- The kernel of the free-product map induced by an intersection-closed
path-connected open cover is the normal closure of the inclusion-arrow relators.

Each relator is the target image of a loop class times the inverse of its source
copy in the free product. See May, *A Concise Course in Algebraic Topology*,
Chapter 2, §§6–7. -/
theorem ker_lift_of_isOpenCover_of_infClosed
    (x : X) (U : I → OpenNhds (X := TopCat.of X) x)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hpc : ∀ i, IsPathConnected ((U i).1 : Set X))
    (hclosed : InfClosed (Set.range U)) :
    (Monoid.CoprodI.lift
      (M := fun i : I => FundamentalGroup (U i).1 ⟨x, (U i).2⟩)
      (N := FundamentalGroup X x)
      (fun i : I => map (ContinuousMap.subtypeVal ((U i).1 : Set X)) ⟨x, (U i).2⟩)).ker =
      Subgroup.normalClosure
        (GrpCat.Colimits.relators (inducedFunctor U ⋙ openNhdsFunctor x)) := by
  exact (congrArg MonoidHom.ker
    (quotientEquivOfIsOpenCover_comp_mk' x U hcover hpc hclosed)).symm.trans
      ((MonoidHom.ker_mulEquiv_comp
        (QuotientGroup.mk'
          (Subgroup.normalClosure
            (GrpCat.Colimits.relators (inducedFunctor U ⋙ openNhdsFunctor x))))
        (quotientEquivOfIsOpenCover x U hcover hpc hclosed)).trans
          (QuotientGroup.ker_mk' _))

end FundamentalGroup
