/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.OpenCoverDescent
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Order.SupClosed

/-!
# Fundamental-groupoid colimits over open inclusions

The functor on open subspaces is the composite
`TopologicalSpace.Opens.toTopCat (TopCat.of X) ⋙
  FundamentalGroupoid.fundamentalGroupoidFunctor`.
The inclusions into `X` give its cocone `FundamentalGroupoid.opensCocone`, without any
covering or intersection-closure assumption.

For a family `U : I → Opens X`, whiskering this cocone by
`CategoryTheory.inducedFunctor U` retains every index and every inclusion between its
opens. In particular, repeated presentations of one open are not identified. If the
family covers `X` and its range is closed under binary intersections, the whiskered
cocone is a colimit in both `Grpd` and `Cat`. Strictly compatible chart functors into
an arbitrary category extend uniquely, with independent target object and morphism
universes. Compatibility and restriction are equalities of functors, not natural
isomorphisms.

May's groupoid theorem on printed p. 17 assumes path-connected open members. The
present formulation generalizes it by dropping that assumption. The based-group
formulation on printed p. 18 additionally uses a common basepoint; none is needed here.
Intersection closure means binary, or equivalently nonempty finite, intersection closure:
the family need not contain the empty intersection `X`. It need not be finite or
injectively indexed.
An empty family can cover only an empty space; its cocone vertex is then the empty
fundamental groupoid.

## Implementation notes

The descent interface uses the strict pairwise open-cover descent in
`FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.OpenCoverDescent`.
Binary intersection closure represents each pairwise intersection by a member of the
indexed family; compatibility along its two inclusions gives pairwise compatibility.
The diagram and cocone themselves use only Mathlib's open-subspace and induced-category
constructions.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §7, printed pp. 17–18:
  the groupoid colimit theorem on p. 17 and the based-group theorem on p. 18.
* `FundamentalGroupoids.AlgebraicTopology.FundamentalGroupoid.OpenCoverDescent`:
  strict descent into arbitrary target categories over pairwise intersections.
* Mathlib's fundamental groupoids, by Shing Tak Lam; open-subspace functors, by
  Kim Morrison; induced categories and colimit cocones in `CategoryTheory`.
-/

@[expose] public section

noncomputable section

universe u v w w'

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroupoid

variable (X : Type u) [TopologicalSpace X]

/-- The cocone of all open-subspace inclusions into the ambient fundamental groupoid.
It requires neither a covering hypothesis nor intersection closure. -/
def opensCocone :
    Cocone (Opens.toTopCat (TopCat.of X) ⋙ fundamentalGroupoidFunctor) where
  pt := Grpd.of (FundamentalGroupoid X)
  ι :=
    { app := fun V => map (Opens.inclusion' (X := TopCat.of X) V).hom
      naturality := by
        intro V W f
        change map (((Opens.toTopCat (TopCat.of X)).map f).hom) ⋙
            map (Opens.inclusion' (X := TopCat.of X) W).hom =
          map (Opens.inclusion' (X := TopCat.of X) V).hom
        rw [← FundamentalGroupoid.map_comp]
        rfl }

/-- The vertex of the open-inclusion cocone is the ambient fundamental groupoid. -/
@[simp]
theorem opensCocone_pt :
    (opensCocone X).pt = Grpd.of (FundamentalGroupoid X) := rfl

variable {X}

/-- The canonical composite assigns an open its fundamental groupoid. -/
theorem opensCocone_diagram_obj (V : Opens X) :
    (Opens.toTopCat (TopCat.of X) ⋙ fundamentalGroupoidFunctor).obj V =
      Grpd.of (FundamentalGroupoid V) := rfl

/-- The canonical composite sends each open inclusion to its induced functor. -/
theorem opensCocone_diagram_map {V W : Opens X} (f : V ⟶ W) :
    (Opens.toTopCat (TopCat.of X) ⋙ fundamentalGroupoidFunctor).map f =
      map (ContinuousMap.inclusion f.le) := rfl

/-- Each leg is the functor induced by the subtype inclusion into the ambient space. -/
theorem opensCocone_ι_app (V : Opens X) :
    (opensCocone X).ι.app V = map (ContinuousMap.subtypeVal (V : Set X)) := rfl

/-- A leg sends a point of an open subspace to the same ambient point. -/
@[simp]
theorem opensCocone_ι_app_obj (V : Opens X) (x : FundamentalGroupoid V) :
    ((opensCocone X).ι.app V).obj x = mk (x.as : X) := rfl

/-- A leg maps a path class by the subtype inclusion. -/
theorem opensCocone_ι_app_map (V : Opens X) {x y : FundamentalGroupoid V} (p : x ⟶ y) :
    ((opensCocone X).ι.app V).map p =
      p.map (ContinuousMap.subtypeVal (V : Set X)) := rfl

/-- Naturality along an open inclusion is strict equality of functors. -/
theorem opensCocone_naturality {V W : Opens X} (h : V ≤ W) :
    map (ContinuousMap.inclusion h) ⋙ (opensCocone X).ι.app W =
      (opensCocone X).ι.app V :=
  (opensCocone X).w (homOfLE h)

variable {ι : Type v}

/-- The inclusion-indexed composite keeps the fundamental groupoid at every index. -/
theorem opensCocone_whisker_diagram_obj (U : ι → Opens X)
    (i : InducedCategory (Opens X) U) :
    (inducedFunctor U ⋙
      (Opens.toTopCat (TopCat.of X) ⋙ fundamentalGroupoidFunctor)).obj i =
        Grpd.of (FundamentalGroupoid (U i)) := rfl

/-- Every arrow of the induced category acts by its open-subspace inclusion. -/
theorem opensCocone_whisker_diagram_map (U : ι → Opens X)
    {i j : InducedCategory (Opens X) U} (f : i ⟶ j) :
    (inducedFunctor U ⋙
      (Opens.toTopCat (TopCat.of X) ⋙ fundamentalGroupoidFunctor)).map f =
        map (ContinuousMap.inclusion f.hom.le) := rfl

/-- Whiskering the open-inclusion cocone leaves its ambient vertex unchanged. -/
theorem opensCocone_whisker_pt (U : ι → Opens X) :
    ((opensCocone X).whisker (inducedFunctor U)).pt =
      Grpd.of (FundamentalGroupoid X) := rfl

/-- The leg at a presented open is induced by its subtype inclusion. -/
theorem opensCocone_whisker_ι_app (U : ι → Opens X)
    (i : InducedCategory (Opens X) U) :
    ((opensCocone X).whisker (inducedFunctor U)).ι.app i =
      map (ContinuousMap.subtypeVal (U i : Set X)) := rfl

/-- Forgetting to categories keeps the ambient fundamental groupoid as vertex. -/
theorem opensCocone_whisker_forgetToCat_pt (U : ι → Opens X) :
    (Grpd.forgetToCat.mapCocone
      ((opensCocone X).whisker (inducedFunctor U))).pt =
        Cat.of (FundamentalGroupoid X) := rfl

/-- The category-valued legs wrap the same subtype-inclusion functors. -/
theorem opensCocone_whisker_forgetToCat_ι_app (U : ι → Opens X)
    (i : InducedCategory (Opens X) U) :
    (Grpd.forgetToCat.mapCocone
      ((opensCocone X).whisker (inducedFunctor U))).ι.app i =
        (map (ContinuousMap.subtypeVal (U i : Set X))).toCatHom := rfl

section Descent

variable {U : ι → Opens X} {C : Type w} [Category.{w'} C]

private theorem pairwise_compatibility_of_infClosed (hclosed : InfClosed (Set.range U))
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ C)
    (hF : ∀ (i j : ι) (hij : U i ≤ U j), map (ContinuousMap.inclusion hij) ⋙ F j = F i)
    (i j : ι) :
    (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j := by
  obtain ⟨k, hk⟩ := hclosed (Set.mem_range_self i) (Set.mem_range_self j)
  have hki : U k ≤ U i := hk.le.trans inf_le_left
  have hkj : U k ≤ U j := hk.le.trans inf_le_right
  let a : C(↑(U i ⊓ U j), U k) := ContinuousMap.inclusion
    (show (↑(U i ⊓ U j) : Set X) ⊆ (U k : Set X) from hk.ge)
  let b : C(U k, U i) := ContinuousMap.inclusion
    (show (U k : Set X) ⊆ (U i : Set X) from hki)
  let c : C(U k, U j) := ContinuousMap.inclusion
    (show (U k : Set X) ⊆ (U j : Set X) from hkj)
  -- Factor the two meet projections through a presented intersection, without
  -- transporting functors across the equality of open subspaces.
  have hb : b.comp a =
      ((Opens.toTopCat (TopCat.of X)).map (Opens.infLELeft (U i) (U j))).hom := by
    ext x
    rfl
  have hc : c.comp a =
      ((Opens.toTopCat (TopCat.of X)).map (Opens.infLERight (U i) (U j))).hom := by
    ext x
    rfl
  have hleft : map a ⋙ map b =
      (openCoverDiagram U).map (Pairwise.Hom.left i j) := by
    rw [openCoverDiagram_map_left]
    exact (FundamentalGroupoid.map_comp b a).symm.trans
      (congrArg (fun f : C(↑(U i ⊓ U j), U i) => map f) hb)
  have hright : map a ⋙ map c =
      (openCoverDiagram U).map (Pairwise.Hom.right i j) := by
    rw [openCoverDiagram_map_right]
    exact (FundamentalGroupoid.map_comp c a).symm.trans
      (congrArg (fun f : C(↑(U i ⊓ U j), U j) => map f) hc)
  have hbF : map b ⋙ F i = F k := hF k i hki
  have hcF : map c ⋙ F j = F k := hF k j hkj
  have hleftF : (openCoverDiagram U).map (Pairwise.Hom.left i j) ⋙ F i =
      map a ⋙ F k := by
    exact (congrArg
      (fun G : FundamentalGroupoid (U i ⊓ U j : Opens X) ⥤ FundamentalGroupoid (U i) =>
        G ⋙ F i) hleft.symm).trans
      ((Functor.assoc (map a) (map b) (F i)).trans
        (congrArg (fun G : FundamentalGroupoid (U k) ⥤ C => map a ⋙ G) hbF))
  have hrightF : (openCoverDiagram U).map (Pairwise.Hom.right i j) ⋙ F j =
      map a ⋙ F k := by
    exact (congrArg
      (fun G : FundamentalGroupoid (U i ⊓ U j : Opens X) ⥤ FundamentalGroupoid (U j) =>
        G ⋙ F j) hright.symm).trans
      ((Functor.assoc (map a) (map c) (F j)).trans
        (congrArg (fun G : FundamentalGroupoid (U k) ⥤ C => map a ⋙ G) hcF))
  exact hleftF.trans hrightF.symm

/-- Extend strictly inclusion-compatible chart functors over an intersection-closed cover.

Compatibility is required along every inclusion between presented opens, including repeated
presentations. Object and morphism universes of the target are independent of the space and
index universes. This generalizes May's groupoid theorem (Chapter 2, §7, printed p. 17)
by dropping its path-connected-member hypothesis. Binary intersection closure suffices;
the family need not contain `X`. The based theorem on p. 18 additionally uses a common
basepoint, which is not required here. -/
@[no_expose]
noncomputable def descOfIsOpenCoverOfInfClosed (hU : IsOpenCover U)
    (hclosed : InfClosed (Set.range U))
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ C)
    (hF : ∀ (i j : ι) (hij : U i ≤ U j), map (ContinuousMap.inclusion hij) ⋙ F j = F i) :
    FundamentalGroupoid X ⥤ C := by
  exact descOfIsOpenCover hU F (pairwise_compatibility_of_infClosed hclosed F hF)

/-- Descent restricts to each chart by equality of functors. -/
@[simp]
theorem inclusion_comp_descOfIsOpenCoverOfInfClosed (hU : IsOpenCover U)
    (hclosed : InfClosed (Set.range U))
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ C)
    (hF : ∀ (i j : ι) (hij : U i ≤ U j), map (ContinuousMap.inclusion hij) ⋙ F j = F i)
    (i : ι) :
    map (ContinuousMap.subtypeVal (U i : Set X)) ⋙
      descOfIsOpenCoverOfInfClosed hU hclosed F hF = F i := by
  exact inclusion_comp_descOfIsOpenCover hU F
    (pairwise_compatibility_of_infClosed hclosed F hF) i

/-- The chart restriction equations uniquely determine the descended functor. -/
theorem descOfIsOpenCoverOfInfClosed_unique (hU : IsOpenCover U)
    (hclosed : InfClosed (Set.range U))
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ C)
    (hF : ∀ (i j : ι) (hij : U i ≤ U j), map (ContinuousMap.inclusion hij) ⋙ F j = F i)
    (K : FundamentalGroupoid X ⥤ C)
    (hK : ∀ i, map (ContinuousMap.subtypeVal (U i : Set X)) ⋙ K = F i) :
    K = descOfIsOpenCoverOfInfClosed hU hclosed F hF := by
  exact descOfIsOpenCover_unique hU F
    (pairwise_compatibility_of_infClosed hclosed F hF) K hK

/-- The strict mapping property of an intersection-closed open cover into any category.

Only coverage and binary intersection closure are required of the family; it need not
contain `X`. This generalizes May's groupoid theorem (Chapter 2, §7, printed p. 17) by
dropping its path-connected-member hypothesis. The based theorem on p. 18 additionally
uses a common basepoint, which is not required here. The target's object and morphism
universes are independent. -/
theorem existsUnique_functor_of_isOpenCover_of_infClosed (hU : IsOpenCover U)
    (hclosed : InfClosed (Set.range U))
    (F : ∀ i, FundamentalGroupoid (U i) ⥤ C)
    (hF : ∀ (i j : ι) (hij : U i ≤ U j), map (ContinuousMap.inclusion hij) ⋙ F j = F i) :
    ∃! K : FundamentalGroupoid X ⥤ C,
      ∀ i, map (ContinuousMap.subtypeVal (U i : Set X)) ⋙ K = F i := by
  refine ⟨descOfIsOpenCoverOfInfClosed hU hclosed F hF,
    inclusion_comp_descOfIsOpenCoverOfInfClosed hU hclosed F hF, ?_⟩
  intro K hK
  exact descOfIsOpenCoverOfInfClosed_unique hU hclosed F hF K hK

end Descent

/-- The full-inclusion cocone of an intersection-closed open cover is a colimit in `Grpd`.

The diagram retains all indices and inclusions. This generalizes May's groupoid theorem
(Chapter 2, §7, printed p. 17) by dropping its path-connected-member hypothesis. Binary
intersection closure suffices; the family need not contain `X`. The based theorem on
p. 18 additionally uses a common basepoint, which is not required here. -/
noncomputable def isColimitOfIsOpenCover (U : ι → Opens X) (hU : IsOpenCover U)
    (hclosed : InfClosed (Set.range U)) :
    IsColimit ((opensCocone X).whisker (inducedFunctor U)) := by
  let F (s : Cocone (inducedFunctor U ⋙
      (Opens.toTopCat (TopCat.of X) ⋙ fundamentalGroupoidFunctor))) (i : ι) :
      FundamentalGroupoid (U i) ⥤ s.pt := s.ι.app i
  have hF (s : Cocone (inducedFunctor U ⋙
      (Opens.toTopCat (TopCat.of X) ⋙ fundamentalGroupoidFunctor)))
      (i j : ι) (hij : U i ≤ U j) :
      map (ContinuousMap.inclusion hij) ⋙ F s j = F s i := by
    have hh := s.w (InducedCategory.homMk (homOfLE hij))
    change map (ContinuousMap.inclusion hij) ⋙ F s j = F s i at hh
    exact hh
  refine
    { desc := fun s => descOfIsOpenCoverOfInfClosed hU hclosed (F s) (hF s)
      fac := ?_
      uniq := ?_ }
  · intro s i
    change map (ContinuousMap.subtypeVal (U i : Set X)) ⋙
      descOfIsOpenCoverOfInfClosed hU hclosed (F s) (hF s) = F s i
    exact inclusion_comp_descOfIsOpenCoverOfInfClosed hU hclosed (F s) (hF s) i
  · intro s m hm
    apply descOfIsOpenCoverOfInfClosed_unique hU hclosed (F s) (hF s) m
    intro i
    have hh := hm i
    change map (ContinuousMap.subtypeVal (U i : Set X)) ⋙ m = F s i at hh
    exact hh

/-- The same full-inclusion cocone is a colimit in `Cat`, obtained using `Grpd.forgetToCat`.

This generalizes May's groupoid theorem (Chapter 2, §7, printed p. 17) by dropping its
path-connected-member hypothesis. Binary intersection closure suffices, without requiring
`X` in the family. The based theorem on p. 18 additionally uses a common basepoint,
which is not required here. The cocone uses open inclusions, and vertices in its universal
property may be arbitrary categories at the bundled sizes. -/
noncomputable def isColimitCatOfIsOpenCover (U : ι → Opens X) (hU : IsOpenCover U)
    (hclosed : InfClosed (Set.range U)) :
    IsColimit (Grpd.forgetToCat.mapCocone
      ((opensCocone X).whisker (inducedFunctor U))) := by
  let F (s : Cocone ((inducedFunctor U ⋙
      (Opens.toTopCat (TopCat.of X) ⋙ fundamentalGroupoidFunctor)) ⋙ Grpd.forgetToCat))
      (i : ι) : FundamentalGroupoid (U i) ⥤ s.pt := (s.ι.app i).toFunctor
  have hF (s : Cocone ((inducedFunctor U ⋙
      (Opens.toTopCat (TopCat.of X) ⋙ fundamentalGroupoidFunctor)) ⋙ Grpd.forgetToCat))
      (i j : ι) (hij : U i ≤ U j) :
      map (ContinuousMap.inclusion hij) ⋙ F s j = F s i := by
    exact congrArg Cat.Hom.toFunctor (s.w (InducedCategory.homMk (homOfLE hij)))
  refine
    { desc := fun s => (descOfIsOpenCoverOfInfClosed hU hclosed (F s) (hF s)).toCatHom
      fac := ?_
      uniq := ?_ }
  · intro s i
    apply Cat.ext
    change map (ContinuousMap.subtypeVal (U i : Set X)) ⋙
      descOfIsOpenCoverOfInfClosed hU hclosed (F s) (hF s) = F s i
    exact inclusion_comp_descOfIsOpenCoverOfInfClosed hU hclosed (F s) (hF s) i
  · intro s m hm
    apply Cat.ext
    apply descOfIsOpenCoverOfInfClosed_unique hU hclosed (F s) (hF s) m.toFunctor
    intro i
    have hh := congrArg Cat.Hom.toFunctor (hm i)
    change map (ContinuousMap.subtypeVal (U i : Set X)) ⋙ m.toFunctor = F s i at hh
    exact hh

end FundamentalGroupoid
