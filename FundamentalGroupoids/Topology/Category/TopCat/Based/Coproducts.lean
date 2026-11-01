/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based
public import FundamentalGroupoids.Topology.Homotopy.WidePushout
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Coproducts of based spaces up to based homotopy

The point-wide-pushout of a family of based spaces is a coproduct both in
`BasedTopCat` and in `BasedTopCat.HomotopyCategory`. Its underlying space is
Mathlib's chosen topological wide pushout of the structure maps from the
one-point space. The structure map and inclusions are its head and factor maps.

`basedWedgeDesc` and `basedWedgeHomotopyDesc` provide descent in the two
categories, with inclusion equations and extensionality. The colimit structure
`basedWedgeHomotopyCoconeIsColimit` concerns the image of the based cofan under
`homotopyQuotient`, retaining the composite discrete diagram. The binary
specialization uses `pairComp` to compare this diagram with the binary diagram.

The key homotopy criterion is `basedWedge_homotopicRel_iff`: based maps are
homotopic relative to the common point if and only if their restrictions are
homotopic relative to each factor's point. Basedness supplies agreement at the
head even for the empty family; no factor need be chosen. The construction uses
`TopCat.widePushoutPointHomotopyRel`, after identifying each one-point structure
map with the constant map at its value.

The index type is arbitrary, including empty. The ambient universe `max u w`
allows the stock topological colimit for an index in `Type w`. No separation,
local compactness of the spaces, or condition on the basepoints is required.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, for the point-wedge setting.
* Mathlib's under categories, topological wide pushouts and discrete colimits
  supply the categorical constructions and universal properties.
* David Wärn's category quotient supplies representatives and equality of
  quotient maps; Shing Tak Lam's relative homotopies supply based homotopy.
* The wide-pushout descent and relative-homotopy formalization of
  Formal Frontier Agents supplies the topological gluing construction.
-/

@[expose] public section

noncomputable section

universe u w z

open CategoryTheory CategoryTheory.Limits

namespace BasedTopCat

variable {J : Type w} (D : J → BasedTopCat.{max u w})

/-- The point-wide-pushout of a family of based spaces, based at its head. -/
def basedWedge : BasedTopCat.{max u w} :=
  Under.mk (WidePushout.head (fun j ↦ (D j).hom))

/-- The underlying space is the chosen topological point-wide-pushout. -/
theorem basedWedge_right :
    (basedWedge D).right =
      widePushout (TopCat.of PUnit.{max u w + 1}) (fun j ↦ (D j).right)
        (fun j ↦ (D j).hom) := rfl

/-- The structure map of the based wedge is the wide-pushout head. -/
theorem basedWedge_hom :
    (basedWedge D).hom = WidePushout.head (fun j ↦ (D j).hom) := rfl

/-- The selected point is the value of the head at `PUnit.unit`. -/
theorem basedWedge_point :
    point (basedWedge D) = WidePushout.head (fun j ↦ (D j).hom) PUnit.unit := rfl

/-- The based factor inclusion, using the wide-pushout compatibility equation. -/
def basedWedgeι (j : J) : D j ⟶ basedWedge D :=
  Under.homMk (WidePushout.ι (fun k ↦ (D k).hom) j)
    (WidePushout.arrow_ι (fun k ↦ (D k).hom) j)

/-- The underlying topological morphism is the factor inclusion. -/
theorem basedWedgeι_right (j : J) :
    (basedWedgeι D j).right = WidePushout.ι (fun k ↦ (D k).hom) j := rfl

/-- The underlying continuous map is the continuous map of the factor inclusion. -/
theorem basedWedgeι_right_hom (j : J) :
    (basedWedgeι D j).right.hom = (WidePushout.ι (fun k ↦ (D k).hom) j).hom := rfl

/-- Each factor inclusion preserves the selected point. -/
theorem basedWedgeι_point (j : J) :
    (basedWedgeι D j).right.hom (point (D j)) = point (basedWedge D) :=
  map_point (basedWedgeι D j)

/-- Restriction along a based inclusion has the expected underlying continuous map. -/
theorem basedWedgeι_comp_right_hom {Y : BasedTopCat.{max u w}}
    (f : basedWedge D ⟶ Y) (j : J) :
    (basedWedgeι D j ≫ f).right.hom =
      f.right.hom.comp (WidePushout.ι (fun k ↦ (D k).hom) j).hom := rfl

/-- Two based maps agree at the common head, including for an empty family. -/
theorem basedWedge_head_eq {Y : BasedTopCat.{max u w}} (f g : basedWedge D ⟶ Y) :
    f.right.hom (WidePushout.head (fun j ↦ (D j).hom) PUnit.unit) =
      g.right.hom (WidePushout.head (fun j ↦ (D j).hom) PUnit.unit) :=
  (map_point f).trans (map_point g).symm

/-- Descend a family of based maps through the point-wide-pushout. -/
def basedWedgeDesc {Y : BasedTopCat.{max u w}} (f : ∀ j, D j ⟶ Y) :
    basedWedge D ⟶ Y :=
  Under.homMk (WidePushout.desc Y.hom (fun j ↦ (f j).right) (fun j ↦ Under.w (f j)))
    (WidePushout.head_desc (fun j ↦ (D j).hom) Y.hom
      (fun j ↦ (f j).right) (fun j ↦ Under.w (f j)))

/-- The topological map underlying based descent is wide-pushout descent. -/
theorem basedWedgeDesc_right {Y : BasedTopCat.{max u w}} (f : ∀ j, D j ⟶ Y) :
    (basedWedgeDesc D f).right =
      WidePushout.desc Y.hom (fun j ↦ (f j).right) (fun j ↦ Under.w (f j)) := rfl

/-- Descent preserves the common point. -/
theorem basedWedgeDesc_point {Y : BasedTopCat.{max u w}} (f : ∀ j, D j ⟶ Y) :
    (basedWedgeDesc D f).right.hom (point (basedWedge D)) = point Y :=
  map_point (basedWedgeDesc D f)

/-- Descent restricts to the given based map on each factor. -/
@[reassoc (attr := simp)]
theorem basedWedgeι_desc {Y : BasedTopCat.{max u w}} (f : ∀ j, D j ⟶ Y) (j : J) :
    basedWedgeι D j ≫ basedWedgeDesc D f = f j := by
  apply Under.UnderMorphism.ext
  exact WidePushout.ι_desc (fun j ↦ (D j).hom) Y.hom
    (fun j ↦ (f j).right) (fun j ↦ Under.w (f j)) j

/-- Based maps from the wedge are determined by all factor restrictions.
Agreement on the head follows from basedness, also for the empty family. -/
theorem basedWedge_hom_ext {Y : BasedTopCat.{max u w}} (f g : basedWedge D ⟶ Y)
    (h : ∀ j, basedWedgeι D j ≫ f = basedWedgeι D j ≫ g) : f = g := by
  apply Under.UnderMorphism.ext
  apply WidePushout.hom_ext (fun j ↦ (D j).hom) f.right g.right
  · intro j
    exact congrArg (fun k : D j ⟶ Y ↦ k.right) (h j)
  · exact (Under.w f).trans (Under.w g).symm

/-- The factor equations uniquely characterize based descent. -/
theorem basedWedgeDesc_unique {Y : BasedTopCat.{max u w}} (f : ∀ j, D j ⟶ Y)
    (g : basedWedge D ⟶ Y) (h : ∀ j, basedWedgeι D j ≫ g = f j) :
    g = basedWedgeDesc D f := by
  apply basedWedge_hom_ext D
  intro j
  exact (h j).trans (basedWedgeι_desc D f j).symm

/-- The family cofan formed by the based inclusions. -/
def basedWedgeCofan : Cofan D :=
  Cofan.mk (basedWedge D) (basedWedgeι D)

/-- The cofan vertex is the based point-wide-pushout. -/
theorem basedWedgeCofan_pt : (basedWedgeCofan D).pt = basedWedge D := rfl

/-- The cofan legs are the based factor inclusions. -/
theorem basedWedgeCofan_inj (j : J) :
    (basedWedgeCofan D).inj j = basedWedgeι D j := rfl

/-- The point-wide-pushout cofan is a coproduct in based spaces. -/
def basedWedgeCofanIsColimit : IsColimit (basedWedgeCofan D) :=
  Cofan.IsColimit.mk _ (fun s ↦ basedWedgeDesc D s.inj)
    (fun s j ↦ basedWedgeι_desc D s.inj j)
    (fun s m hm ↦ basedWedgeDesc_unique D s.inj m hm)

/-- The colimit descent of the based cofan is the named based descent. -/
theorem basedWedgeCofanIsColimit_desc (s : Cofan D) :
    (basedWedgeCofanIsColimit D).desc s = basedWedgeDesc D s.inj := rfl

-- Equality of the whole attaching family transports the wide pushout, head,
-- inclusions, endpoint maps and relative singleton simultaneously.
private theorem homotopicRel_of_point_factors
    {X : J → TopCat.{max u w}} (x : ∀ j, X j)
    (a : ∀ j, TopCat.of PUnit.{max u w + 1} ⟶ X j)
    (ha : a = fun j ↦ TopCat.const (x j))
    {Z : Type z} [TopologicalSpace Z]
    {f g : C((widePushout (TopCat.of PUnit.{max u w + 1}) X a : TopCat.{max u w}), Z)}
    (headEq : f (WidePushout.head a PUnit.unit) = g (WidePushout.head a PUnit.unit))
    (H : ∀ j, ContinuousMap.HomotopicRel
      (f.comp (WidePushout.ι a j).hom) (g.comp (WidePushout.ι a j).hom) {x j}) :
    ContinuousMap.HomotopicRel f g {WidePushout.head a PUnit.unit} := by
  classical
  cases ha
  exact ⟨TopCat.widePushoutPointHomotopyRel x headEq (fun j ↦ (H j).some)⟩

/-- Based maps from the point-wide-pushout are singleton-relative homotopic exactly
when all restrictions along its based inclusions are singleton-relative homotopic.
This statement includes the empty family, with no additional head-equality hypothesis. -/
theorem basedWedge_homotopicRel_iff {Y : BasedTopCat.{max u w}}
    (f g : basedWedge D ⟶ Y) :
    ContinuousMap.HomotopicRel f.right.hom g.right.hom {point (basedWedge D)} ↔
      ∀ j : J, ContinuousMap.HomotopicRel
        (basedWedgeι D j ≫ f).right.hom (basedWedgeι D j ≫ g).right.hom {point (D j)} := by
  constructor
  · intro H j
    exact ContinuousMap.HomotopicRel.precomp_continuousMap H (basedWedgeι D j).right.hom
      (by
        intro x hx
        have hx' : x = point (D j) := Set.mem_singleton_iff.mp hx
        subst x
        exact Set.mem_singleton_iff.mpr (basedWedgeι_point D j))
  · intro H
    exact homotopicRel_of_point_factors (fun j ↦ point (D j)) (fun j ↦ (D j).hom)
      (funext fun j ↦ hom_eq_const_point (D j)) (basedWedge_head_eq D f g) H

/-- The image of the based wedge cofan in the based-homotopy category. -/
def basedWedgeHomotopyCocone :
    Cocone (Discrete.functor D ⋙ homotopyQuotient) :=
  homotopyQuotient.mapCocone (basedWedgeCofan D)

/-- The mapped cocone vertex is the quotient image of the based point-wide-pushout. -/
theorem basedWedgeHomotopyCocone_pt :
    (basedWedgeHomotopyCocone D).pt = homotopyQuotient.obj (basedWedge D) := rfl

/-- The mapped cocone leg is the quotient image of the based inclusion. -/
theorem basedWedgeHomotopyCocone_ι_app (j : J) :
    (basedWedgeHomotopyCocone D).ι.app (Discrete.mk j) =
      homotopyQuotient.map (basedWedgeι D j) := rfl

/-- Descend a family of based-homotopy classes by choosing based representatives. -/
def basedWedgeHomotopyDesc (Y : HomotopyCategory.{max u w})
    (f : ∀ j, homotopyQuotient.obj (D j) ⟶ Y) :
    homotopyQuotient.obj (basedWedge D) ⟶ Y :=
  homotopyQuotient.map (basedWedgeDesc D
    (fun j ↦ homotopyQuotient.preimage (Y := Y.as) (f j)))

/-- Descent of based-homotopy classes restricts to each prescribed class. -/
@[reassoc (attr := simp)]
theorem basedWedgeHomotopyι_desc (Y : HomotopyCategory.{max u w})
    (f : ∀ j, homotopyQuotient.obj (D j) ⟶ Y) (j : J) :
    homotopyQuotient.map (basedWedgeι D j) ≫ basedWedgeHomotopyDesc D Y f = f j := by
  rw [basedWedgeHomotopyDesc, ← homotopyQuotient.map_comp, basedWedgeι_desc,
    homotopyQuotient.map_preimage]

/-- Based-homotopy classes of maps from the wedge are determined by their
restrictions. The factorwise relative homotopies glue at the common point. -/
theorem basedWedgeHomotopy_hom_ext {Y : HomotopyCategory.{max u w}}
    (f g : homotopyQuotient.obj (basedWedge D) ⟶ Y)
    (h : ∀ j, homotopyQuotient.map (basedWedgeι D j) ≫ f =
      homotopyQuotient.map (basedWedgeι D j) ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := homotopyQuotient.map_surjective
    (X := basedWedge D) (Y := Y.as) f
  obtain ⟨g, rfl⟩ := homotopyQuotient.map_surjective
    (X := basedWedge D) (Y := Y.as) g
  apply (homotopyQuotient_map_eq_iff f g).2
  apply (basedWedge_homotopicRel_iff D f g).2
  intro j
  apply (homotopyQuotient_map_eq_iff _ _).1
  simpa only [homotopyQuotient.map_comp] using h j

/-- The factor equations uniquely characterize descent of based-homotopy classes. -/
theorem basedWedgeHomotopyDesc_unique (Y : HomotopyCategory.{max u w})
    (f : ∀ j, homotopyQuotient.obj (D j) ⟶ Y)
    (g : homotopyQuotient.obj (basedWedge D) ⟶ Y)
    (h : ∀ j, homotopyQuotient.map (basedWedgeι D j) ≫ g = f j) :
    g = basedWedgeHomotopyDesc D Y f := by
  apply basedWedgeHomotopy_hom_ext D
  intro j
  exact (h j).trans (basedWedgeHomotopyι_desc D Y f j).symm

/-- Passing a descended based map to its class agrees with descending its classes.
Thus the result is independent of the representatives used in quotient descent. -/
theorem basedWedgeHomotopyDesc_map {Y : BasedTopCat.{max u w}} (f : ∀ j, D j ⟶ Y) :
    basedWedgeHomotopyDesc D (homotopyQuotient.obj Y)
      (fun j ↦ homotopyQuotient.map (f j)) = homotopyQuotient.map (basedWedgeDesc D f) := by
  apply basedWedgeHomotopy_hom_ext D
  intro j
  rw [basedWedgeHomotopyι_desc, ← homotopyQuotient.map_comp, basedWedgeι_desc]

/-- The image of the point-wide-pushout cofan is a coproduct cocone in the
based-homotopy category. -/
def basedWedgeHomotopyCoconeIsColimit : IsColimit (basedWedgeHomotopyCocone D) where
  desc s := basedWedgeHomotopyDesc D s.pt (fun j ↦ s.ι.app (Discrete.mk j))
  fac s j := by
    obtain ⟨j⟩ := j
    exact basedWedgeHomotopyι_desc D s.pt (fun j ↦ s.ι.app (Discrete.mk j)) j
  uniq s m hm :=
    basedWedgeHomotopyDesc_unique D s.pt (fun j ↦ s.ι.app (Discrete.mk j)) m
      (fun j ↦ hm (Discrete.mk j))

/-- The descent map of the mapped cocone is the named descent of its components. -/
theorem basedWedgeHomotopyCoconeIsColimit_desc
    (s : Cocone (Discrete.functor D ⋙ homotopyQuotient)) :
    (basedWedgeHomotopyCoconeIsColimit D).desc s =
      basedWedgeHomotopyDesc D s.pt (fun j ↦ s.ι.app (Discrete.mk j)) := rfl

/-- The image of the point-wide-pushout cofan is a coproduct cocone in
`BasedTopCat.HomotopyCategory`. -/
theorem basedWedgeHomotopyCocone_nonempty_isColimit :
    Nonempty (IsColimit (basedWedgeHomotopyCocone D)) :=
  ⟨basedWedgeHomotopyCoconeIsColimit D⟩

/-- The wedge of an empty family is initial in based spaces. -/
def basedWedgeIsInitial [IsEmpty J] : IsInitial (basedWedge D) :=
  IsInitial.ofUniqueHom (fun _ ↦ basedWedgeDesc D (fun j ↦ isEmptyElim j))
    (fun _ f ↦ basedWedgeDesc_unique D _ f (fun j ↦ isEmptyElim j))

/-- The unique based map from an empty wedge is descent of the empty family. -/
theorem basedWedgeIsInitial_to [IsEmpty J] (Y : BasedTopCat.{max u w}) :
    (basedWedgeIsInitial D).to Y = basedWedgeDesc D (fun j ↦ isEmptyElim j) := rfl

/-- The empty point-wide-pushout is also initial up to based homotopy. -/
def basedWedgeHomotopyIsInitial [IsEmpty J] :
    IsInitial (homotopyQuotient.obj (basedWedge D)) :=
  IsInitial.ofUniqueHom (fun Y ↦ basedWedgeHomotopyDesc D Y (fun j ↦ isEmptyElim j))
    (fun Y f ↦ basedWedgeHomotopyDesc_unique D Y _ f (fun j ↦ isEmptyElim j))

/-- The unique class from an empty wedge is descent of the empty family. -/
theorem basedWedgeHomotopyIsInitial_to [IsEmpty J] (Y : HomotopyCategory.{max u w}) :
    (basedWedgeHomotopyIsInitial D).to Y =
      basedWedgeHomotopyDesc D Y (fun j ↦ isEmptyElim j) := rfl

section Binary

variable (X Y : BasedTopCat.{u})

/-- The binary point-wide-pushout cocone, using the comparison between the mapped
pair diagram and the pair of quotient objects. Its vertex and inclusions are
unchanged by this comparison. -/
def basedWedgePairHomotopyCofan :
    BinaryCofan (homotopyQuotient.obj X) (homotopyQuotient.obj Y) :=
  (Cocone.precompose (pairComp X Y homotopyQuotient).inv).obj
    (basedWedgeHomotopyCocone (pairFunction X Y))

/-- The vertex of the binary cocone is the class of the two-factor wedge. -/
theorem basedWedgePairHomotopyCofan_pt :
    (basedWedgePairHomotopyCofan X Y).pt =
      homotopyQuotient.obj (basedWedge (pairFunction X Y)) := rfl

/-- The left binary inclusion is the class of the left based wedge inclusion. -/
theorem basedWedgePairHomotopyCofan_inl :
    (basedWedgePairHomotopyCofan X Y).inl =
      homotopyQuotient.map (basedWedgeι (pairFunction X Y) WalkingPair.left) :=
  Category.id_comp _

/-- The right binary inclusion is the class of the right based wedge inclusion. -/
theorem basedWedgePairHomotopyCofan_inr :
    (basedWedgePairHomotopyCofan X Y).inr =
      homotopyQuotient.map (basedWedgeι (pairFunction X Y) WalkingPair.right) :=
  Category.id_comp _

/-- The two-factor point-wide-pushout is a binary coproduct up to based homotopy. -/
def basedWedgePairHomotopyCofanIsColimit : IsColimit (basedWedgePairHomotopyCofan X Y) :=
  (IsColimit.precomposeInvEquiv (pairComp X Y homotopyQuotient)
    (basedWedgeHomotopyCocone (pairFunction X Y))).symm
      (basedWedgeHomotopyCoconeIsColimit (pairFunction X Y))

end Binary

end BasedTopCat
