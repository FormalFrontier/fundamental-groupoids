/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Functor
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Product
public import FundamentalGroupoids.Topology.Category.TopCat.Based.Products
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# Product preservation by the fundamental-group functor

The canonical categorical product comparison for `FundamentalGroup.functor` acts
by coordinate evaluation on loop classes. After identifying the based product
with the dependent product, its forward homomorphism is exactly
`FundamentalGroup.piMulEquiv.toMonoidHom`.

`FundamentalGroup.functor_preservesLimitsOfShape_discrete` says that every existing
product cone is preserved, with independent index and space universes and including
the empty product. It does not assert the existence of all large products in a
fixed category. For a family-specific comparison, the chosen source and target
products are explicit assumptions. Target-product existence can instead be derived
from preservation, transporting along `Discrete.compNatIsoDiscrete`.

The comparison itself is Mathlib's `CategoryTheory.Limits.piComparison`; its
isomorphism, inverse projection law and diagram naturality are supplied by
`PreservesProduct.iso`, `inv_piComparison_comp_map_π` and `preservesLimitNatIso`.
For coordinate based maps and separately chosen products, `map_lift_piComparison`
together with the projection equations gives naturality without blanket product existence.
The raw product agreement below uses `MonoidHom.pi` of the chosen group-product
projections. Its underlying function is the canonical identification obtained from
the forgetful product comparison and `CategoryTheory.Limits.Types.productIso`.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §8, for the
  product calculation of fundamental groups. Product preservation is its categorical
  formulation, with product existence kept separate from preservation.
* Mathlib's fundamental-group construction by Mark Lavrentyev and product-groupoid
  construction by Praneeth Kolichala underlie `FundamentalGroup.piMulEquiv`.
* Mathlib's product comparisons and preservation API, by Kim Morrison and Bhavik Mehta,
  supply the categorical comparison and its isomorphism.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace FundamentalGroup

section Comparison

variable {I : Type v} (X : I → BasedTopCat.{u})
variable [HasProduct X] [HasProduct (fun i => functor.obj (X i))]

/-- Evaluating the canonical comparison at a chosen product projection gives the
homomorphism induced by that based projection. -/
theorem functor_piComparison_π_apply
    (q : functor.obj (∏ᶜ X)) (i : I) :
    Pi.π (fun j => functor.obj (X j)) i (piComparison functor X q) =
      mapOfEq (Pi.π X i).right.hom (BasedTopCat.map_point (Pi.π X i)) q := by
  exact ConcreteCategory.congr_hom (piComparison_comp_π functor X i) q

/-- On a loop representative, the canonical comparison gives its projected loop,
with both endpoints cast by the projection's basepoint equality. -/
theorem functor_piComparison_π_fromPath
    (γ : Path (BasedTopCat.point (∏ᶜ X)) (BasedTopCat.point (∏ᶜ X))) (i : I) :
    Pi.π (fun j => functor.obj (X j)) i
        (piComparison functor X (fromPath (Path.Homotopic.Quotient.mk γ))) =
      fromPath (Path.Homotopic.Quotient.mk
        ((γ.map (Pi.π X i).right.hom.continuous).cast
          (BasedTopCat.map_point (Pi.π X i)).symm
          (BasedTopCat.map_point (Pi.π X i)).symm)) := by
  exact (functor_piComparison_π_apply X
    (fromPath (Path.Homotopic.Quotient.mk γ)) i).trans
    (mapOfEq_apply (Pi.π X i).right.hom (BasedTopCat.map_point (Pi.π X i))
      (fromPath (Path.Homotopic.Quotient.mk γ)))

end Comparison

/-- After the canonical based-product identification and the coordinate
identification of the group product, the comparison homomorphism is the forward
homomorphism of `piMulEquiv`. This identity does not assume product preservation. -/
theorem functor_piComparison_eq_piMulEquiv {I : Type v}
    (X : I → BasedTopCat.{max u v}) :
    (MonoidHom.pi (fun i => (Pi.π (fun j => functor.obj (X j)) i).hom)).comp
        ((piComparison functor X).hom.comp
          (functor.map (BasedTopCat.piIsoPi X).inv).hom) =
      (piMulEquiv (fun i => BasedTopCat.point (X i))).toMonoidHom := by
  apply MonoidHom.ext
  intro q
  funext i
  let π : BasedTopCat.of (∀ j, (X j).right) (fun j => BasedTopCat.point (X j)) ⟶ X i :=
    Under.homMk (TopCat.piπ (fun j => (X j).right) i) (by
      apply TopCat.ext
      intro t
      cases t
      rfl)
  have hπ : (BasedTopCat.piIsoPi X).inv ≫ Pi.π X i = π :=
    Under.UnderMorphism.ext (BasedTopCat.piIsoPi_inv_π X i)
  have hmap : (functor.map π).hom =
      map (ContinuousMap.eval i) (fun j => BasedTopCat.point (X j)) :=
    (functor_map_hom π).trans
      (mapOfEq_rfl (ContinuousMap.eval i) (fun j => BasedTopCat.point (X j)))
  exact (functor_piComparison_π_apply X
    (functor.map (BasedTopCat.piIsoPi X).inv q) i).trans
    ((ConcreteCategory.congr_hom
      (functor.map_comp (BasedTopCat.piIsoPi X).inv (Pi.π X i)) q).symm.trans
      ((congrArg
        (fun f : BasedTopCat.of (∀ j, (X j).right)
            (fun j => BasedTopCat.point (X j)) ⟶ X i => functor.map f q) hπ).trans
        ((DFunLike.congr_fun hmap q).trans
          (piMulEquiv_apply (fun j => BasedTopCat.point (X j)) q i).symm)))

/-- Sections over a discrete category are arbitrary families of elements. -/
private def discreteSectionsEquiv {I : Type v} (F : Discrete I ⥤ Type u) :
    F.sections ≃ ∀ i, F.obj (Discrete.mk i) where
  toFun s i := s.val (Discrete.mk i)
  invFun p := ⟨fun j => p j.as, by
    rintro ⟨i⟩ ⟨j⟩ ⟨h⟩
    cases h
    exact F.map_id_apply (Discrete.mk i) (p i)⟩
  left_inv s := by
    apply Subtype.ext
    funext j
    rfl
  right_inv p := rfl

/-- The underlying equivalence of a limiting fan with its coordinate families. -/
private def fanEquivPi {I : Type v} {X : I → TopCat.{u}}
    (c : Fan X) (hc : IsLimit c) : c.pt ≃ ∀ i, X i :=
  (Types.isLimitEquivSections (isLimitOfPreserves (forget TopCat) hc)).trans
    (discreteSectionsEquiv ((Discrete.functor X) ⋙ forget TopCat))

/-- A limiting fan is homeomorphic to the raw dependent product, even when that
product type is not an object of the fan's ambient category. -/
private def fanHomeomorphPi {I : Type v} {X : I → TopCat.{u}}
    (c : Fan X) (hc : IsLimit c) : c.pt ≃ₜ ∀ i, X i :=
  (fanEquivPi c hc).toHomeomorphOfIsInducing ⟨by
    rw [TopCat.induced_of_isLimit c hc, induced_to_pi]
    exact le_antisymm
      (le_iInf fun i => iInf_le _ (Discrete.mk i))
      (le_iInf fun j => iInf_le _ j.as)⟩

private theorem fanHomeomorphPi_apply {I : Type v} {X : I → TopCat.{u}}
    (c : Fan X) (hc : IsLimit c) (x : c.pt) (i : I) :
    fanHomeomorphPi c hc x i = (c.π.app (Discrete.mk i)).hom x := rfl

/-- The fundamental-group functor preserves every existing indexed product,
including the empty product, with independent index and space universes.
This is the categorical form of the product calculation in May, Chapter 2, §8;
it imposes no existence or index-smallness hypothesis. -/
instance functor_preservesLimitsOfShape_discrete (I : Type v) :
    PreservesLimitsOfShape (Discrete I) functor.{u} := by
  classical
  let (X : I → BasedTopCat.{u}) : PreservesLimit (Discrete.functor X) functor := by
    constructor
    intro c hc
    let cTop : Fan (fun i => (X i).right) :=
      Fan.mk c.pt.right (fun i => (c.π.app (Discrete.mk i)).right)
    -- The forgetful functor is a right adjoint: its left adjoint adjoins a basepoint.
    have hcTop : IsLimit cTop :=
      (Fan.isLimitMapConeEquiv
        (Under.forget (TopCat.of PUnit.{u + 1})) X c)
        (isLimitOfPreserves (Under.forget (TopCat.of PUnit.{u + 1})) hc)
    -- The product can be larger than the ambient universe; no bundled raw Pi
    -- object or blanket product-existence instance is needed.
    let h := fanHomeomorphPi cTop hcTop
    let p := fun i => BasedTopCat.point (X i)
    have hp : h (BasedTopCat.point c.pt) = p := by
      funext i
      change fanHomeomorphPi cTop hcTop (BasedTopCat.point c.pt) i = p i
      rw [fanHomeomorphPi_apply]
      exact BasedTopCat.map_point (c.π.app (Discrete.mk i))
    let f : C(c.pt.right, ∀ i, (X i).right) := ⟨h, h.continuous⟩
    let E : FundamentalGroupoid c.pt.right ≌ FundamentalGroupoid (∀ i, (X i).right) :=
      FundamentalGroupoidFunctor.equivOfHomotopyEquiv h.toHomotopyEquiv
    let e₀ : FundamentalGroup c.pt.right (BasedTopCat.point c.pt) ≃*
        FundamentalGroup (∀ i, (X i).right) (h (BasedTopCat.point c.pt)) :=
      E.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk (BasedTopCat.point c.pt))
    let e : FundamentalGroup c.pt.right (BasedTopCat.point c.pt) ≃*
        ∀ i, FundamentalGroup (X i).right (p i) :=
      (e₀.trans (eqToIso (C := FundamentalGroupoid (∀ i, (X i).right))
        (congrArg FundamentalGroupoid.mk hp)).conj).trans (piMulEquiv p)
    have he (q : FundamentalGroup c.pt.right (BasedTopCat.point c.pt)) (i : I) :
        e q i = functor.map (c.π.app (Discrete.mk i)) q := by
      have h₀ : e q i = map (ContinuousMap.eval i) p (mapOfEq f hp q) := rfl
      have h₁ : map (ContinuousMap.eval i) p (mapOfEq f hp q) =
          mapOfEq ((ContinuousMap.eval i).comp f)
            ((congrArg (ContinuousMap.eval i) hp).trans rfl) q :=
        (DFunLike.congr_fun (mapOfEq_rfl (ContinuousMap.eval i) p)
          (mapOfEq f hp q)).symm.trans
          (DFunLike.congr_fun (mapOfEq_comp (ContinuousMap.eval i) f hp rfl) q).symm
      have h₂ : mapOfEq ((ContinuousMap.eval i).comp f)
          ((congrArg (ContinuousMap.eval i) hp).trans rfl) q =
            functor.map (c.π.app (Discrete.mk i)) q := rfl
      exact h₀.trans (h₁.trans h₂)
    let d : Fan (fun i => functor.obj (X i)) :=
      Fan.mk (functor.obj c.pt) (fun i => functor.map (c.π.app (Discrete.mk i)))
    -- The existing group-forgetful functor creates limits of every size.
    -- Its Type-valued section characterization needs only this coordinate bijection.
    have hsection : Function.Bijective
        (Types.sectionOfCone ((forget GrpCat).mapCone d)) := by
      constructor
      · intro a b hab
        apply e.injective
        funext i
        rw [he a i, he b i]
        exact congrArg (fun s => s.val (Discrete.mk i)) hab
      · intro s
        refine ⟨e.symm (fun i => s.val (Discrete.mk i)), ?_⟩
        apply Subtype.ext
        funext j
        change functor.map (c.π.app (Discrete.mk j.as))
            (e.symm (fun i => s.val (Discrete.mk i))) = s.val j
        rw [← he]
        exact congrFun (e.apply_symm_apply _) j.as
    have hd : IsLimit d :=
      isLimitOfReflects (forget GrpCat)
        ((Types.isLimit_iff_bijective_sectionOfCone _).mpr hsection).some
    exact ⟨(Fan.isLimitMapConeEquiv functor X c).symm hd⟩
  exact preservesLimitsOfShape_of_discrete functor

end FundamentalGroup
