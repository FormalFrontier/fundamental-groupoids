/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Topology.Category.TopCat.Limits.Products

/-!
# Products of based spaces

`BasedTopCat.piIsoPi` identifies the chosen categorical product with the dependent
product of the underlying spaces, based at the family of selected points. Its
underlying isomorphism is the composite of the product-preservation isomorphism
for `Under.forget` and `TopCat.piIsoPi`.

The explicit product lies in the ambient universe `max u v`, where `v` is the
index universe. This identification makes no assertion that every large-index
product exists in a smaller fixed category of based spaces.

## References

* Mathlib's `Mathlib.CategoryTheory.Limits.Over`, by Johan Commelin, Reid Barton
  and Bhavik Mehta, supplies the limits created by the under-category forgetful functor.
* Mathlib's `Mathlib.Topology.Category.TopCat.Limits.Products`, by Patrick Massot,
  Kim Morrison, Mario Carneiro and Andrew Yang, supplies the topological product.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace BasedTopCat

/-- The chosen product of based spaces is isomorphic to their dependent product,
based at the family of selected points. -/
def piIsoPi {I : Type v} (X : I → BasedTopCat.{max u v}) :
    ∏ᶜ X ≅ of (∀ i, (X i).right) (fun i => point (X i)) :=
  Under.isoMk
    ((PreservesProduct.iso (Under.forget (TopCat.of PUnit.{max (u + 1) (v + 1)})) X) ≪≫
      TopCat.piIsoPi (fun i => (X i).right)) (by
        apply TopCat.ext
        intro t
        cases t
        funext i
        exact (TopCat.piIsoPi_hom_apply (fun j => (X j).right) i
          ((PreservesProduct.iso
            (Under.forget (TopCat.of PUnit.{max (u + 1) (v + 1)})) X).hom
              (point (∏ᶜ X)))).trans
          ((ConcreteCategory.congr_hom
            (piComparison_comp_π
              (Under.forget (TopCat.of PUnit.{max (u + 1) (v + 1)})) X i)
            (point (∏ᶜ X))).trans (map_point (Pi.π X i))))

/-- The underlying forward map uses the forgetful product comparison followed by
the topological product identification. -/
theorem piIsoPi_hom_right {I : Type v} (X : I → BasedTopCat.{max u v}) :
    (piIsoPi X).hom.right =
      (PreservesProduct.iso (Under.forget (TopCat.of PUnit.{max (u + 1) (v + 1)})) X).hom ≫
        (TopCat.piIsoPi (fun i => (X i).right)).hom := rfl

/-- Each coordinate of the forward map is the corresponding categorical projection. -/
@[simp]
theorem piIsoPi_hom_apply {I : Type v} (X : I → BasedTopCat.{max u v})
    (x : (∏ᶜ X : BasedTopCat.{max u v}).right) (i : I) :
    TopCat.Hom.hom (Y := TopCat.of (∀ j, (X j).right))
      (piIsoPi X).hom.right x i = (Pi.π X i).right.hom x := by
  rw [piIsoPi_hom_right]
  exact (TopCat.piIsoPi_hom_apply (fun j => (X j).right) i
    ((PreservesProduct.iso
      (Under.forget (TopCat.of PUnit.{max (u + 1) (v + 1)})) X).hom x)).trans
    (ConcreteCategory.congr_hom
      (piComparison_comp_π
        (Under.forget (TopCat.of PUnit.{max (u + 1) (v + 1)})) X i) x)

/-- The inverse product identification has the coordinate evaluation maps as its legs. -/
@[reassoc (attr := simp)]
theorem piIsoPi_inv_π {I : Type v} (X : I → BasedTopCat.{max u v}) (i : I) :
    (piIsoPi X).inv.right ≫ (Pi.π X i).right =
      TopCat.piπ (fun j => (X j).right) i := by
  apply TopCat.ext
  intro x
  change (Pi.π X i).right.hom ((piIsoPi X).inv.right.hom x) = x i
  rw [← piIsoPi_hom_apply]
  exact congrFun
    (ConcreteCategory.congr_hom (Under.inv_right_hom_right (piIsoPi X)) x) i

/-- The forward product identification sends the selected point to its coordinate family. -/
@[simp]
theorem piIsoPi_hom_point {I : Type v} (X : I → BasedTopCat.{max u v}) :
    TopCat.Hom.hom (Y := TopCat.of (∀ i, (X i).right))
      (piIsoPi X).hom.right (point (∏ᶜ X)) = fun i => point (X i) :=
  map_point (piIsoPi X).hom

end BasedTopCat
