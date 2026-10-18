/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.CategoryTheory.Groupoid.Covering
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.Combinatorics.Quiver.Covering

/-!
# Fibers and covering properties of the category-of-elements projection

For a type-valued functor on any category, `Functor.Elements.fiberEquiv` identifies
an object fiber of the projection with the functor's value. Its forward map transports
the element along the equality specifying its fiber; its inverse pairs a value with
its base object. When the projection is a covering, this equivalence sends canonical
lift targets to the corresponding functor maps and canonical monodromy to
`F.map a.hom`. These comparisons use the supplied covering proof and work for any
category. Automorphism multiplication composes the right factor first, so covariance
makes this the forward-hom left action.

For a functor `F : G ⥤ Type w` on a groupoid, the projection `Functor.Elements.π F`
is a covering of the underlying quivers. For an element `x`, an outgoing arrow
`g : x.obj ⟶ b` determines the target element `F.map g x.val` and the whole lifted
arrow. Reversal gives the corresponding bijection on incoming arrows.
No nonemptiness, connectedness or surjectivity on objects is required.

The category of elements, its groupoid structure and its projection are Mathlib's
constructions. The fiber equivalence follows the dependent-transport construction of
Mathlib's `Equiv.sigmaSubtype`, applied directly to objects of the category of elements.
The covering proof uses Mathlib's bijective-star criterion and groupoid reversal.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3, §§3–4, supplies
  the functor and group-action viewpoint for categorical coverings.
* `FundamentalGroupoids.CategoryTheory.Groupoid.Covering`, by Formal Frontier Agents,
  supplies the canonical lifting and monodromy constructions.
* `Mathlib.CategoryTheory.Elements`, by Kim Morrison and Joël Riou, supplies the
  category of elements and its projection.
* `Mathlib.CategoryTheory.FiberedCategory.Fiber`, by Calle Sönne and Paul Lezeau,
  supplies object fibers.
* `Mathlib.Logic.Equiv.Basic`, by Leonardo de Moura and Mario Carneiro, supplies the
  analogous `Equiv.sigmaSubtype` construction.
* `Mathlib.CategoryTheory.EqToHom`, by Reid Barton and Kim Morrison, supplies the
  interpretation of equality transport as a morphism.
* `Mathlib.CategoryTheory.Groupoid`, by Reid Barton, Kim Morrison and David Wärn,
  supplies groupoid reversal.
* `Mathlib.Combinatorics.Quiver.Covering`, by Antoine Labelle and Rémi Bottinelli,
  supplies the covering criterion for quivers with involutive reversal.
-/

@[expose] public section

universe u v w

namespace CategoryTheory.Functor.Elements

section Category

variable {G : Type u} [Category.{v} G]

/-- The object fiber of the category-of-elements projection over `g` is equivalent
to `F.obj g`. The forward map transports a value along the equality specifying its
fiber, and the inverse forms an element over `g`. -/
@[simps -isSimp apply, simps symm_apply]
def fiberEquiv (F : G ⥤ Type w) (g : G) : (π F).Fiber g ≃ F.obj g where
  toFun x := x.property ▸ x.val.val
  invFun z := ⟨F.elementsMk g z, rfl⟩
  left_inv := by
    rintro ⟨e, q⟩
    rcases e with @⟨b, z⟩
    change b = g at q
    cases q
    rfl
  right_inv z := rfl

/-- The fiber equivalence recovers the value of an element constructed over `g`. -/
@[simp]
theorem fiberEquiv_mk (F : G ⥤ Type w) (g : G) (z : F.obj g) :
    fiberEquiv F g ⟨F.elementsMk g z, rfl⟩ = z :=
  rfl

/-- Equality transport in the fiber equivalence agrees with applying `F` to the
morphism determined by the fiber equality. -/
theorem fiberEquiv_apply_eq_map (F : G ⥤ Type w) (g : G) (x : (π F).Fiber g) :
    fiberEquiv F g x = F.map (eqToHom x.property) x.val.val := by
  rcases x with ⟨e, q⟩
  rcases e with @⟨b, z⟩
  change b = g at q
  cases q
  simp only [fiberEquiv_mk, eqToHom_refl, Functor.map_id_apply]

end Category

/-- Under the fiber equivalence, a canonical lift target is the image under the
original functor map. This uses the supplied covering proof and does not require
the base category to be a groupoid. -/
theorem fiberEquiv_coveringLiftTarget {G : Type u} [Category.{v} G]
    (F : G ⥤ Type w) (hπ : (π F).toPrefunctor.IsCovering)
    {g h : G} (f : g ⟶ h) (x : (π F).Fiber g) :
    (fiberEquiv F h) ((π F).coveringLiftTarget hπ f x) =
      F.map f ((fiberEquiv F g) x) := by
  rw [fiberEquiv_apply_eq_map F h, fiberEquiv_apply_eq_map F g,
    ← ((π F).coveringLiftHom hπ f x).map_val]
  simpa only [F.map_comp_apply, π_map] using
    congrArg (fun k => F.map k x.val.val)
      ((π F).coveringLiftHom_map hπ f x)

/-- Under the fiber equivalence, canonical monodromy acts by the functor map of
the automorphism's forward hom. The scalar dictionary is the canonical left action
associated with the supplied covering proof. -/
theorem fiberEquiv_monodromyMulAction_smul {G : Type u} [Category.{v} G]
    (F : G ⥤ Type w) (hπ : (π F).toPrefunctor.IsCovering)
    (g : G) (a : Aut g) (x : (π F).Fiber g) :
    (fiberEquiv F g)
        (@SMul.smul (Aut g) ((π F).Fiber g)
          ((π F).monodromyMulAction hπ g).toSemigroupAction.toSMul a x) =
      F.map a.hom ((fiberEquiv F g) x) := by
  rw [(π F).monodromyMulAction_smul hπ a x]
  exact fiberEquiv_coveringLiftTarget F hπ a.hom x

/-- The projection from the category of elements of a type-valued functor on a
groupoid is a covering of the underlying quivers. -/
theorem π_isCovering {G : Type u} [Category.{v} G] [IsGroupoid G]
    (F : G ⥤ Type w) : (π F).toPrefunctor.IsCovering := by
  let baseGroupoid : Groupoid.{v} G := Groupoid.ofIsGroupoid
  let elementsGroupoid : Groupoid.{v} F.Elements :=
    @Functor.Elements.groupoid G baseGroupoid F
  refine @Prefunctor.isCovering_of_bijective_star
    F.Elements elementsGroupoid.toCategory.toCategoryStruct.toQuiver
    G baseGroupoid.toCategory.toCategoryStruct.toQuiver
    (π F).toPrefunctor
    (@groupoidHasInvolutiveReverse F.Elements elementsGroupoid)
    (@groupoidHasInvolutiveReverse G baseGroupoid)
    (@functorMapReverse F.Elements elementsGroupoid G baseGroupoid (π F)) ?_
  intro x
  constructor
  · rintro ⟨y, f⟩ ⟨z, g⟩ h
    rcases y with @⟨b, y⟩
    rcases z with @⟨c, z⟩
    change (⟨b, f.hom⟩ : Quiver.Star x.obj) = ⟨c, g.hom⟩ at h
    obtain rfl : b = c := congrArg Sigma.fst h
    have hfg : f.hom = g.hom := sigma_mk_injective h
    have hyz : y = z := by
      calc
        y = F.map f.hom x.val := f.map_val.symm
        _ = F.map g.hom x.val := congrArg (fun k => F.map k x.val) hfg
        _ = z := g.map_val
    subst z
    have hhom : f = g := hom_ext hfg
    cases hhom
    rfl
  · rintro ⟨b, g⟩
    refine ⟨⟨F.elementsMk b (F.map g x.val), homMk g rfl⟩, ?_⟩
    rfl

end CategoryTheory.Functor.Elements
