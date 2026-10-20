/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product

/-!
# Fundamental groupoids of indexed products

For a family `X : I → TopCat`, the index and the coordinate spaces may live in
independent universes. The functor `FundamentalGroupoidFunctor.piAssembly`
assembles coordinate objects and path classes, and
`FundamentalGroupoidFunctor.piProj` projects to a coordinate.
`FundamentalGroupoidFunctor.piProductIso` packages these functors as an
isomorphism of bundled groupoids, oriented from the product of the coordinate
groupoids to the fundamental groupoid of the product space.

The space of dependent functions has its product topology. The groupoids and
their product use the fundamental-groupoid and Pi-category instances. No
finiteness, nonemptiness, connectedness, or choice of basepoint is required.
The two bundled endpoints have object and morphism universes `max u v` for
`I : Type u` and `X : I → TopCat.{v}`.

## Implementation notes

The constructions and the assembly functor laws follow Mathlib's
`Mathlib.AlgebraicTopology.FundamentalGroupoid.Product`, by Praneeth Kolichala.
Projection uses the induced functor `FundamentalGroupoid.map`, which accepts
independent source and target universes. The underlying path-class assembly
and its characteristic equations are those of
`Mathlib.Topology.Homotopy.Product`.

The comparison theorems identify all three constructions with Mathlib's
`proj`, `piToPiTop`, and `piIso` when the index and coordinate universes agree.
No preservation-of-limits assertion in a fixed universe of `TopCat` is added.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace FundamentalGroupoidFunctor

universe u v

section Pi

variable {I : Type u} (X : I → TopCat.{v})

/-- Evaluation at a coordinate induces a functor from the fundamental groupoid
of a product space to the fundamental groupoid of that coordinate. -/
def piProj (i : I) :
    FundamentalGroupoid (∀ i, X i) ⥤ FundamentalGroupoid (X i) :=
  FundamentalGroupoid.map ⟨fun f => f i, continuous_apply i⟩

/-- The projection functor evaluates the underlying point. -/
@[simp]
theorem piProj_obj (i : I) (a : FundamentalGroupoid (∀ i, X i)) :
    (piProj X i).obj a = FundamentalGroupoid.mk (a.as i) :=
  rfl

/-- On arrows, the projection functor is projection of path homotopy classes. -/
@[simp]
theorem piProj_map (i : I) {a b : FundamentalGroupoid (∀ i, X i)} (p : a ⟶ b) :
    (piProj X i).map p = Path.Homotopic.proj i p :=
  rfl

/-- Assemble coordinate objects and path homotopy classes into the fundamental
groupoid of the product space. -/
def piAssembly :
    (∀ i, FundamentalGroupoid (X i)) ⥤ FundamentalGroupoid (∀ i, X i) where
  obj a := ⟨fun i => (a i).as⟩
  map p := Path.Homotopic.pi p
  map_id a := by
    change (Path.Homotopic.pi fun i => Path.Homotopic.Quotient.mk _) = _
    simp only [Path.Homotopic.pi_lift]
    rfl
  map_comp p q := (Path.Homotopic.comp_pi_eq_pi_comp p q).symm

/-- The assembly functor forms the dependent function of underlying points. -/
@[simp]
theorem piAssembly_obj (a : ∀ i, FundamentalGroupoid (X i)) :
    (piAssembly X).obj a = FundamentalGroupoid.mk (fun i => (a i).as) :=
  rfl

/-- On arrows, assembly is the product of path homotopy classes. -/
@[simp]
theorem piAssembly_map {a b : ∀ i, FundamentalGroupoid (X i)} (p : a ⟶ b) :
    (piAssembly X).map p = Path.Homotopic.pi p :=
  rfl

/-- On path representatives, assembly is the pointwise product path, stated in
its path-class normal form. -/
@[simp]
theorem piAssembly_map_mk (a b : ∀ i, FundamentalGroupoid (X i))
    (p : ∀ i, Path (a i).as (b i).as) :
    Path.Homotopic.pi (fun i => Path.Homotopic.Quotient.mk (p i)) =
      Path.Homotopic.Quotient.mk (Path.pi p) := by
  exact Path.Homotopic.pi_lift p

/-- Projecting an assembled arrow recovers its chosen coordinate. -/
theorem piProj_map_piAssembly (i : I) {a b : ∀ i, FundamentalGroupoid (X i)}
    (p : a ⟶ b) :
    (piProj X i).map ((piAssembly X).map p) = p i := by
  exact Path.Homotopic.proj_pi i p

/-- Assembling all coordinate projections recovers an arrow of the product space. -/
theorem piAssembly_map_piProj {a b : FundamentalGroupoid (∀ i, X i)} (p : a ⟶ b) :
    (piAssembly X).map (fun i => (piProj X i).map p) = p := by
  exact Path.Homotopic.pi_proj p

/-- The product of the coordinate fundamental groupoids is isomorphic to the
fundamental groupoid of the product space. Its inverse is the family of
functors induced by coordinate projections. -/
def piProductIso :
    Grpd.of (∀ i, FundamentalGroupoid (X i)) ≅
      Grpd.of (FundamentalGroupoid (∀ i, X i)) where
  hom := piAssembly X
  inv := Functor.pi' (piProj X)
  hom_inv_id := by
    change piAssembly X ⋙ Functor.pi' (piProj X) = 𝟭 _
    apply Functor.hext
    · intro a
      rfl
    · intro a b p
      exact heq_of_eq (funext fun i => piProj_map_piAssembly X i p)
  inv_hom_id := by
    change Functor.pi' (piProj X) ⋙ piAssembly X = 𝟭 _
    apply Functor.hext
    · intro a
      rfl
    · intro a b p
      exact heq_of_eq (piAssembly_map_piProj X p)

/-- The forward functor of the product isomorphism is coordinate assembly. -/
@[simp]
theorem piProductIso_hom : (piProductIso X).hom = piAssembly X :=
  rfl

/-- The inverse functor of the product isomorphism is the family of projections. -/
@[simp]
theorem piProductIso_inv : (piProductIso X).inv = Functor.pi' (piProj X) :=
  rfl

/-- The product isomorphism assembles the underlying coordinate points. -/
@[simp]
theorem piProductIso_hom_obj (a : ∀ i, FundamentalGroupoid (X i)) :
    (piProductIso X).hom.obj a = FundamentalGroupoid.mk (fun i => (a i).as) :=
  rfl

/-- The product isomorphism assembles coordinate path classes. -/
@[simp]
theorem piProductIso_hom_map {a b : ∀ i, FundamentalGroupoid (X i)} (p : a ⟶ b) :
    (piProductIso X).hom.map p = Path.Homotopic.pi p :=
  rfl

/-- The inverse product isomorphism evaluates the underlying point at every coordinate,
in the normal form of `piProductIso_inv`. -/
@[simp]
theorem piProductIso_inv_obj (a : FundamentalGroupoid (∀ i, X i)) :
    (Functor.pi' (piProj X)).obj a = fun i => FundamentalGroupoid.mk (a.as i) :=
  rfl

/-- The inverse product isomorphism projects a path class to every coordinate,
in the normal form of `piProductIso_inv`. -/
@[simp]
theorem piProductIso_inv_map {a b : FundamentalGroupoid (∀ i, X i)} (p : a ⟶ b) :
    (Functor.pi' (piProj X)).map p = fun i => Path.Homotopic.proj i p :=
  rfl

/-- Evaluation of the inverse arrow map is projection to the chosen coordinate. -/
theorem piProductIso_inv_map_apply (i : I) {a b : FundamentalGroupoid (∀ i, X i)}
    (p : a ⟶ b) :
    ((piProductIso X).inv.map p) i = Path.Homotopic.proj i p :=
  rfl

end Pi

section SameUniverse

variable {I : Type u} (X : I → TopCat.{u})

/-- At equal index and coordinate universes, projection agrees with Mathlib's
bundled fundamental-groupoid projection functor. -/
theorem piProj_eq_proj (i : I) : piProj X i = proj X i := by
  rfl

/-- At equal index and coordinate universes, assembly agrees with Mathlib's
product-to-product-space functor. -/
theorem piAssembly_eq_piToPiTop : piAssembly X = piToPiTop X := by
  rfl

/-- At equal index and coordinate universes, the product isomorphism agrees
with Mathlib's product isomorphism as an equality of bundled isomorphisms. -/
theorem piProductIso_eq_piIso : piProductIso X = piIso X := by
  exact Iso.ext (piAssembly_eq_piToPiTop X)

end SameUniverse

end FundamentalGroupoidFunctor
