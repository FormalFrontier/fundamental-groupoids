/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.Combinatorics.Quiver.Covering

/-!
# Monodromy of a covering functor

For a functor `F : E ⥤ B` whose underlying prefunctor is a covering, the inverse
of its map on outgoing stars lifts an arrow from any object over its source.
`Functor.coveringLiftTarget` is the target of this lift, in the object fiber
`F.Fiber b`, and `Functor.coveringLiftHom` is its arrow.

Lifting automorphisms of `b` gives `Functor.monodromyMulAction`, a left action of
`Aut b` on `F.Fiber b`. Multiplication in `Aut b` composes the right factor first,
so this action uses the automorphism's hom without an inverse or an opposite.
The construction works for categories. The forward pretransitivity statement
requires `E` to be a preconnected groupoid, but imposes no further condition on
`B`. Conversely, over a preconnected groupoid `B`, pretransitivity on one
specified fiber implies that `E` is preconnected, with no groupoid structure
assumed on `E`. The proof lifts arrows into that fiber and a monodromy loop to
join any two objects by a zigzag. Both statements use pairwise connectedness;
neither surjectivity on objects nor nonemptiness of a fiber is required.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3, §§3–4:
  translation of fibers of a groupoid covering and its monodromy action.
  The preconnectedness criterion is a derived consequence of the fiber-translation
  argument of §4, rather than a theorem stated there.
* `Mathlib.Combinatorics.Quiver.Covering` supplies stars and covering prefunctors.
* `Mathlib.CategoryTheory.FiberedCategory.Fiber` supplies object fibers, and
  `Mathlib.CategoryTheory.Endomorphism` supplies automorphism groups.
* `Mathlib.CategoryTheory.IsConnected` supplies zigzags and preconnectedness, and
  `Mathlib.CategoryTheory.Groupoid` supplies groupoids on existing categories.
-/

@[expose] public section

universe vE vB uE uB

namespace CategoryTheory.Functor

variable {E : Type uE} {B : Type uB}

section Category

variable [Category.{vE} E] [Category.{vB} B] (F : E ⥤ B)
  (hF : F.toPrefunctor.IsCovering)

private theorem coveringStar_eq_iff {e y : E} {b : B} (hy : F.obj y = b)
    (g : e ⟶ y) (f : F.obj e ⟶ b) :
    F.toPrefunctor.star e (Quiver.Star.mk g) = Quiver.Star.mk f ↔
      F.map g ≫ eqToHom hy = f := by
  subst b
  change (⟨F.obj y, F.map g⟩ : Quiver.Star (F.obj e)) = ⟨F.obj y, f⟩ ↔ _
  simp

private theorem star_snd_comp_eqToHom {e : E} {s t : Quiver.Star e} (h : s = t) :
    s.2 ≫ eqToHom (congrArg Sigma.fst h) = t.2 := by
  cases h
  simp

/-- The unique outgoing lift of `f` from `x`, as a target-arrow pair. -/
noncomputable def coveringLift {b b' : B} (f : b ⟶ b') (x : F.Fiber b) :
    Quiver.Star x.val :=
  (Equiv.ofBijective (F.toPrefunctor.star x.val) (hF.star_bijective x.val)).symm
    ⟨b', eqToHom x.property ≫ f⟩

/-- Mapping the entire lifted target-arrow pair recovers the prescribed base arrow. -/
@[simp] theorem coveringLift_map {b b' : B} (f : b ⟶ b') (x : F.Fiber b) :
    F.toPrefunctor.star x.val (F.coveringLift hF f x) =
      ⟨b', eqToHom x.property ≫ f⟩ :=
  Equiv.ofBijective_apply_symm_apply _ _ _

/-- Uniqueness of the entire outgoing lift, including its target. -/
theorem coveringLift_unique {b b' : B} (f : b ⟶ b') (x : F.Fiber b)
    (s : Quiver.Star x.val)
    (hs : F.toPrefunctor.star x.val s = ⟨b', eqToHom x.property ≫ f⟩) :
    s = F.coveringLift hF f x :=
  (hF.star_bijective x.val).injective (hs.trans (F.coveringLift_map hF f x).symm)

/-- The target of the lift, as an object of the fiber over the target of `f`. -/
noncomputable def coveringLiftTarget {b b' : B} (f : b ⟶ b') (x : F.Fiber b) :
    F.Fiber b' :=
  ⟨(F.coveringLift hF f x).1, congrArg Sigma.fst (F.coveringLift_map hF f x)⟩

/-- The underlying object of the lifted target is the first projection of the lift. -/
@[simp] theorem coveringLiftTarget_val {b b' : B} (f : b ⟶ b') (x : F.Fiber b) :
    (F.coveringLiftTarget hF f x).val = (F.coveringLift hF f x).1 :=
  rfl

/-- The lifted arrow has source `x.val` and target the lifted fiber object. -/
noncomputable def coveringLiftHom {b b' : B} (f : b ⟶ b') (x : F.Fiber b) :
    x.val ⟶ (F.coveringLiftTarget hF f x).val :=
  (F.coveringLift hF f x).2

/-- The lifted arrow maps to `f`, after identifying the source and target fibers. -/
theorem coveringLiftHom_map {b b' : B} (f : b ⟶ b') (x : F.Fiber b) :
    F.map (F.coveringLiftHom hF f x) ≫
        eqToHom (F.coveringLiftTarget hF f x).property =
      eqToHom x.property ≫ f := by
  exact star_snd_comp_eqToHom (F.coveringLift_map hF f x)

/-- The lift of an identity is the identity target-arrow pair. -/
@[simp] theorem coveringLift_id {b : B} (x : F.Fiber b) :
    F.coveringLift hF (𝟙 b) x = ⟨x.val, 𝟙 x.val⟩ := by
  rcases x with ⟨e, rfl⟩
  symm
  apply F.coveringLift_unique hF (𝟙 (F.obj e)) ⟨e, rfl⟩
  change (⟨F.obj e, F.map (𝟙 e)⟩ : Quiver.Star (F.obj e)) =
    ⟨F.obj e, eqToHom (rfl : F.obj e = F.obj e) ≫ 𝟙 (F.obj e)⟩
  rw [F.map_id, eqToHom_refl, Category.id_comp]

/-- Lifting a composite composes the successive lifted target-arrow pairs. -/
theorem coveringLift_comp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
    (x : F.Fiber b₀) :
    F.coveringLift hF (f ≫ g) x =
      ⟨(F.coveringLiftTarget hF g (F.coveringLiftTarget hF f x)).val,
        F.coveringLiftHom hF f x ≫
          F.coveringLiftHom hF g (F.coveringLiftTarget hF f x)⟩ := by
  symm
  apply F.coveringLift_unique hF (f ≫ g) x
  apply (coveringStar_eq_iff F
    (F.coveringLiftTarget hF g (F.coveringLiftTarget hF f x)).property _ _).mpr
  rw [F.map_comp, Category.assoc,
    F.coveringLiftHom_map hF g (F.coveringLiftTarget hF f x),
    ← Category.assoc, F.coveringLiftHom_map hF f x]
  exact Category.assoc _ _ _

/-- Lifting an identity leaves the fiber object unchanged. -/
@[simp] theorem coveringLiftTarget_id {b : B} (x : F.Fiber b) :
    F.coveringLiftTarget hF (𝟙 b) x = x := by
  apply Subtype.ext
  exact congrArg Sigma.fst (F.coveringLift_id hF x)

/-- Targets of lifts respect composition. -/
theorem coveringLiftTarget_comp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
    (x : F.Fiber b₀) :
    F.coveringLiftTarget hF (f ≫ g) x =
      F.coveringLiftTarget hF g (F.coveringLiftTarget hF f x) := by
  apply Subtype.ext
  exact congrArg Sigma.fst (F.coveringLift_comp hF f g x)

/-- The identity lift has identity arrow, with its target identified by
`coveringLiftTarget_id`. -/
@[simp] theorem coveringLiftHom_id {b : B} (x : F.Fiber b) :
    F.coveringLiftHom hF (𝟙 b) x ≫
        eqToHom (congrArg Subtype.val (F.coveringLiftTarget_id hF x)) =
      𝟙 x.val := by
  simpa only [coveringLiftHom, coveringLiftTarget] using
    star_snd_comp_eqToHom (F.coveringLift_id hF x)

/-- Lifted arrows respect composition, with their targets identified by
`coveringLiftTarget_comp`. -/
theorem coveringLiftHom_comp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
    (x : F.Fiber b₀) :
    F.coveringLiftHom hF (f ≫ g) x ≫
        eqToHom (congrArg Subtype.val (F.coveringLiftTarget_comp hF f g x)) =
      F.coveringLiftHom hF f x ≫
        F.coveringLiftHom hF g (F.coveringLiftTarget hF f x) := by
  simpa only [coveringLiftHom, coveringLiftTarget] using
    star_snd_comp_eqToHom (F.coveringLift_comp hF f g x)

/-- The monodromy action on an object fiber, obtained by lifting automorphisms
and taking their targets. -/
@[instance_reducible]
noncomputable def monodromyMulAction (b : B) : MulAction (Aut b) (F.Fiber b) where
  smul a x := F.coveringLiftTarget hF a.hom x
  one_smul x := by
    change F.coveringLiftTarget hF (𝟙 b) x = x
    exact F.coveringLiftTarget_id hF x
  mul_smul a c x := by
    change F.coveringLiftTarget hF (c.hom ≫ a.hom) x =
      F.coveringLiftTarget hF a.hom (F.coveringLiftTarget hF c.hom x)
    exact F.coveringLiftTarget_comp hF c.hom a.hom x

/-- The monodromy action sends a fiber object to the target of the lifted hom. -/
theorem monodromyMulAction_smul {b : B} (a : Aut b) (x : F.Fiber b) :
    (F.monodromyMulAction hF b).toSemigroupAction.toSMul.smul a x =
      F.coveringLiftTarget hF a.hom x :=
  rfl

end Category

section Groupoid

variable [Groupoid.{vE} E] [Category.{vB} B] (F : E ⥤ B)
  (hF : F.toPrefunctor.IsCovering)

/-- The monodromy action of a covering functor with preconnected total groupoid
is pretransitive on each object fiber. This generalizes the forward transitivity
assertion of May, Chapter 3, §4: the base need only be a category, and neither
object-surjectivity nor a nonempty-fiber hypothesis is required. -/
theorem monodromyMulAction_isPretransitive [IsPreconnected E] (b : B) :
    @MulAction.IsPretransitive (Aut b) (F.Fiber b)
      (F.monodromyMulAction hF b).toSemigroupAction.toSMul := by
  rw [MulAction.isPretransitive_iff]
  intro x y
  obtain ⟨g⟩ := nonempty_hom_of_preconnected_groupoid x.val y.val
  let a : Aut b :=
    (eqToIso x.property).symm ≪≫
      F.mapIso ((Groupoid.isoEquivHom x.val y.val).symm g) ≪≫ eqToIso y.property
  have ha : eqToHom x.property ≫ a.hom = F.map g ≫ eqToHom y.property := by
    change eqToHom x.property ≫
        (eqToHom x.property.symm ≫ (F.map g ≫ eqToHom y.property)) =
      F.map g ≫ eqToHom y.property
    rw [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
  have hg : Quiver.Star.mk g = F.coveringLift hF a.hom x := by
    apply F.coveringLift_unique hF a.hom x
    exact (coveringStar_eq_iff F y.property g
      (eqToHom x.property ≫ a.hom)).mpr ha.symm
  refine ⟨a, ?_⟩
  refine (F.monodromyMulAction_smul hF a x).trans ?_
  apply Subtype.ext
  exact (F.coveringLiftTarget_val hF a.hom x).trans (congrArg Sigma.fst hg).symm

end Groupoid

universe uG vG

/-- A covering functor to a preconnected groupoid has preconnected total category
if its canonical monodromy action on one specified object fiber is pretransitive.
The total category is not assumed to be a groupoid. Preconnectedness and
pretransitivity are pairwise, so the total category and the fiber may be empty.
This is a derived consequence of the fiber-translation argument in May,
Chapter 3, §4, rather than a theorem stated there. -/
theorem isPreconnected_of_monodromyMulAction_isPretransitive
    {E : Type uE} {G : Type uG} [Category.{vE} E] [Category.{vG} G]
    [IsGroupoid G] [IsPreconnected G]
    (P : E ⥤ G) (hP : P.toPrefunctor.IsCovering) (g : G)
    (htrans : @MulAction.IsPretransitive (Aut g) (P.Fiber g)
      (P.monodromyMulAction hP g).toSemigroupAction.toSMul) : IsPreconnected E := by
  let baseGroupoid : Groupoid.{vG} G := Groupoid.ofIsGroupoid
  have hbase : ∀ b b' : G, Nonempty (b ⟶ b') :=
    @nonempty_hom_of_preconnected_groupoid G baseGroupoid ‹IsPreconnected G›
  apply zigzag_isPreconnected
  intro x y
  obtain ⟨f⟩ := hbase (P.obj x) g
  obtain ⟨k⟩ := hbase (P.obj y) g
  let xg : P.Fiber g := P.coveringLiftTarget hP f ⟨x, rfl⟩
  let yg : P.Fiber g := P.coveringLiftTarget hP k ⟨y, rfl⟩
  obtain ⟨a, ha⟩ := htrans.exists_smul_eq xg yg
  have htarget : P.coveringLiftTarget hP a.hom xg = yg :=
    (P.monodromyMulAction_smul hP a xg).symm.trans ha
  exact (Zigzag.of_hom_hom
      (P.coveringLiftHom hP f ⟨x, rfl⟩)
      (P.coveringLiftHom hP a.hom xg ≫
        eqToHom (congrArg Subtype.val htarget))).trans
    (Zigzag.of_inv (P.coveringLiftHom hP k ⟨y, rfl⟩))

end CategoryTheory.Functor
