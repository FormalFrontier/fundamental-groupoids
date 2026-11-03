/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.PUnit
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Fundamental groupoids with singleton path components

The forward functor retains each point and sends each path class to the discrete morphism
specified by its endpoint equality. The reverse functor is the functor from a discrete
category determined by the canonical point inclusion, without a hypothesis on path components.
The two functors form a canonical equivalence when all path components are subsingletons.
This condition concerns paths, not discreteness of the topology on the underlying space.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X]

private theorem toTop_eq_of_hom (hX : ∀ x : X, (pathComponent x).Subsingleton)
    {x y : FundamentalGroupoid X} (p : x ⟶ y) :
    toTop (X := TopCat.of X) x = toTop (X := TopCat.of X) y := by
  refine Path.Homotopic.Quotient.ind
    (motive := fun _ => toTop (X := TopCat.of X) x = toTop (X := TopCat.of X) y)
    ?_ (toPath (X := TopCat.of X) p)
  intro q
  exact hX _ (mem_pathComponent_self _) (mem_pathComponent_iff.mpr ⟨q⟩)

/-- The point-preserving functor to the discrete category when every path component is a
subsingleton. Its action on morphisms is the equality morphism forced by the endpoints. -/
def toDiscrete (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    FundamentalGroupoid X ⥤ Discrete X where
  obj x := Discrete.mk (toTop (X := TopCat.of X) x)
  map p := Discrete.eqToHom' (by exact toTop_eq_of_hom hX p)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The functor determined by the canonical inclusion of points into their fundamental
groupoid. This construction needs no hypothesis on path components. -/
noncomputable def fromDiscrete : Discrete X ⥤ FundamentalGroupoid X :=
  Discrete.functor (fun x : X => fromTop (X := TopCat.of X) x)

/-- The forward functor retains the underlying point of every object. -/
@[simp] theorem toDiscrete_obj (hX : ∀ x : X, (pathComponent x).Subsingleton)
    (x : FundamentalGroupoid X) :
    (toDiscrete hX).obj x = Discrete.mk (toTop (X := TopCat.of X) x) := rfl

/-- A point included in the fundamental groupoid is sent to that same discrete object. -/
@[simp] theorem toDiscrete_obj_fromTop (hX : ∀ x : X, (pathComponent x).Subsingleton)
    (x : X) :
    (toDiscrete hX).obj (fromTop (X := TopCat.of X) x) = Discrete.mk x := rfl

/-- Every morphism is sent to the discrete morphism for its endpoint equality. -/
theorem toDiscrete_map (hX : ∀ x : X, (pathComponent x).Subsingleton)
    {x y : FundamentalGroupoid X} (p : x ⟶ y)
    (hxy : toTop (X := TopCat.of X) x = toTop (X := TopCat.of X) y) :
    (toDiscrete hX).map p = Discrete.eqToHom' hxy :=
  Subsingleton.elim _ _

/-- The morphism characteristic applies to every class of paths between two points. -/
theorem toDiscrete_map_fromPath (hX : ∀ x : X, (pathComponent x).Subsingleton)
    {x y : X} (p : Path.Homotopic.Quotient x y) (hxy : x = y) :
    (toDiscrete hX).map (fromPath p) = Discrete.eqToHom' hxy :=
  Subsingleton.elim _ _

/-- The reverse functor includes the underlying point of every discrete object. -/
@[simp] theorem fromDiscrete_obj (x : Discrete X) :
    (fromDiscrete (X := X)).obj x = fromTop (X := TopCat.of X) x.as :=
  Discrete.functor_obj_eq_as _ x

/-- The reverse functor includes each point as its canonical fundamental-groupoid object. -/
theorem fromDiscrete_obj_mk (x : X) :
    (fromDiscrete (X := X)).obj (Discrete.mk x) = fromTop (X := TopCat.of X) x :=
  Discrete.functor_obj _ x

/-- A discrete morphism is sent to the fundamental-groupoid equality morphism on its points. -/
theorem fromDiscrete_map {x y : Discrete X} (p : x ⟶ y) :
    (fromDiscrete (X := X)).map p =
      eqToHom (congrArg (fun z : X => fromTop (X := TopCat.of X) z)
        (Discrete.eq_of_hom p)) := by
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      have hxy : x = y := Discrete.eq_of_hom p
      subst y
      have hp : p = 𝟙 (Discrete.mk x) := Subsingleton.elim _ _
      subst p
      have hid : HEq (𝟙 ((fromDiscrete (X := X)).obj (Discrete.mk x)))
          (𝟙 (fromTop (X := TopCat.of X) x)) :=
        Eq.ndrec
          (motive := fun z : FundamentalGroupoid X =>
            HEq (𝟙 ((fromDiscrete (X := X)).obj (Discrete.mk x))) (𝟙 z))
          (HEq.refl _) (fromDiscrete_obj_mk x)
      simpa only [eqToHom_refl] using
        ((fromDiscrete (X := X)).map_id (Discrete.mk x)).trans (eq_of_heq hid)

private theorem path_eq_refl (hX : ∀ x : X, (pathComponent x).Subsingleton)
    {x : X} (p : Path x x) : p = Path.refl x := by
  apply Path.ext
  funext t
  -- The entire path range lies in this component, not only its endpoints.
  have hrange : Set.range p.extend ⊆ pathComponent x :=
    (isPathConnected_range p.continuous_extend).subset_pathComponent
      (show x ∈ Set.range p.extend from ⟨0, p.extend_zero⟩)
  exact hX x (hrange ⟨t, p.extend_extends' t⟩) (mem_pathComponent_self x)

private theorem hom_eq (hX : ∀ x : X, (pathComponent x).Subsingleton)
    {x y : FundamentalGroupoid X} (p q : x ⟶ y) : p = q := by
  cases x with
  | mk x =>
    cases y with
    | mk y =>
      have hxy : x = y := toTop_eq_of_hom hX p
      subst y
      exact Path.Homotopic.Quotient.ind₂
        (motive := fun a b => fromPath a = fromPath b)
        (fun a b => by rw [path_eq_refl hX a, path_eq_refl hX b])
        (toPath (X := TopCat.of X) p) (toPath (X := TopCat.of X) q)

/-- The canonical equivalence with the discrete category on the same points when every path
component is a subsingleton. Its forward and inverse functors are `toDiscrete` and
`fromDiscrete`, respectively. -/
noncomputable def equivDiscrete (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    FundamentalGroupoid X ≌ Discrete X := by
  refine CategoryTheory.Equivalence.mk (toDiscrete hX) (fromDiscrete (X := X)) ?_ ?_
  · refine NatIso.ofComponents (fun x => eqToIso ?_) ?_
    · simp only [Functor.id_obj, Functor.comp_obj, toDiscrete_obj, fromDiscrete_obj]
    · intro x y p
      exact (by exact hom_eq hX _ _)
  · refine Discrete.natIso (fun x => eqToIso ?_)
    cases x with
    | mk x =>
      simp only [Functor.comp_obj, Functor.id_obj, fromDiscrete_obj,
        toDiscrete_obj_fromTop]

/-- The forward functor of the canonical equivalence is the point-preserving functor. -/
@[simp] theorem equivDiscrete_functor (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    (equivDiscrete hX).functor = toDiscrete hX := rfl

/-- The inverse functor of the canonical equivalence is the hypothesis-free point inclusion. -/
@[simp] theorem equivDiscrete_inverse (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    (equivDiscrete hX).inverse = fromDiscrete (X := X) := rfl

/-- The point-preserving functor is an equivalence when path components are subsingletons. -/
theorem toDiscrete_isEquivalence (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    Functor.IsEquivalence (toDiscrete hX) := by
  simpa only [equivDiscrete_functor] using
    (inferInstance : Functor.IsEquivalence (equivDiscrete hX).functor)

/-- The canonical forward and reverse functors are the two functors of an equivalence. -/
theorem exists_equivalence_toDiscrete (hX : ∀ x : X, (pathComponent x).Subsingleton) :
    ∃ e : FundamentalGroupoid X ≌ Discrete X,
      e.functor = toDiscrete hX ∧ e.inverse = fromDiscrete (X := X) :=
  ⟨equivDiscrete hX, equivDiscrete_functor hX, equivDiscrete_inverse hX⟩

/-- The canonical equivalence for a totally disconnected space. In particular this applies
with the existing instances when the topology is discrete. -/
noncomputable def equivDiscreteOfTotallyDisconnectedSpace [TotallyDisconnectedSpace X] :
    FundamentalGroupoid X ≌ Discrete X :=
  equivDiscrete (fun x _ ha _ hb =>
    (totallyDisconnectedSpace_iff_connectedComponent_subsingleton.mp
      (inferInstance : TotallyDisconnectedSpace X) x)
      (pathComponent_subset_component x ha) (pathComponent_subset_component x hb))

/-- The forward functor in the totally disconnected case is the canonical point-preserving
functor, using the inclusion of path components into connected components. -/
@[simp] theorem equivDiscreteOfTotallyDisconnectedSpace_functor [TotallyDisconnectedSpace X] :
    (equivDiscreteOfTotallyDisconnectedSpace (X := X)).functor =
      toDiscrete (fun x _ ha _ hb =>
        (totallyDisconnectedSpace_iff_connectedComponent_subsingleton.mp
          (inferInstance : TotallyDisconnectedSpace X) x)
          (pathComponent_subset_component x ha) (pathComponent_subset_component x hb)) :=
  equivDiscrete_functor _

/-- The inverse functor in the totally disconnected case is the point inclusion. -/
@[simp] theorem equivDiscreteOfTotallyDisconnectedSpace_inverse [TotallyDisconnectedSpace X] :
    (equivDiscreteOfTotallyDisconnectedSpace (X := X)).inverse = fromDiscrete (X := X) :=
  equivDiscrete_inverse _

/-- The totally disconnected specialization retains each point as the same discrete object. -/
theorem equivDiscreteOfTotallyDisconnectedSpace_obj [TotallyDisconnectedSpace X] (x : X) :
    (equivDiscreteOfTotallyDisconnectedSpace (X := X)).functor.obj
      (fromTop (X := TopCat.of X) x) = Discrete.mk x := by
  rw [equivDiscreteOfTotallyDisconnectedSpace_functor]
  exact toDiscrete_obj_fromTop _ x

/-- On `PUnit`, the forward functor of the canonical equivalence is naturally isomorphic
to the forward functor of `punitEquivDiscretePUnit`. -/
theorem equivDiscrete_punit_functor_iso
    (hX : ∀ x : PUnit.{u + 1}, (pathComponent x).Subsingleton) :
    Nonempty ((equivDiscrete hX).functor ≅
      (punitEquivDiscretePUnit.{u, u}).functor) := by
  refine ⟨NatIso.ofComponents (fun x => eqToIso ?_) ?_⟩
  · exact Discrete.as_bijective.injective (Subsingleton.elim _ _)
  · intro x y p
    exact Subsingleton.elim _ _

variable {Y : Type v} [TopologicalSpace Y]

/-- The forward functor commutes with the functors induced by a continuous map. -/
theorem toDiscrete_naturality (hX : ∀ x : X, (pathComponent x).Subsingleton)
    (hY : ∀ y : Y, (pathComponent y).Subsingleton) (f : C(X, Y)) :
    FundamentalGroupoid.map f ⋙ toDiscrete hY =
      toDiscrete hX ⋙ Discrete.functor (fun x : X => Discrete.mk (f x)) := by
  have hobj : ∀ x : FundamentalGroupoid X,
      (FundamentalGroupoid.map f ⋙ toDiscrete hY).obj x =
        (toDiscrete hX ⋙ Discrete.functor (fun x : X => Discrete.mk (f x))).obj x := by
    intro x
    simp only [Functor.comp_obj, toDiscrete_obj, Discrete.functor_obj]; rfl
  apply Functor.toPrefunctor_injective
  exact Prefunctor.ext hobj (fun _ _ _ => Subsingleton.elim _ _)

/-- The reverse functor commutes with the functors induced by any continuous map, without
hypotheses on path components in either space. -/
theorem fromDiscrete_naturality (f : C(X, Y)) :
    Discrete.functor (fun x : X => Discrete.mk (f x)) ⋙ fromDiscrete (X := Y) =
      fromDiscrete (X := X) ⋙ FundamentalGroupoid.map f := by
  apply Discrete.functor_ext
  intro x
  simp only [Functor.comp_obj, Discrete.functor_obj, fromDiscrete_obj_mk]; rfl

end FundamentalGroupoid
