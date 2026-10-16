/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Subpath

/-!
# Local generation of fundamental groupoids over open covers

A composition-stable morphism property on `FundamentalGroupoid X` can be checked on the
images of the fundamental groupoids of the members of any indexed open cover. The cover
and its local identity arrows already supply all identity arrows: a separate identity or
inverse stability hypothesis is unnecessary. The index type and space have independent
universes, and neither needs to be nonempty.

The generated-arrow statement uses `MorphismProperty.strictMap` and
`MorphismProperty.multiplicativeClosure`. The natural-transformation constructor applies
the induction principle to Mathlib's `MorphismProperty.naturalityProperty`; its target can
be any category, not necessarily a groupoid.

## Limitations

This is the local-generation step supporting the proof in May, Chapter 2, §7, generalized
to arbitrary indexed open covers without connectedness or intersection assumptions. It
is not the van Kampen colimit theorem. In particular, it does not construct a functor from
compatible local functors: homotopy-grid pasting, refinement independence and the colimit
descent construction are separate questions.

## References

- J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §7.
- Mathlib's interval subdivision API in `Mathlib.Topology.UnitInterval`, by Patrick Massot
  and Kim Morrison, and its subpath/concatenation API in `Mathlib.Topology.Subpath`, by
  Sebastian Kumar.
- Mathlib's morphism-property composition, strict-image and closure APIs, by Andrew Yang,
  Joël Riou and Aras Ergus. No additional cover or generation structure is introduced.
-/

@[expose] public section

universe u v w w'

open CategoryTheory TopologicalSpace

namespace FundamentalGroupoid

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Opens X}

open scoped unitInterval

/-- The constant path represents the identity arrow of the fundamental groupoid. -/
theorem fromPath_mk_refl (a : X) :
    fromPath (Path.Homotopic.Quotient.mk (Path.refl a)) = 𝟙 (mk a) := rfl

/-- Concatenation of paths represents composition of their fundamental-groupoid arrows. -/
theorem fromPath_mk_trans {a b c : X} (p : Path a b) (q : Path b c) :
    fromPath (Path.Homotopic.Quotient.mk (p.trans q)) =
      fromPath (Path.Homotopic.Quotient.mk p) ≫ fromPath (Path.Homotopic.Quotient.mk q) := rfl

/-- Mapping a representative path gives the image of its fundamental-groupoid arrow. -/
theorem map_fromPath_mk {Y : Type*} [TopologicalSpace Y] (f : C(X, Y))
    {a b : X} (p : Path a b) :
    (map f).map (fromPath (Path.Homotopic.Quotient.mk p)) =
      fromPath (Path.Homotopic.Quotient.mk (p.map f.continuous)) := rfl

-- Restrict a path to a cover member once, keeping its endpoints in that subtype.
private theorem morphismProperty_mk_of_range_subset
    (P : MorphismProperty (FundamentalGroupoid X))
    (hP : ∀ (i : ι) ⦃x y : FundamentalGroupoid (U i)⦄ (f : x ⟶ y),
      P ((map (ContinuousMap.subtypeVal (U i))).map f))
    {a b : X} (p : Path a b) (i : ι) (hp : Set.range p ⊆ U i) :
    P (fromPath (Path.Homotopic.Quotient.mk p)) := by
  have ha : a ∈ U i := p.source ▸ hp ⟨0, rfl⟩
  have hb : b ∈ U i := p.target ▸ hp ⟨1, rfl⟩
  let q : Path (⟨a, ha⟩ : U i) ⟨b, hb⟩ :=
    { toFun := fun t => ⟨p t, hp ⟨t, rfl⟩⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  have hq : q.map continuous_subtype_val = p := by
    ext t
    rfl
  have hmap :
      (map (ContinuousMap.subtypeVal (U i : Set X))).map
          (fromPath (Path.Homotopic.Quotient.mk q)) =
        fromPath (Path.Homotopic.Quotient.mk p) := by
    rw [map_fromPath_mk]
    exact congrArg (fun r : Path a b => fromPath (Path.Homotopic.Quotient.mk r)) hq
  exact hmap ▸ hP i (fromPath (Path.Homotopic.Quotient.mk q))

-- Endpoint transport changes neither the path nor the property of its class.
private theorem morphismProperty_mk_cast_iff
    (P : MorphismProperty (FundamentalGroupoid X))
    {a b a' b' : X} (p : Path a b) (ha : a' = a) (hb : b' = b) :
    P (fromPath (Path.Homotopic.Quotient.mk (p.cast ha hb))) ↔
      P (fromPath (Path.Homotopic.Quotient.mk p)) := by
  subst a' b'
  rfl

-- Composition stability extends from the factors to Mathlib's concatenation.
private theorem morphismProperty_concat
    (P : MorphismProperty (FundamentalGroupoid X)) [P.IsStableUnderComposition]
    (hid : ∀ a : X, P (𝟙 (mk a))) {n : ℕ} (p : Fin (n + 1) → X)
    (q : (k : Fin n) → Path (p k.castSucc) (p k.succ))
    (hq : ∀ k, P (fromPath (Path.Homotopic.Quotient.mk (q k)))) :
    P (fromPath (Path.Homotopic.Quotient.mk (Path.concat p q))) := by
  induction n with
  | zero =>
    have hzero : fromPath (Path.Homotopic.Quotient.mk (Path.concat p q)) =
        𝟙 (mk (p 0)) := by
      rw [Path.concat_zero]
      exact fromPath_mk_refl _
    exact hzero.symm ▸ hid (p 0)
  | succ n ih =>
    have hsucc : fromPath (Path.Homotopic.Quotient.mk (Path.concat p q)) =
        fromPath (Path.Homotopic.Quotient.mk
          (Path.concat (p ∘ Fin.castSucc) (fun k => q k.castSucc))) ≫
        fromPath (Path.Homotopic.Quotient.mk (q (Fin.last n))) := by
      rw [Path.concat_succ]
      exact fromPath_mk_trans _ _
    exact hsucc.symm ▸ P.comp_mem _ _ (ih (p ∘ Fin.castSucc) (fun k => q k.castSucc)
      (fun k => hq k.castSucc)) (hq (Fin.last n))

/-- Small-path induction over an indexed open cover: a composition-stable morphism property
that holds on every local inclusion image holds on every arrow of the fundamental groupoid.

This is the local-generation step of May, *A Concise Course in Algebraic Topology*,
Chapter 2, §7, without the connectedness or intersection assumptions of his colimit diagram.
Local identity arrows and the cover supply identities, so neither a separate identity
hypothesis nor stability under inverses is required. -/
theorem morphismProperty_of_isOpenCover (hU : IsOpenCover U)
    (P : MorphismProperty (FundamentalGroupoid X)) [P.IsStableUnderComposition]
    (hP : ∀ (i : ι) ⦃x y : FundamentalGroupoid (U i)⦄ (f : x ⟶ y),
      P ((map (ContinuousMap.subtypeVal (U i))).map f))
    {x y : FundamentalGroupoid X} (f : x ⟶ y) : P f := by
  obtain ⟨a⟩ := x
  obtain ⟨b⟩ := y
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
  have hid (a : X) : P (𝟙 (mk a)) := by
    obtain ⟨i, hi⟩ := hU.exists_mem a
    have hmap : (map (ContinuousMap.subtypeVal (U i : Set X))).map
        (𝟙 (mk (⟨a, hi⟩ : U i))) = 𝟙 (mk a) :=
      (map (ContinuousMap.subtypeVal (U i : Set X))).map_id _
    exact hmap ▸ hP i (𝟙 (mk (⟨a, hi⟩ : U i)))
  have hcover := hU.comap p.toContinuousMap
  obtain ⟨t, ht₀, hmono, ⟨n, hn⟩, hsmall⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => ((U i).comap p.toContinuousMap).isOpen)
      (by rw [hcover.iSup_set_eq_univ])
  have hpiece (k : ℕ) :
      P (fromPath (Path.Homotopic.Quotient.mk (p.subpath (t k) (t (k + 1))))) := by
    obtain ⟨i, hi⟩ := hsmall k
    apply morphismProperty_mk_of_range_subset P hP _ i
    rw [Path.range_subpath_of_le _ _ _ (hmono (Nat.le_succ k))]
    rintro _ ⟨s, hs, rfl⟩
    exact hi hs
  let s : Fin (n + 1) → I := fun k => t k
  have hconcat := morphismProperty_concat P hid (p ∘ s)
    (fun k => p.subpath (s k.castSucc) (s k.succ)) (fun k => hpiece k)
  have heq := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.concat_subpath p s)
  rw [heq] at hconcat
  -- Transport the endpoints in the entire proposition, including its implicit objects.
  have hp : P (fromPath (Path.Homotopic.Quotient.mk (p.subpath 0 1))) :=
    (congrArg₂ (fun r t : I => P (fromPath (Path.Homotopic.Quotient.mk (p.subpath r t))))
      (show s 0 = 0 from ht₀) (show s (Fin.last n) = 1 from hn n le_rfl)).mp hconcat
  rw [Path.subpath_zero_one] at hp
  exact (morphismProperty_mk_cast_iff P p p.source p.target).mp hp

/-- The strict inclusion images of the local fundamental groupoids generate all global
arrows under Mathlib's existing multiplicative closure. No faithfulness of the inclusion
functors is asserted or needed. -/
theorem multiplicativeClosure_iSup_strictMap_eq_top_of_isOpenCover (hU : IsOpenCover U) :
    (⨆ i : ι, (⊤ : MorphismProperty (FundamentalGroupoid (U i))).strictMap
      (map (ContinuousMap.subtypeVal (U i : Set X)))).multiplicativeClosure =
        (⊤ : MorphismProperty (FundamentalGroupoid X)) := by
  apply top_unique
  intro x y f _
  apply morphismProperty_of_isOpenCover hU _ ?_ f
  intro i a b g
  apply MorphismProperty.le_multiplicativeClosure
  exact (MorphismProperty.iSup_iff _ _).2 ⟨i, .map trivial⟩

variable {C : Type w} [Category.{w'} C] {F G : FundamentalGroupoid X ⥤ C}

/-- Construct a natural transformation between global functors from objectwise components
that are natural on every inclusion image of an open cover.

The local condition is Mathlib's `naturalityProperty`: for each local arrow, its image
under `F` followed by the target component equals the source component followed by its
image under `G`. The components are global data; no separate overlap compatibility is needed. -/
def natTransOfIsOpenCover (hU : IsOpenCover U)
    (app : ∀ x, F.obj x ⟶ G.obj x)
    (happ : ∀ (i : ι) ⦃x y : FundamentalGroupoid (U i)⦄ (f : x ⟶ y),
      MorphismProperty.naturalityProperty app ((map (ContinuousMap.subtypeVal (U i))).map f)) :
    F ⟶ G where
  app := app
  naturality := by
    intro x y f
    exact morphismProperty_of_isOpenCover hU (MorphismProperty.naturalityProperty app) happ f

/-- The natural transformation constructed from local naturality has the prescribed components. -/
@[simp]
theorem natTransOfIsOpenCover_app (hU : IsOpenCover U)
    (app : ∀ x, F.obj x ⟶ G.obj x)
    (happ : ∀ (i : ι) ⦃x y : FundamentalGroupoid (U i)⦄ (f : x ⟶ y),
      MorphismProperty.naturalityProperty app ((map (ContinuousMap.subtypeVal (U i))).map f))
    (x : FundamentalGroupoid X) :
    (natTransOfIsOpenCover hU app happ).app x = app x := rfl

/-- The prescribed components uniquely determine the natural transformation constructed
from local naturality. -/
theorem natTransOfIsOpenCover_unique (hU : IsOpenCover U)
    (app : ∀ x, F.obj x ⟶ G.obj x)
    (happ : ∀ (i : ι) ⦃x y : FundamentalGroupoid (U i)⦄ (f : x ⟶ y),
      MorphismProperty.naturalityProperty app ((map (ContinuousMap.subtypeVal (U i))).map f))
    (α : F ⟶ G) (hα : ∀ x, α.app x = app x) :
    α = natTransOfIsOpenCover hU app happ := by
  ext x
  simpa only [natTransOfIsOpenCover_app] using hα x

end FundamentalGroupoid
