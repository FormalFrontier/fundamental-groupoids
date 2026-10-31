/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenNhds
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.Topology.Sets.OpenCover
import Mathlib.CategoryTheory.Limits.Types.ColimitType
import FundamentalGroupoids.Topology.Path

/-!
# Fundamental groups of directed open covers

For an inclusion-directed open cover by neighborhoods of a supplied basepoint, the
ambient fundamental group has the universal property of the colimit of the local
fundamental groups. The diagram and cocone are the existing `openNhdsFunctor` and
`openNhdsCocone`, restricted along `CategoryTheory.inducedFunctor U`. Every index is
retained, including distinct indices presenting the same open neighborhood, and all
transition maps are induced by the corresponding subspace inclusions.

The homomorphism universal property permits any target monoid in a universe independent
of the space and index universes. The categorical form concerns the inclusion cocone
in `GrpCat` in the space universe; it imposes no smallness hypothesis on the index type.

## Implementation notes

No path connectedness of the members or ambient space, intersection closure,
separation, local connectivity, finiteness or dimension hypothesis is required.
Nonemptiness of the index type follows by applying the covering hypothesis to the
supplied basepoint and is not a separate assumption. Compactness puts each loop and
each based homotopy in one chart. These stage-surjectivity and eventual-equality
statements recognize the ambient group as Mathlib's heterogeneous type colimit.
Its descent map preserves multiplication by putting two inputs in a common chart;
this uses the existing group operations and works for any target monoid.

## References

* Mathlib's `IsCompact.elim_directed_cover` in
  `Mathlib.Topology.Compactness.Compact` gives containment of a compact set in one
  member of an indexed directed open cover.
* Joël Riou's `Functor.CoconeTypes` and its descent and representative APIs in
  `Mathlib.CategoryTheory.Limits.Types.ColimitType` supply the independent-universe
  type-colimit universal property.
* `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.OpenNhds` supplies the
  neighborhood functor, inclusion-induced maps and inclusion cocone.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 2, §7,
  printed pp. 18–19, uses compact loop and homotopy images in the finite-stage
  colimit step of the van Kampen proof. The directed-cover formulation here
  isolates that step without path-connectedness or intersection closure and
  permits arbitrary target monoids.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace FundamentalGroup

variable {X : Type u} [TopologicalSpace X] {I : Type v}

-- Keep the existing maps, with their entire monoid-hom types expressed using
-- the canonical fundamental groups rather than opaque bundled carriers.
private noncomputable def inclusionHom (p : X) (V : OpenNhds (X := TopCat.of X) p) :
    FundamentalGroup V.1 ⟨p, V.2⟩ →* FundamentalGroup X p :=
  ((openNhdsCocone p).ι.app V).hom

private theorem inclusionHom_mk (p : X) (V : OpenNhds (X := TopCat.of X) p)
    (γ : Path (⟨p, V.2⟩ : V.1) ⟨p, V.2⟩) :
    inclusionHom p V (Path.Homotopic.Quotient.mk γ) =
      Path.Homotopic.Quotient.mk (γ.map continuous_subtype_val) := rfl

private noncomputable def transitionHom (p : X)
    {V W : OpenNhds (X := TopCat.of X) p} (hVW : V ≤ W) :
    FundamentalGroup V.1 ⟨p, V.2⟩ →* FundamentalGroup W.1 ⟨p, W.2⟩ :=
  ((openNhdsFunctor p).map (homOfLE hVW)).hom

private theorem transitionHom_mk (p : X)
    {V W : OpenNhds (X := TopCat.of X) p} (hVW : V ≤ W)
    (γ : Path (⟨p, V.2⟩ : V.1) ⟨p, V.2⟩) :
    transitionHom p hVW (Path.Homotopic.Quotient.mk γ) =
      Path.Homotopic.Quotient.mk
        (γ.map (ContinuousMap.inclusion
          (s := (V.1 : Set X)) (t := (W.1 : Set X)) hVW).continuous) := rfl

-- The index type is inhabited because the supplied basepoint belongs to the cover.
private theorem exists_range_subset (p : X) (U : I → OpenNhds (X := TopCat.of X) p)
    (hcover : IsOpenCover (fun i => (U i).1)) (hdir : Directed (· ≤ ·) U)
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (f : C(K, X)) :
    ∃ i, Set.range f ⊆ (U i).1 := by
  classical
  obtain ⟨i, _⟩ := hcover.exists_mem p
  let : Nonempty I := ⟨i⟩
  refine (isCompact_range f.continuous).elim_directed_cover
    (fun i => ((U i).1 : Set X)) (fun i => (U i).1.isOpen) ?_ ?_
  · rw [hcover.iSup_set_eq_univ]
    exact Set.subset_univ _
  · intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, hik, hjk⟩

-- A loop, unlike a general path in an arbitrary cover, needs no subdivision here.
private theorem exists_stage (p : X) (U : I → OpenNhds (X := TopCat.of X) p)
    (hcover : IsOpenCover (fun i => (U i).1)) (hdir : Directed (· ≤ ·) U)
    (γ : FundamentalGroup X p) :
    ∃ (i : I) (δ : FundamentalGroup (U i).1 ⟨p, (U i).2⟩),
      inclusionHom p (U i) δ = γ := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    obtain ⟨i, hi⟩ := exists_range_subset p U hcover hdir γ.toContinuousMap
    refine ⟨i, Path.Homotopic.Quotient.mk (γ.codRestrict hi), ?_⟩
    rw [inclusionHom_mk, Path.codRestrict_map_subtypeVal]

-- Compactness is used on the whole based square, not on an unbased homotopy.
-- The common stage also receives the two original stages, so its transition maps
-- are precisely the inclusion-induced maps of the neighborhood functor.
private theorem exists_stage_eq (p : X) (U : I → OpenNhds (X := TopCat.of X) p)
    (hcover : IsOpenCover (fun i => (U i).1)) (hdir : Directed (· ≤ ·) U)
    (i j : I) (γ : FundamentalGroup (U i).1 ⟨p, (U i).2⟩)
    (δ : FundamentalGroup (U j).1 ⟨p, (U j).2⟩)
    (h : inclusionHom p (U i) γ = inclusionHom p (U j) δ) :
    ∃ (k : I) (hik : U i ≤ U k) (hjk : U j ≤ U k),
      transitionHom p hik γ = transitionHom p hjk δ := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    induction δ using Path.Homotopic.Quotient.ind with
    | mk δ =>
      have hambient : (γ.map continuous_subtype_val).Homotopic
          (δ.map continuous_subtype_val) := by
        apply Path.Homotopic.Quotient.eq.mp
        rw [inclusionHom_mk, inclusionHom_mk] at h
        exact h
      obtain ⟨H⟩ := hambient
      obtain ⟨l, hl⟩ := exists_range_subset p U hcover hdir H.toContinuousMap
      obtain ⟨m, him, hjm⟩ := hdir i j
      obtain ⟨k, hmk, hlk⟩ := hdir m l
      let hik : U i ≤ U k := him.trans hmk
      let hjk : U j ≤ U k := hjm.trans hmk
      let γk : Path (⟨p, (U k).2⟩ : (U k).1) ⟨p, (U k).2⟩ :=
        γ.map (ContinuousMap.inclusion
          (s := ((U i).1 : Set X)) (t := ((U k).1 : Set X)) hik).continuous
      let δk : Path (⟨p, (U k).2⟩ : (U k).1) ⟨p, (U k).2⟩ :=
        δ.map (ContinuousMap.inclusion
          (s := ((U j).1 : Set X)) (t := ((U k).1 : Set X)) hjk).continuous
      have hγk : γk.map continuous_subtype_val = γ.map continuous_subtype_val := by
        ext t
        rfl
      have hδk : δk.map continuous_subtype_val = δ.map continuous_subtype_val := by
        ext t
        rfl
      have hlocal : γk.Homotopic δk :=
        Path.Homotopic.of_subtypeVal (H.cast hγk.symm hδk.symm)
          (fun x hx => hlk (hl hx))
      refine ⟨k, hik, hjk, ?_⟩
      rw [transitionHom_mk, transitionHom_mk]
      exact Path.Homotopic.Quotient.eq.mpr hlocal

/-- Compatible homomorphisms from the fundamental groups of an inclusion-directed
open cover by neighborhoods of `p` extend uniquely to the ambient fundamental group.

Compatibility is required along every inclusion of presented neighborhoods, including
inclusions between repeated presentations. Neither the neighborhoods nor the ambient
space need be path connected, and the range need not be closed under intersections.
The target may be any monoid, in a universe independent of the space and index universes.
This generalizes the compact finite-stage colimit step in May, Chapter 2, §7,
printed p. 19. -/
theorem existsUnique_hom_of_isOpenCover_of_directed
    (p : X) (U : I → OpenNhds (X := TopCat.of X) p)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hdir : Directed (· ≤ ·) U)
    (G : Type w) [Monoid G]
    (φ : ∀ i, FundamentalGroup (U i).1 ⟨p, (U i).2⟩ →* G)
    (hφ : ∀ (i j : I) (hij : U i ≤ U j),
      (φ j).comp (((openNhdsFunctor p).map (homOfLE hij)).hom) = φ i) :
    ∃! ψ : FundamentalGroup X p →* G,
      ∀ i, ψ.comp (((openNhdsCocone p).ι.app (U i)).hom) = φ i := by
  classical
  -- Fix the unbundled source and target groups so the monoid laws below use
  -- their canonical instances rather than opaque bundled carriers.
  let ι (i : I) : FundamentalGroup (U i).1 ⟨p, (U i).2⟩ →* FundamentalGroup X p :=
    inclusionHom p (U i)
  let F := inducedFunctor U ⋙ openNhdsFunctor p ⋙ forget GrpCat
  -- Use the existing heterogeneous-universe colimit of types. Its point is the
  -- ambient fundamental group, and its legs are the given inclusion maps.
  let c : F.CoconeTypes :=
    { pt := FundamentalGroup X p
      ι i := ι i
      ι_naturality f := by
        funext x
        exact ConcreteCategory.congr_hom ((openNhdsCocone p).w f.hom) x }
  have hc : c.IsColimit := by
    refine ⟨⟨?_, (c.descColimitType_surjective_iff).mpr ?_⟩⟩
    · intro x y hxy
      obtain ⟨i, xi, rfl⟩ := F.ιColimitType_jointly_surjective x
      obtain ⟨j, xj, rfl⟩ := F.ιColimitType_jointly_surjective y
      obtain ⟨k, hik, hjk, hk⟩ := exists_stage_eq p U hcover hdir i j xi xj hxy
      exact F.ιColimitType_eq_of_map_eq_map xi xj
        (InducedCategory.homMk (homOfLE hik))
        (InducedCategory.homMk (homOfLE hjk)) hk
    · exact exists_stage p U hcover hdir
  let t : F.CoconeTypes :=
    { pt := G
      ι i := φ i
      ι_naturality f := by
        funext x
        exact DFunLike.congr_fun (hφ _ _ f.hom.le) x }
  let f : FundamentalGroup X p → G := hc.desc t
  have hf (i : I) (x : FundamentalGroup (U i).1 ⟨p, (U i).2⟩) :
      f (ι i x) = φ i x :=
    hc.fac_apply t i x
  have hw (i j : I) (hij : U i ≤ U j)
      (x : FundamentalGroup (U i).1 ⟨p, (U i).2⟩) :
      ι j (transitionHom p hij x) = ι i x :=
    ConcreteCategory.congr_hom ((openNhdsCocone p).w (homOfLE hij)) x
  have hf_one : f 1 = 1 := by
    obtain ⟨i, _⟩ := hcover.exists_mem p
    calc
      f 1 = f (ι i 1) := congrArg f (ι i).map_one.symm
      _ = φ i 1 := hf i 1
      _ = 1 := (φ i).map_one
  have hf_mul (x y : FundamentalGroup X p) : f (x * y) = f x * f y := by
    obtain ⟨i, xi, rfl⟩ := exists_stage p U hcover hdir x
    obtain ⟨j, xj, rfl⟩ := exists_stage p U hcover hdir y
    change f (ι i xi * ι j xj) = f (ι i xi) * f (ι j xj)
    obtain ⟨k, hik, hjk⟩ := hdir i j
    let xi' : FundamentalGroup (U k).1 ⟨p, (U k).2⟩ :=
      transitionHom p hik xi
    let xj' : FundamentalGroup (U k).1 ⟨p, (U k).2⟩ :=
      transitionHom p hjk xj
    calc
      _ = f (ι k (xi' * xj')) := by
        rw [(ι k).map_mul, hw i k hik xi, hw j k hjk xj]
      _ = φ k (xi' * xj') := hf k _
      _ = φ k xi' * φ k xj' := (φ k).map_mul _ _
      _ = _ := by
        rw [← hf k xi', ← hf k xj', hw i k hik xi, hw j k hjk xj]
  let ψ : FundamentalGroup X p →* G :=
    { toFun := f
      map_one' := hf_one
      map_mul' := hf_mul }
  refine ⟨ψ, ?_, ?_⟩
  · intro i
    exact MonoidHom.ext (hf i)
  · intro ψ' hψ'
    apply MonoidHom.ext
    intro x
    obtain ⟨i, xi, rfl⟩ := exists_stage p U hcover hdir x
    exact (DFunLike.congr_fun (hψ' i) xi).trans (hf i xi).symm

/-- The inclusion cocone of an inclusion-directed open cover by neighborhoods of `p`
is a colimit in `GrpCat` in the space universe.

The diagram is the restriction of `openNhdsFunctor p` along the induced inclusion
category on the supplied index type. It retains repeated neighborhoods and requires
neither path connectedness nor intersection closure. The independent-target
homomorphism form is `existsUnique_hom_of_isOpenCover_of_directed`. -/
noncomputable def isColimitOfIsOpenCoverOfDirected
    (p : X) (U : I → OpenNhds (X := TopCat.of X) p)
    (hcover : IsOpenCover (fun i => (U i).1))
    (hdir : Directed (· ≤ ·) U) :
    IsColimit ((openNhdsCocone p).whisker (inducedFunctor U)) := by
  classical
  apply IsColimit.ofExistsUnique
  intro s
  have hs (i j : I) (hij : U i ≤ U j) :
      (s.ι.app j).hom.comp (((openNhdsFunctor p).map (homOfLE hij)).hom) =
        (s.ι.app i).hom :=
    congrArg GrpCat.Hom.hom (s.w (InducedCategory.homMk (homOfLE hij)))
  obtain ⟨ψ, hψ, huniq⟩ := existsUnique_hom_of_isOpenCover_of_directed
    p U hcover hdir s.pt (fun i => (s.ι.app i).hom) hs
  refine ⟨GrpCat.ofHom ψ, ?_, ?_⟩
  · intro i
    exact GrpCat.hom_ext (hψ i)
  · intro m hm
    apply GrpCat.hom_ext
    exact huniq m.hom (fun i => congrArg GrpCat.Hom.hom (hm i))

end FundamentalGroup
