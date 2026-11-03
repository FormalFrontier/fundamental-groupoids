/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.CategoryTheory.Category.Pointed.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Exactness of short complexes of pointed types

A short complex of pointed types is exact precisely when the image of its first
map is the fibre of its second map over the distinguished point. The reverse
implication constructs compatible left and right homology data using the
point-fibre kernels and quotient cokernels.

## References

The homology-data framework is due to Joël Riou in
`Mathlib.Algebra.Homology.ShortComplex.Exact`. The concrete constructions in
`FundamentalGroupoids.CategoryTheory.Category.Pointed.Limits` use Yaël Dillies's
formalization of pointed types, Kim Morrison and Markus Himmel's kernel and
cokernel API, and Christian Merten's function coequalizer API in Mathlib.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Pointed

private theorem isZero_cokernelObj_of_surjective {X Y : Pointed.{u}} (f : X ⟶ Y)
    (hf : Function.Surjective f) : IsZero (cokernelObj f) := by
  apply (isZero_iff_subsingleton _).2
  have hpoint : ∀ q : cokernelObj f, q = (cokernelObj f).point := by
    intro q
    obtain ⟨y, rfl⟩ := cokernelπ_surjective f q
    exact (cokernelπ_eq_point_iff f y).2 (hf y)
  exact ⟨fun q r => (hpoint q).trans (hpoint r).symm⟩

private theorem exact_of_range_eq_preimage (S : ShortComplex Pointed.{u})
    (hset : Set.range (fun x : S.X₁ => S.f x) =
      (fun y : S.X₂ => S.g y) ⁻¹' ({S.X₃.point} : Set S.X₃)) : S.Exact := by
  let f' : S.X₁ ⟶ pointFibre S.g :=
    (pointFibreIsLimit S.g).lift (KernelFork.ofι S.f S.zero)
  have hf' : f' ≫ pointFibreι S.g = S.f :=
    (KernelFork.IsLimit.lift' (pointFibreIsLimit S.g) S.f S.zero).property
  let g' : cokernelObj S.f ⟶ S.X₃ :=
    (cokernelIsColimit S.f).desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : cokernelπ S.f ≫ g' = S.g :=
    (CokernelCofork.IsColimit.desc' (cokernelIsColimit S.f) S.g S.zero).property
  let left : S.LeftHomologyData :=
    { K := pointFibre S.g
      H := cokernelObj f'
      i := pointFibreι S.g
      π := cokernelπ f'
      wi := pointFibreι_comp S.g
      hi := pointFibreIsLimit S.g
      wπ := comp_cokernelπ f'
      hπ := cokernelIsColimit f' }
  let right : S.RightHomologyData :=
    { Q := cokernelObj S.f
      H := pointFibre g'
      p := cokernelπ S.f
      ι := pointFibreι g'
      wp := comp_cokernelπ S.f
      hp := cokernelIsColimit S.f
      wι := pointFibreι_comp g'
      hι := pointFibreIsLimit g' }
  have hcycles : ∀ y : pointFibre S.g,
      pointFibreι S.g y ∈ Set.range (fun x : S.X₁ => S.f x) := by
    intro y
    rw [hset]
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, pointFibreι_apply] using y.property
  have hf'_surjective : Function.Surjective f' := by
    intro y
    obtain ⟨a, ha⟩ := hcycles y
    refine ⟨a, ?_⟩
    apply pointFibre_ext
    calc
      pointFibreι S.g (f' a) = S.f a := by
        simpa only [CategoryTheory.comp_apply] using
          congrArg (fun k : S.X₁ ⟶ S.X₂ => k a) hf'
      _ = pointFibreι S.g y := ha
  have hleft : IsZero left.H := isZero_cokernelObj_of_surjective f' hf'_surjective
  -- A zero of the descended map has a representative that is already in the image of `f`.
  have hright_point : ∀ z : pointFibre g', z = (pointFibre g').point := by
    intro z
    apply pointFibre_ext
    obtain ⟨b, hb⟩ := cokernelπ_surjective S.f (pointFibreι g' z)
    have hgb : S.g b = S.X₃.point := by
      calc
        S.g b = g' (cokernelπ S.f b) := by
          simpa only [CategoryTheory.comp_apply] using
            (congrArg (fun k : S.X₂ ⟶ S.X₃ => k b) hg').symm
        _ = g' (pointFibreι g' z) := congrArg g' hb
        _ = S.X₃.point := z.property
    have hb_range : b ∈ Set.range (fun a : S.X₁ => S.f a) := by
      rw [hset]
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hgb
    calc
      pointFibreι g' z = cokernelπ S.f b := hb.symm
      _ = (cokernelObj S.f).point := (cokernelπ_eq_point_iff S.f b).2 hb_range
      _ = pointFibreι g' (pointFibre g').point := (pointFibreι g').map_point.symm
  have hright : IsZero right.H :=
    (isZero_iff_subsingleton (pointFibre g')).2
      ⟨fun z w => (hright_point z).trans (hright_point w).symm⟩
  let e : left.H ≅ right.H := hleft.iso hright
  have hip : pointFibreι S.g ≫ cokernelπ S.f = 0 := by
    apply (comp_eq_zero_iff _ _).2
    intro y
    exact (cokernelπ_eq_point_iff S.f _).2 (hcycles y)
  refine ⟨⟨{ left := left, right := right, iso := e, comm := ?_ }, hleft⟩⟩
  have hπ : left.π = 0 := hleft.eq_of_tgt _ _
  calc
    left.π ≫ e.hom ≫ right.ι = 0 := by simp only [hπ, zero_comp]
    _ = left.i ≫ right.p := hip.symm

/-- A short complex of pointed types is exact if and only if the image of its first map
is the fibre of its second map over the distinguished point. -/
theorem exact_iff_range_eq_preimage (S : ShortComplex Pointed.{u}) :
    S.Exact ↔ Set.range (fun x : S.X₁ => S.f x) =
      (fun y : S.X₂ => S.g y) ⁻¹' ({S.X₃.point} : Set S.X₃) := by
  constructor
  · intro h
    have hzero : pointFibreι S.g ≫ cokernelπ S.f = 0 :=
      h.comp_eq_zero (pointFibreι_comp S.g) (comp_cokernelπ S.f)
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
        (comp_eq_zero_iff S.f S.g).1 S.zero x
    · intro y hy
      have hy' : S.g y = S.X₃.point := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hy
      have hz := (comp_eq_zero_iff (pointFibreι S.g) (cokernelπ S.f)).1 hzero
        (⟨y, hy'⟩ : pointFibre S.g)
      exact (cokernelπ_eq_point_iff S.f y).1 hz
  · exact exact_of_range_eq_preimage S

end Pointed
