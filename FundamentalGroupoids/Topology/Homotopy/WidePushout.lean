/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Limits.Products
public import FundamentalGroupoids.Topology.Category.TopCat.Limits.WidePushout
public import Mathlib.Topology.Homotopy.Basic

/-!
# Parametrized continuity and homotopy descent for wide pushouts

A supplied topological colimit has its characteristic continuity property after
product with a parameter space `P`, for maps to `Y`, whenever
`LocallyCompactPair P Y` holds. In particular, local compactness of `P` suffices;
no separation condition on `Y` or local compactness of the diagram is needed.
The parameter, target, diagram and indexing universes are independent.

`TopCat.widePushoutProdDesc` descends compatible jointly continuous families.
Its head and factor equations, uniqueness, fixed-parameter agreement with
`TopCat.widePushoutDesc`, and parameter-precomposition law give its universal
property. `TopCat.widePushoutHomotopy` glues canonical interval homotopies
whose restrictions agree on the attaching space at every time. The common
point need not remain fixed when the attaching space is a point.

Chosen-point-relative homotopies between the restrictions of arbitrary maps
descend uniquely to a homotopy relative to the head, using
`TopCat.widePushoutPointHomotopyRel`. The explicit equality of the endpoint maps
at the head includes the empty-index case. The target universe is independent;
no finiteness, separation, cofibration or nonempty-index hypothesis is imposed.

## References

* The homotopy descent and point-relative interfaces originate in
  `SphereTopology.Topology.WidePushoutHomotopy` and
  `SphereTopology.Topology.WidePushoutPointHomotopy` by Formal Frontier Agents.
* Mathlib's topological-colimit API by Patrick Massot, Kim Morrison, Mario
  Carneiro and Andrew Yang, and its concrete-colimit API, supply finality and
  representatives.
* Reid Barton's compact-open formalization supplies individual-map currying;
  Mathlib's evaluation and locally compact pair APIs supply joint evaluation.
* Shing Tak Lam's homotopy formalization supplies the interval convention and
  the `ContinuousMap.HomotopyLike` interface, as well as relative homotopies.
* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 2, §8,
  p. 19, for the point-wedge setting, not the pair-hypothesis continuity criterion
  or its universe-general descent API.
* The free-path-space transposition used in the homotopy extension property
  motivates putting the parameter inside the continuous mapping space.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe p q y u v w z

namespace TopCat

variable {I : Type v} {B : TopCat.{max u v}} {X : I → TopCat.{max u v}}
  (f : ∀ i, B ⟶ X i)

/-- Joint continuity out of a product with a wide pushout is checked on the
head and every factor. Retaining the head also covers the empty index. -/
theorem continuous_prod_widePushout_iff {P : Type p} {Y : Type y}
    [TopologicalSpace P] [TopologicalSpace Y] [LocallyCompactPair P Y]
    (a : P × (widePushout B X f : TopCat.{max u v}) → Y) :
    Continuous a ↔
      Continuous (fun z : P × B ↦ a (z.1, WidePushout.head f z.2)) ∧
      ∀ i, Continuous (fun z : P × X i ↦ a (z.1, WidePushout.ι f i z.2)) := by
  refine (continuous_prod_iff_of_isColimit
    (colimit.cocone (WidePushoutShape.wideSpan B X f)) (colimit.isColimit _) a).trans ?_
  constructor
  · intro h
    exact ⟨h none, fun i ↦ h (some i)⟩
  · rintro ⟨hB, hX⟩ (_ | i)
    · exact hB
    · exact hX i

/-- Functions on a product with a wide pushout are determined by their values
on the head and every factor, with no topology on the parameter or target. -/
theorem widePushout_prod_funext {P : Type p} {Y : Sort y}
    {a b : P × (widePushout B X f : TopCat.{max u v}) → Y}
    (hB : ∀ t x, a (t, WidePushout.head f x) = b (t, WidePushout.head f x))
    (hX : ∀ i t x, a (t, WidePushout.ι f i x) = b (t, WidePushout.ι f i x)) : a = b := by
  funext ⟨t, x⟩
  exact congrFun (widePushout_funext f
    (g := fun z ↦ a (t, z)) (h := fun z ↦ b (t, z)) (hB t) (fun i ↦ hX i t)) x

section ProductDescent

variable {P : Type p} {Y : Type y} [TopologicalSpace P] [TopologicalSpace Y]
  [LocallyCompactPair P Y]
  (g : C(P × B, Y)) (h : ∀ i, C(P × X i, Y))
  (w : ∀ i t b, h i (t, f i b) = g (t, b))

/-- Descend compatible jointly continuous families through a wide pushout.
The parameter and target universes are independent of the diagram universe. -/
def widePushoutProdDesc : C(P × (widePushout B X f : TopCat.{max u v}), Y) where
  toFun z := widePushoutDesc f (g.curry z.1) (fun i ↦ (h i).curry z.1)
    (fun i b ↦ w i z.1 b) z.2
  continuous_toFun := by
    apply (continuous_prod_widePushout_iff f _).2
    constructor
    · exact g.continuous.congr (fun z ↦
        (widePushoutDesc_head f (g.curry z.1) (fun i ↦ (h i).curry z.1)
          (fun i b ↦ w i z.1 b) z.2).symm)
    · intro i
      exact (h i).continuous.congr (fun z ↦
        (widePushoutDesc_ι f (g.curry z.1) (fun i ↦ (h i).curry z.1)
          (fun i b ↦ w i z.1 b) i z.2).symm)

/-- Product descent restricts to the prescribed family on the head. -/
@[simp] theorem widePushoutProdDesc_head (t : P) (b : B) :
    widePushoutProdDesc f g h w (t, WidePushout.head f b) = g (t, b) :=
  widePushoutDesc_head f (g.curry t) (fun i ↦ (h i).curry t) (fun i b ↦ w i t b) b

/-- Product descent restricts to the prescribed family on every factor. -/
@[simp] theorem widePushoutProdDesc_ι (i : I) (t : P) (x : X i) :
    widePushoutProdDesc f g h w (t, WidePushout.ι f i x) = h i (t, x) :=
  widePushoutDesc_ι f (g.curry t) (fun i ↦ (h i).curry t) (fun i b ↦ w i t b) i x

/-- The head and factor equations uniquely characterize product descent. -/
theorem widePushoutProdDesc_unique
    (a : C(P × (widePushout B X f : TopCat.{max u v}), Y))
    (hB : ∀ t b, a (t, WidePushout.head f b) = g (t, b))
    (hX : ∀ i t x, a (t, WidePushout.ι f i x) = h i (t, x)) :
    a = widePushoutProdDesc f g h w := by
  apply DFunLike.coe_injective
  apply widePushout_prod_funext f
  · intro t b
    exact (hB t b).trans (widePushoutProdDesc_head f g h w t b).symm
  · intro i t x
    exact (hX i t x).trans (widePushoutProdDesc_ι f g h w i t x).symm

/-- At each fixed parameter, product descent is the existing continuous descent
of the head and factor slices. -/
theorem widePushoutProdDesc_curry (t : P) :
    (widePushoutProdDesc f g h w).curry t =
      widePushoutDesc f (g.curry t) (fun i ↦ (h i).curry t) (fun i b ↦ w i t b) := by
  ext x
  rfl

/-- Restricting or reparametrizing a descended family is descent of the
reparametrized head and factor families. -/
theorem widePushoutProdDesc_comp_prodMap {Q : Type q} [TopologicalSpace Q]
    [LocallyCompactPair Q Y] (a : C(Q, P)) :
    (widePushoutProdDesc f g h w).comp (a.prodMap (ContinuousMap.id _)) =
      widePushoutProdDesc f (g.comp (a.prodMap (ContinuousMap.id B)))
        (fun i ↦ (h i).comp (a.prodMap (ContinuousMap.id (X i))))
        (fun i t b ↦ w i (a t) b) := by
  apply widePushoutProdDesc_unique
  · intro t b
    exact widePushoutProdDesc_head f g h w (a t) b
  · intro i t x
    exact widePushoutProdDesc_ι f g h w i (a t) x

end ProductDescent

section Homotopy

variable {Y : Type y} [TopologicalSpace Y]
  {a₀ a₁ : C((widePushout B X f : TopCat.{max u v}), Y)}
  {HB : Type*} [FunLike HB (unitInterval × B) Y]
  [ContinuousMap.HomotopyLike HB (a₀.comp (WidePushout.head f).hom)
    (a₁.comp (WidePushout.head f).hom)]
  {HX : I → Type*} [∀ i, FunLike (HX i) (unitInterval × X i) Y]
  [∀ i, ContinuousMap.HomotopyLike (HX i) (a₀.comp (WidePushout.ι f i).hom)
    (a₁.comp (WidePushout.ι f i).hom)]
  (g : HB) (h : ∀ i, HX i) (w : ∀ i t b, h i (t, f i b) = g (t, b))

/-- Glue homotopies agreeing on the attaching space at every time.
No pointwise fixing or separation hypothesis is imposed. -/
def widePushoutHomotopy : ContinuousMap.Homotopy a₀ a₁ :=
  let d := widePushoutProdDesc f (⟨g, map_continuous g⟩ : C(unitInterval × B, Y))
    (fun i ↦ ⟨h i, map_continuous (h i)⟩) w
  { toContinuousMap := d
    map_zero_left := by
      intro x
      apply congrFun (widePushout_funext f (g := fun x ↦ d (0, x)) (h := a₀) ?_ ?_) x
      · intro b
        exact (widePushoutProdDesc_head f _ _ w 0 b).trans
          (ContinuousMap.HomotopyLike.map_zero_left g b)
      · intro i z
        exact (widePushoutProdDesc_ι f _ _ w i 0 z).trans
          (ContinuousMap.HomotopyLike.map_zero_left (h i) z)
    map_one_left := by
      intro x
      apply congrFun (widePushout_funext f (g := fun x ↦ d (1, x)) (h := a₁) ?_ ?_) x
      · intro b
        exact (widePushoutProdDesc_head f _ _ w 1 b).trans
          (ContinuousMap.HomotopyLike.map_one_left g b)
      · intro i z
        exact (widePushoutProdDesc_ι f _ _ w i 1 z).trans
          (ContinuousMap.HomotopyLike.map_one_left (h i) z) }

/-- Glued homotopies have the prescribed restriction to the head at all times. -/
@[simp] theorem widePushoutHomotopy_head (t : unitInterval) (b : B) :
    widePushoutHomotopy f g h w (t, WidePushout.head f b) = g (t, b) :=
  widePushoutProdDesc_head f (⟨g, map_continuous g⟩ : C(unitInterval × B, Y))
    (fun i ↦ ⟨h i, map_continuous (h i)⟩) w t b

/-- Glued homotopies have the prescribed restriction to every factor at all times. -/
@[simp] theorem widePushoutHomotopy_ι (i : I) (t : unitInterval) (x : X i) :
    widePushoutHomotopy f g h w (t, WidePushout.ι f i x) = h i (t, x) :=
  widePushoutProdDesc_ι f (⟨g, map_continuous g⟩ : C(unitInterval × B, Y))
    (fun i ↦ ⟨h i, map_continuous (h i)⟩) w i t x

/-- The all-time head and factor equations uniquely characterize the glued homotopy. -/
theorem widePushoutHomotopy_unique (H : ContinuousMap.Homotopy a₀ a₁)
    (hB : ∀ t b, H (t, WidePushout.head f b) = g (t, b))
    (hX : ∀ i t x, H (t, WidePushout.ι f i x) = h i (t, x)) :
    H = widePushoutHomotopy f g h w := by
  apply DFunLike.coe_injective
  apply widePushout_prod_funext f
  · intro t b
    exact (hB t b).trans (widePushoutHomotopy_head f g h w t b).symm
  · intro i t x
    exact (hX i t x).trans (widePushoutHomotopy_ι f g h w i t x).symm

end Homotopy

end TopCat

namespace TopCat

variable {J : Type w} {X : J → TopCat.{max u w}} (x : ∀ j, X j)

set_option quotPrecheck false in
local notation "aX" => (fun j : J ↦ (TopCat.const (x j) :
  TopCat.of PUnit ⟶ X j))
set_option quotPrecheck false in
local notation "WX" => (widePushout (TopCat.of PUnit) X aX : TopCat)
set_option quotPrecheck false in
local notation "hx" => (WidePushout.head aX PUnit.unit)

/-- A factor inclusion sends its chosen point to the common head. -/
@[simp] theorem widePushoutPoint_ι_basepoint (j : J) : WidePushout.ι aX j (x j) = hx := by
  calc
    _ = WidePushout.ι aX j (aX j PUnit.unit) :=
      (congrArg (fun z : X j ↦ WidePushout.ι aX j z)
        (TopCat.const_apply (X := TopCat.of PUnit.{max u w + 1}) (x j) PUnit.unit)).symm
    _ = (aX j ≫ WidePushout.ι aX j) PUnit.unit :=
      (TopCat.comp_app (aX j) (WidePushout.ι aX j) PUnit.unit).symm
    _ = hx := congrArg
      (fun k : TopCat.of PUnit.{max u w + 1} ⟶ WX ↦ k PUnit.unit)
      (WidePushout.arrow_ι aX j)

section RelativeHomotopy

/-- Chosen-point-relative factor homotopies descend to a homotopy relative to the
common head. Equality of the endpoint maps at the head is explicit, including
when the index type is empty. -/
def widePushoutPointHomotopyRel
    {J : Type w} {X : J → TopCat.{max u w}} (x : ∀ j, X j)
    {Z : Type z} [TopologicalSpace Z]
    {f g : C((widePushout (TopCat.of PUnit.{max u w + 1}) X
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) : TopCat.{max u w}), Z)}
    (headEq : f (WidePushout.head
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit) =
      g (WidePushout.head
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit))
    (factorHomotopyRel : ∀ j : J, ContinuousMap.HomotopyRel
      (f.comp (WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j).hom)
      (g.comp (WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j).hom) {x j}) :
    ContinuousMap.HomotopyRel f g {WidePushout.head
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit} := by
  let a : ∀ j : J, TopCat.of PUnit.{max u w + 1} ⟶ X j := fun j ↦ TopCat.const (x j)
  let HB : ContinuousMap.Homotopy (f.comp (WidePushout.head a).hom)
      (g.comp (WidePushout.head a).hom) :=
    (ContinuousMap.Homotopy.refl
      (ContinuousMap.const _ (f (WidePushout.head a PUnit.unit)))).cast
      (by ext b; cases b; rfl)
      (by ext b; cases b; exact headEq)
  have h : ∀ j t b, factorHomotopyRel j (t, a j b) = HB (t, b) := by
    intro j t b
    cases b
    change factorHomotopyRel j (t, x j) = f (WidePushout.head a PUnit.unit)
    calc
      _ = f (WidePushout.ι a j (x j)) := (factorHomotopyRel j).eq_fst t (by simp)
      _ = f (WidePushout.head a PUnit.unit) :=
        congrArg f (widePushoutPoint_ι_basepoint x j)
  refine
    { toHomotopy := widePushoutHomotopy a HB (fun j ↦ (factorHomotopyRel j).toHomotopy) h
      prop' := ?_ }
  intro t z hz
  have hz : z = WidePushout.head a PUnit.unit := Set.mem_singleton_iff.mp hz
  subst z
  change widePushoutHomotopy a HB (fun j ↦ (factorHomotopyRel j).toHomotopy) h
    (t, WidePushout.head a PUnit.unit) = f (WidePushout.head a PUnit.unit)
  exact (widePushoutHomotopy_head a HB
    (fun j ↦ (factorHomotopyRel j).toHomotopy) h t PUnit.unit).trans rfl

/-- The descended relative homotopy fixes the common head at every time. -/
@[simp] theorem widePushoutPointHomotopyRel_head
    {J : Type w} {X : J → TopCat.{max u w}} (x : ∀ j, X j)
    {Z : Type z} [TopologicalSpace Z]
    {f g : C((widePushout (TopCat.of PUnit.{max u w + 1}) X
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) : TopCat.{max u w}), Z)}
    (headEq : f (WidePushout.head
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit) =
      g (WidePushout.head
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit))
    (factorHomotopyRel : ∀ j : J, ContinuousMap.HomotopyRel
      (f.comp (WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j).hom)
      (g.comp (WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j).hom) {x j}) (t : unitInterval) :
    widePushoutPointHomotopyRel x headEq factorHomotopyRel
      (t, WidePushout.head
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit) =
      f (WidePushout.head
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit) := by
  exact (widePushoutPointHomotopyRel x headEq factorHomotopyRel).eq_fst t (by simp)

/-- The descended relative homotopy has the prescribed values on every factor. -/
@[simp] theorem widePushoutPointHomotopyRel_ι
    {J : Type w} {X : J → TopCat.{max u w}} (x : ∀ j, X j)
    {Z : Type z} [TopologicalSpace Z]
    {f g : C((widePushout (TopCat.of PUnit.{max u w + 1}) X
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) : TopCat.{max u w}), Z)}
    (headEq : f (WidePushout.head
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit) =
      g (WidePushout.head
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit))
    (factorHomotopyRel : ∀ j : J, ContinuousMap.HomotopyRel
      (f.comp (WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j).hom)
      (g.comp (WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j).hom) {x j})
    (j : J) (t : unitInterval) (a : X j) :
    widePushoutPointHomotopyRel x headEq factorHomotopyRel
      (t, WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j a) =
      factorHomotopyRel j (t, a) := by
  change (widePushoutPointHomotopyRel x headEq factorHomotopyRel).toHomotopy
    (t, WidePushout.ι
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) j a) = _
  dsimp only [widePushoutPointHomotopyRel]
  rw [widePushoutHomotopy_ι]
  rfl

/-- A homotopy relative to the head is determined by its restrictions to all
factors, including when the index type is empty. -/
theorem widePushoutPointHomotopyRel_unique
    {J : Type w} {X : J → TopCat.{max u w}} (x : ∀ j, X j)
    {Z : Type z} [TopologicalSpace Z]
    {f g : C((widePushout (TopCat.of PUnit.{max u w + 1}) X
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) : TopCat.{max u w}), Z)}
    (headEq : f (WidePushout.head
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit) =
      g (WidePushout.head
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit))
    (factorHomotopyRel : ∀ j : J, ContinuousMap.HomotopyRel
      (f.comp (WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j).hom)
      (g.comp (WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j).hom) {x j})
    (K : ContinuousMap.HomotopyRel f g {WidePushout.head
      (fun j : J ↦ (TopCat.const (x j) :
        TopCat.of PUnit.{max u w + 1} ⟶ X j)) PUnit.unit})
    (hK : ∀ (j : J) (t : unitInterval) (a : X j),
      K (t, WidePushout.ι
        (fun j : J ↦ (TopCat.const (x j) :
          TopCat.of PUnit.{max u w + 1} ⟶ X j)) j a) = factorHomotopyRel j (t, a)) :
    K = widePushoutPointHomotopyRel x headEq factorHomotopyRel := by
  apply DFunLike.coe_injective
  apply widePushout_prod_funext
    (fun j : J ↦ (TopCat.const (x j) : TopCat.of PUnit.{max u w + 1} ⟶ X j))
  · intro t b
    cases b
    exact (K.eq_fst t (by simp)).trans
      (widePushoutPointHomotopyRel_head x headEq factorHomotopyRel t).symm
  · intro j t a
    exact (hK j t a).trans
      (widePushoutPointHomotopyRel_ι x headEq factorHomotopyRel j t a).symm

end RelativeHomotopy

end TopCat
