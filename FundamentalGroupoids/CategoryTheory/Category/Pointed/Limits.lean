/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.CategoryTheory.Category.Pointed
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.Logic.Function.Coequalizer

/-!
# Kernels and cokernels of pointed maps

Kernels are fibres over the distinguished point. Cokernels are function
coequalizers that identify the image with the distinguished point. Their lift and
descent maps give the limiting and colimiting universal properties. The cokernel
projection is surjective, and its point fibre is the image of the original map.

## References

The pointed-type construction follows Yaël Dillies's formalization in
`Mathlib.CategoryTheory.Category.Pointed`. The kernel and cokernel constructions
use Kim Morrison and Markus Himmel's universal-property API in
`Mathlib.CategoryTheory.Limits.Shapes.Kernels`. The quotient and its eliminator
use Christian Merten's formalization in `Mathlib.Logic.Function.Coequalizer`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Pointed

/-- The fibre of a pointed map over the target's distinguished point. -/
def pointFibre {X Y : Pointed.{u}} (g : X ⟶ Y) : Pointed.{u} :=
  Pointed.of (⟨X.point, g.map_point⟩ : { x : X // g x = Y.point })

/-- The inclusion of the point fibre into the source. -/
def pointFibreι {X Y : Pointed.{u}} (g : X ⟶ Y) : pointFibre g ⟶ X where
  toFun := Subtype.val
  map_point := rfl

/-- The point-fibre inclusion returns the underlying element. -/
@[simp]
theorem pointFibreι_apply {X Y : Pointed.{u}} (g : X ⟶ Y) (x : pointFibre g) :
    pointFibreι g x = x.val := rfl

/-- Elements of the point fibre are determined by their images in the source. -/
@[ext]
theorem pointFibre_ext {X Y : Pointed.{u}} {g : X ⟶ Y} {x y : pointFibre g}
    (h : pointFibreι g x = pointFibreι g y) : x = y :=
  Subtype.ext h

/-- The composite of the point-fibre inclusion with the map is zero. -/
@[simp]
theorem pointFibreι_comp {X Y : Pointed.{u}} (g : X ⟶ Y) :
    pointFibreι g ≫ g = 0 :=
  (Pointed.comp_eq_zero_iff (pointFibreι g) g).2 (fun x => x.property)

/-- The kernel fork given by the point-fibre inclusion. -/
def pointFibreFork {X Y : Pointed.{u}} (g : X ⟶ Y) : KernelFork g :=
  KernelFork.ofι (pointFibreι g) (pointFibreι_comp g)

/-- The arrow of the point-fibre fork is the subtype inclusion. -/
@[simp]
theorem pointFibreFork_ι {X Y : Pointed.{u}} (g : X ⟶ Y) :
    (pointFibreFork g).ι = pointFibreι g := rfl

/-- A map with zero composite lifts to the point fibre by retaining its values. -/
def pointFibreLift {X Y T : Pointed.{u}} (g : X ⟶ Y) (t : T ⟶ X)
    (ht : t ≫ g = 0) : T ⟶ pointFibre g where
  toFun z := ⟨t z, (Pointed.comp_eq_zero_iff t g).1 ht z⟩
  map_point := Subtype.ext t.map_point

/-- The underlying value of the point-fibre lift is the original map's value. -/
@[simp]
theorem pointFibreLift_apply {X Y T : Pointed.{u}} (g : X ⟶ Y) (t : T ⟶ X)
    (ht : t ≫ g = 0) (z : T) :
    (pointFibreLift g t ht z).val = t z := rfl

/-- The point-fibre lift factors the original map through the inclusion. -/
@[simp]
theorem pointFibreLift_comp_ι {X Y T : Pointed.{u}} (g : X ⟶ Y) (t : T ⟶ X)
    (ht : t ≫ g = 0) : pointFibreLift g t ht ≫ pointFibreι g = t := by
  apply Pointed.Hom.ext
  funext z
  exact pointFibreLift_apply g t ht z

/-- A map into the point fibre is uniquely determined by its composite with the inclusion. -/
theorem pointFibreLift_unique {X Y T : Pointed.{u}} (g : X ⟶ Y) (t : T ⟶ X)
    (ht : t ≫ g = 0) (m : T ⟶ pointFibre g) (hm : m ≫ pointFibreι g = t) :
    m = pointFibreLift g t ht := by
  apply Pointed.Hom.ext
  funext z
  apply pointFibre_ext
  exact congrArg (fun k : T ⟶ X => k z) hm

/-- The point-fibre fork is a limiting kernel fork. -/
def pointFibreIsLimit {X Y : Pointed.{u}} (g : X ⟶ Y) : IsLimit (pointFibreFork g) :=
  KernelFork.IsLimit.ofι (pointFibreι g) (pointFibreι_comp g)
    (fun {_} t ht => pointFibreLift g t ht)
    (fun {_} t ht => pointFibreLift_comp_ι g t ht)
    (fun {_} t ht m hm => pointFibreLift_unique g t ht m hm)

/-- Every pointed map has a kernel, given by its point fibre. -/
instance hasKernels : HasKernels Pointed.{u} where
  has_limit g := HasLimit.mk ⟨pointFibreFork g, pointFibreIsLimit g⟩

end Pointed

namespace Pointed

variable {X Y Z : Pointed.{u}}

/-- The cokernel quotient, pointed by the class of the target's distinguished point. -/
def cokernelObj (f : X ⟶ Y) : Pointed.{u} :=
  Pointed.of
    (Function.Coequalizer.mk (fun x : X => f x) (fun _ : X => Y.point) Y.point)

/-- The carrier of the pointed cokernel is a function coequalizer. -/
theorem coe_cokernelObj (f : X ⟶ Y) :
    ↥(cokernelObj f) = Function.Coequalizer (fun x : X => f x) (fun _ : X => Y.point) :=
  rfl

/-- The distinguished point of the cokernel is the class of the target's point. -/
theorem cokernelObj_point (f : X ⟶ Y) :
    (cokernelObj f).point =
      Function.Coequalizer.mk (fun x : X => f x) (fun _ : X => Y.point) Y.point :=
  rfl

/-- The projection from the target of a pointed map to its cokernel quotient. -/
def cokernelπ (f : X ⟶ Y) : Y ⟶ cokernelObj f where
  toFun := Function.Coequalizer.mk (fun x : X => f x) (fun _ : X => Y.point)
  map_point := rfl

/-- The cokernel projection sends an element to its coequalizer class. -/
theorem cokernelπ_apply (f : X ⟶ Y) (y : Y) :
    cokernelπ f y =
      Function.Coequalizer.mk (fun x : X => f x) (fun _ : X => Y.point) y :=
  rfl

/-- Every element of the pointed cokernel has a representative in the target. -/
theorem cokernelπ_surjective (f : X ⟶ Y) : Function.Surjective (cokernelπ f) :=
  Function.Coequalizer.mk_surjective _ _

/-- A pointed map followed by its cokernel projection is zero. -/
@[reassoc (attr := simp)]
theorem comp_cokernelπ (f : X ⟶ Y) : f ≫ cokernelπ f = 0 := by
  apply (comp_eq_zero_iff f (cokernelπ f)).2
  intro x
  exact Function.Coequalizer.condition (fun x : X => f x) (fun _ : X => Y.point) x

/-- The cofork given by the pointed cokernel projection. -/
def cokernelCofork (f : X ⟶ Y) : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)

/-- The projection of the cokernel cofork is the quotient projection. -/
@[simp]
theorem cokernelCofork_π (f : X ⟶ Y) : (cokernelCofork f).π = cokernelπ f :=
  rfl

/-- A pointed map vanishing on `f` descends to the cokernel quotient. -/
def cokernelDesc (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) : cokernelObj f ⟶ Z where
  toFun := Function.Coequalizer.desc (fun x : X => f x) (fun _ : X => Y.point) g
    (funext fun x => ((comp_eq_zero_iff f g).1 h x).trans g.map_point.symm)
  map_point := g.map_point

/-- Descent along the cokernel projection evaluates on representatives. -/
@[simp]
theorem cokernelDesc_apply (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) (y : Y) :
    cokernelDesc f g h (cokernelπ f y) = g y :=
  Function.Coequalizer.desc_mk (fun x : X => f x) (fun _ : X => Y.point) g
    (funext fun x => ((comp_eq_zero_iff f g).1 h x).trans g.map_point.symm) y

/-- The descended pointed map factors the original map through the projection. -/
@[reassoc (attr := simp)]
theorem cokernelπ_desc (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0) :
    cokernelπ f ≫ cokernelDesc f g h = g := by
  apply Pointed.Hom.ext
  funext y
  exact cokernelDesc_apply f g h y

/-- A pointed map out of the cokernel is determined by its composite with the projection. -/
theorem cokernelDesc_unique (f : X ⟶ Y) (g : Y ⟶ Z) (h : f ≫ g = 0)
    (k : cokernelObj f ⟶ Z) (hk : cokernelπ f ≫ k = g) : k = cokernelDesc f g h := by
  apply Pointed.Hom.ext
  funext q
  obtain ⟨y, rfl⟩ := cokernelπ_surjective f q
  exact (congrArg (fun a : Y ⟶ Z => a y) hk).trans (cokernelDesc_apply f g h y).symm

/-- The pointed cokernel cofork satisfies the colimit universal property. -/
def cokernelIsColimit (f : X ⟶ Y) : IsColimit (cokernelCofork f) :=
  CokernelCofork.IsColimit.ofπ (cokernelπ f) (comp_cokernelπ f)
    (fun {_} g h => cokernelDesc f g h)
    (fun {_} g h => cokernelπ_desc f g h)
    (fun {_} g h k hk => cokernelDesc_unique f g h k hk)

/-- A class is the distinguished point exactly when its representative is in the image. -/
theorem cokernelπ_eq_point_iff (f : X ⟶ Y) (y : Y) :
    cokernelπ f y = (cokernelObj f).point ↔ y ∈ Set.range (fun x : X => f x) := by
  constructor
  · intro hy
    classical
    -- A pointed Boolean-valued map separates the image from its complement.
    let T : Pointed.{u} := Pointed.of (ULift.up false : ULift.{u} Bool)
    have hpoint : Y.point ∈ Set.range (fun x : X => f x) := ⟨X.point, f.map_point⟩
    let g : Y ⟶ T :=
      { toFun := fun z =>
          if z ∈ Set.range (fun x : X => f x) then ULift.up false else ULift.up true
        map_point := by
          change (if Y.point ∈ Set.range (fun x : X => f x) then
            (ULift.up false : ULift.{u} Bool) else ULift.up true) = ULift.up false
          exact ite_eq_left hpoint }
    have hg : f ≫ g = 0 := by
      apply (comp_eq_zero_iff f g).2
      intro x
      change (if f x ∈ Set.range (fun x : X => f x) then
        (ULift.up false : ULift.{u} Bool) else ULift.up true) = ULift.up false
      exact ite_eq_left ⟨x, rfl⟩
    have hvalue : g y = T.point := by
      calc
        g y = cokernelDesc f g hg (cokernelπ f y) := (cokernelDesc_apply f g hg y).symm
        _ = cokernelDesc f g hg (cokernelObj f).point := congrArg (cokernelDesc f g hg) hy
        _ = T.point := (cokernelDesc f g hg).map_point
    by_contra hmem
    change (if y ∈ Set.range (fun x : X => f x) then
      (ULift.up false : ULift.{u} Bool) else ULift.up true) = ULift.up false at hvalue
    rw [ite_eq_right hmem] at hvalue
    have hbool : (true : Bool) = false := congrArg ULift.down hvalue
    cases hbool
  · rintro ⟨x, rfl⟩
    exact (comp_eq_zero_iff f (cokernelπ f)).1 (comp_cokernelπ f) x

/-- The category of pointed types has cokernels. -/
instance hasCokernels : HasCokernels Pointed.{u} where
  has_colimit f :=
    { exists_colimit :=
        ⟨{ cocone := cokernelCofork f, isColimit := cokernelIsColimit f }⟩ }

end Pointed
