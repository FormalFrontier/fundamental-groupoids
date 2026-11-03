/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based.Universe
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Loop
public import FundamentalGroupoids.Topology.Path
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Based homotopy fibers and lifted sequence maps

The homotopy fiber retains paths from the chosen target point to the image of
its point coordinate. For an arrow of based spaces in a common universe,
`BasedTopCat.homotopyFiberFunctor` selects this original homotopy fiber over the
target basepoint, based at the source basepoint and the constant path. Strict
based squares act on its point coordinate and postcompose its whole forward
path. `BasedTopCat.homotopyFiberProjection` projects naturally to the arrow's
original source based space.

Its projection and whole-forward-loop inclusion also become based maps after
ordinary universe lifting of spaces in independent universes. The map on based
loops is pointwise application of the original continuous map, with endpoint
casts determined by its basepoint equation. These lifted constructions use the
original homotopy fiber and path spaces; no identification with a homotopy fiber
or loop space of lifted maps is used.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, §6, p. 61,
  for the path direction of the ordinary homotopy fiber used by
  `ContinuousMap.HomotopyFiber`.
* Mathlib's `CategoryTheory.Arrow` and `CategoryTheory.Under` supply strict
  commutative squares and the under-category structure of based spaces. The
  geometry and continuity of the fiber maps come from
  `ContinuousMap.HomotopyFiber.map`.
-/

@[expose] public section

open CategoryTheory


namespace BasedTopCat

section Functor

universe u

/-- The ordinary homotopy fiber over the target basepoint, functorial in strict based squares.
Its selected point is the source basepoint together with the constant target path. -/
def homotopyFiberFunctor : Arrow BasedTopCat.{u} ⥤ BasedTopCat.{u} where
  obj f :=
    BasedTopCat.of
      (ContinuousMap.HomotopyFiber f.hom.right.hom (BasedTopCat.point f.right))
      (ContinuousMap.HomotopyFiber.const
        (f := f.hom.right.hom) (b := BasedTopCat.point f.right)
        (BasedTopCat.point f.left) (BasedTopCat.map_point f.hom))
  map {f g} sq :=
    let w : ∀ e : f.left.right,
        g.hom.right.hom (sq.left.right.hom e) =
          sq.right.right.hom (f.hom.right.hom e) :=
      fun e => congrArg (fun k : f.left ⟶ g.right => k.right.hom e) (Arrow.w sq)
    BasedTopCat.ofHom
      (ContinuousMap.HomotopyFiber.map
        (f := f.hom.right.hom) (f' := g.hom.right.hom)
        (b := BasedTopCat.point f.right) (b' := BasedTopCat.point g.right)
        sq.left.right.hom sq.right.right.hom w (BasedTopCat.map_point sq.right))
      (ContinuousMap.HomotopyFiber.map_const_of_point_eq
        (f := f.hom.right.hom) (f' := g.hom.right.hom)
        (b := BasedTopCat.point f.right) (b' := BasedTopCat.point g.right)
        sq.left.right.hom sq.right.right.hom w (BasedTopCat.map_point sq.right)
        (BasedTopCat.point f.left) (BasedTopCat.point g.left)
        (BasedTopCat.map_point f.hom) (BasedTopCat.map_point g.hom)
        (BasedTopCat.map_point sq.left))
  map_id f := by
    apply Under.UnderMorphism.ext
    rw [Under.id_right]
    apply TopCat.hom_ext
    rw [TopCat.hom_id]
    exact ContinuousMap.HomotopyFiber.map_id
      (f := f.hom.right.hom) (b := BasedTopCat.point f.right)
  map_comp {f g h} sq sq' := by
    apply Under.UnderMorphism.ext
    rw [Under.comp_right]
    apply TopCat.hom_ext
    rw [TopCat.hom_comp]
    exact (ContinuousMap.HomotopyFiber.map_comp
      (f := f.hom.right.hom) (f' := g.hom.right.hom) (f'' := h.hom.right.hom)
      (b := BasedTopCat.point f.right) (b' := BasedTopCat.point g.right)
      (b'' := BasedTopCat.point h.right)
      sq.left.right.hom sq.right.right.hom
      sq'.left.right.hom sq'.right.right.hom
      (fun e => congrArg (fun k : f.left ⟶ g.right => k.right.hom e) (Arrow.w sq))
      (fun e => congrArg (fun k : g.left ⟶ h.right => k.right.hom e) (Arrow.w sq'))
      (BasedTopCat.map_point sq.right) (BasedTopCat.map_point sq'.right)).symm

/-- The underlying space is the original ordinary homotopy fiber over the target basepoint. -/
theorem homotopyFiberFunctor_obj_right (f : Arrow BasedTopCat.{u}) :
    (homotopyFiberFunctor.obj f).right =
      TopCat.of (ContinuousMap.HomotopyFiber f.hom.right.hom (BasedTopCat.point f.right)) :=
  rfl

/-- The selected fiber point retains the source basepoint and the constant target path. -/
@[simp]
theorem homotopyFiberFunctor_obj_point (f : Arrow BasedTopCat.{u}) :
    BasedTopCat.point (homotopyFiberFunctor.obj f) =
      ContinuousMap.HomotopyFiber.const
        (f := f.hom.right.hom) (b := BasedTopCat.point f.right)
        (BasedTopCat.point f.left) (BasedTopCat.map_point f.hom) :=
  rfl

/-- A strict based square acts on the retained point by its source-coordinate map. -/
@[simp]
theorem homotopyFiberFunctor_map_point {f g : Arrow BasedTopCat.{u}} (sq : f ⟶ g)
    (z : ContinuousMap.HomotopyFiber f.hom.right.hom (BasedTopCat.point f.right)) :
    ContinuousMap.HomotopyFiber.point ((homotopyFiberFunctor.map sq).right.hom z) =
      sq.left.right.hom (ContinuousMap.HomotopyFiber.point z) :=
  ContinuousMap.HomotopyFiber.point_map
    sq.left.right.hom sq.right.right.hom
    (fun e => congrArg (fun k : f.left ⟶ g.right => k.right.hom e) (Arrow.w sq))
    (BasedTopCat.map_point sq.right) z

/-- A strict based square postcomposes the entire retained forward path. -/
@[simp]
theorem homotopyFiberFunctor_map_path {f g : Arrow BasedTopCat.{u}} (sq : f ⟶ g)
    (z : ContinuousMap.HomotopyFiber f.hom.right.hom (BasedTopCat.point f.right)) :
    ContinuousMap.HomotopyFiber.path ((homotopyFiberFunctor.map sq).right.hom z) =
      sq.right.right.hom.comp (ContinuousMap.HomotopyFiber.path z) :=
  ContinuousMap.HomotopyFiber.path_map
    sq.left.right.hom sq.right.right.hom
    (fun e => congrArg (fun k : f.left ⟶ g.right => k.right.hom e) (Arrow.w sq))
    (BasedTopCat.map_point sq.right) z

/-- The retained-point projection from the homotopy fiber to the arrow's original source. -/
def homotopyFiberProjection :
    homotopyFiberFunctor ⟶ (Arrow.leftFunc : Arrow BasedTopCat.{u} ⥤ BasedTopCat.{u}) where
  app f :=
    Under.homMk
      (TopCat.ofHom (ContinuousMap.HomotopyFiber.point
        (f := f.hom.right.hom) (b := BasedTopCat.point f.right)))
      (by
        apply TopCat.ext
        intro t
        cases t
        rfl)
  naturality {f g} sq := by
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    intro z
    exact homotopyFiberFunctor_map_point sq z

/-- Each projection component is the original raw retained-point continuous map. -/
@[simp]
theorem homotopyFiberProjection_app_right_hom (f : Arrow BasedTopCat.{u}) :
    (homotopyFiberProjection.app f).right.hom =
      ContinuousMap.HomotopyFiber.point
        (f := f.hom.right.hom) (b := BasedTopCat.point f.right) :=
  rfl

/-- The natural projection evaluates by taking the original retained point. -/
theorem homotopyFiberProjection_app_apply (f : Arrow BasedTopCat.{u})
    (z : ContinuousMap.HomotopyFiber f.hom.right.hom (BasedTopCat.point f.right)) :
    (homotopyFiberProjection.app f).right.hom z = ContinuousMap.HomotopyFiber.point z :=
  rfl

end Functor

/-- The lifted point projection of the original homotopy fiber, based at its constant path. -/
def homotopyFiberPoint.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    ofULift.{max w u v} (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h) ⟶
      ofULift.{max w u v} E e₀ :=
  ofHomULift.{w} (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
    (ContinuousMap.HomotopyFiber.point_const e₀ h)

/-- The lifted whole-forward-loop inclusion into the original homotopy fiber. -/
noncomputable def homotopyFiberLoopInclusion.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    ofULift.{max w u v} (Path b b) (Path.refl b) ⟶
      ofULift.{max w u v} (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h) :=
  ofHomULift.{w} (ContinuousMap.HomotopyFiber.loopInclusion f b e₀ h)
    (ContinuousMap.HomotopyFiber.loopInclusion_refl f b e₀ h)

/-- The lifted based map on the original loop spaces induced by a based continuous map. -/
def loopMapHom.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b) :
    ofULift.{max w u v} (Path e₀ e₀) (Path.refl e₀) ⟶
      ofULift.{max w u v} (Path b b) (Path.refl b) :=
  ofHomULift.{w} (f.loopMap e₀ b h) (f.loopMap_refl e₀ b h)

/-- The lifted fiber projection evaluates by taking the original point coordinate. -/
@[simp]
theorem homotopyFiberPoint_apply.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (x : ULift.{max w u v} (ContinuousMap.HomotopyFiber f b)) :
    (homotopyFiberPoint.{w} f b e₀ h).right.hom x =
      ULift.up (ContinuousMap.HomotopyFiber.point x.down) := rfl

/-- The lifted projection sends the constant-path fiber point to the chosen source point. -/
@[simp]
theorem homotopyFiberPoint_const.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    (homotopyFiberPoint.{w} f b e₀ h).right.hom
        (ULift.up (ContinuousMap.HomotopyFiber.const e₀ h)) = ULift.up e₀ := rfl

/-- The lifted loop inclusion is the lift of the named loop inclusion. -/
@[simp]
theorem homotopyFiberLoopInclusion_apply.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (γ : ULift.{max w u v} (Path b b)) :
    (homotopyFiberLoopInclusion.{w} f b e₀ h).right.hom γ =
      ULift.up (ContinuousMap.HomotopyFiber.loopInclusion f b e₀ h γ.down) := rfl

/-- The point coordinate of the lifted loop inclusion is the chosen source point. -/
@[simp]
theorem homotopyFiberLoopInclusion_point.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (γ : ULift.{max w u v} (Path b b)) :
    ContinuousMap.HomotopyFiber.point
        ((homotopyFiberLoopInclusion.{w} f b e₀ h).right.hom γ).down = e₀ :=
  ContinuousMap.HomotopyFiber.loopInclusion_point f b e₀ h γ.down

/-- The retained path of the lifted loop inclusion is the entire original forward loop. -/
@[simp]
theorem homotopyFiberLoopInclusion_path.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (γ : ULift.{max w u v} (Path b b)) :
    ContinuousMap.HomotopyFiber.path
        ((homotopyFiberLoopInclusion.{w} f b e₀ h).right.hom γ).down =
      γ.down.toContinuousMap :=
  ContinuousMap.HomotopyFiber.loopInclusion_path f b e₀ h γ.down

/-- The lifted loop inclusion sends the constant loop to the constant-path fiber point. -/
theorem homotopyFiberLoopInclusion_refl.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    (homotopyFiberLoopInclusion.{w} f b e₀ h).right.hom (ULift.up (Path.refl b)) =
      ULift.up (ContinuousMap.HomotopyFiber.const e₀ h) :=
  congrArg ULift.up (ContinuousMap.HomotopyFiber.loopInclusion_refl f b e₀ h)

/-- The lifted loop map evaluates by lifting the pointwise loop map. -/
@[simp]
theorem loopMapHom_apply.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b)
    (γ : ULift.{max w u v} (Path e₀ e₀)) :
    (loopMapHom.{w} f e₀ b h).right.hom γ = ULift.up (f.loopMap e₀ b h γ.down) := rfl

/-- Evaluation in time of the lifted loop map is pointwise application of the original map. -/
@[simp]
theorem loopMapHom_apply_apply.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b)
    (γ : ULift.{max w u v} (Path e₀ e₀)) (t : unitInterval) :
    ((loopMapHom.{w} f e₀ b h).right.hom γ).down t = f (γ.down t) := rfl

/-- The lifted loop map preserves the selected constant loop. -/
theorem loopMapHom_refl.{w, u, v} {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (e₀ : E) (b : B) (h : f e₀ = b) :
    (loopMapHom.{w} f e₀ b h).right.hom (ULift.up (Path.refl e₀)) =
      ULift.up (Path.refl b) :=
  congrArg ULift.up (f.loopMap_refl e₀ b h)

/-- The lifted identity map on loops is the identity based morphism. -/
@[simp]
theorem loopMapHom_id.{w, u} {E : Type u} [TopologicalSpace E] (e₀ : E) :
    loopMapHom.{w} (ContinuousMap.id E) e₀ e₀ rfl =
      𝟙 (ofULift.{max w u} (Path e₀ e₀) (Path.refl e₀)) := by
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  intro γ
  exact congrArg ULift.up (congrArg (fun k : C(Path e₀ e₀, Path e₀ e₀) ↦ k γ.down)
    (ContinuousMap.loopMap_id e₀))

/-- The lifted loop map preserves composition in a common universe. -/
theorem loopMapHom_comp.{w, u, v, t} {E : Type u} {B : Type v} {T : Type t}
    [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace T]
    (f : C(E, B)) (g : C(B, T)) (e₀ : E) (b : B) (c : T)
    (hf : f e₀ = b) (hg : g b = c) :
    loopMapHom.{max w u v t} (g.comp f) e₀ c ((congrArg g hf).trans hg) =
      loopMapHom.{max w u v t} f e₀ b hf ≫ loopMapHom.{max w u v t} g b c hg := by
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  intro γ
  exact congrArg ULift.up (congrArg (fun k : C(Path e₀ e₀, Path c c) ↦ k γ.down)
    (ContinuousMap.loopMap_comp f g e₀ b c hf hg))

end BasedTopCat
