/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based.Universe
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Loop
public import FundamentalGroupoids.Topology.Path

/-!
# Based maps in the homotopy-fiber sequence

The homotopy fiber retains paths from the chosen target point to the image of
its point coordinate. Its projection and whole-forward-loop inclusion become
based maps after ordinary universe lifting of the original spaces. The map on
based loops is pointwise application of the original continuous map, with
endpoint casts determined by its basepoint equation.

The source and target spaces may lie in independent universes. In particular,
we lift the original homotopy fiber and the original path spaces; no
identification with a homotopy fiber or loop space of lifted maps is used.
-/

@[expose] public section

open CategoryTheory


namespace BasedTopCat

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
