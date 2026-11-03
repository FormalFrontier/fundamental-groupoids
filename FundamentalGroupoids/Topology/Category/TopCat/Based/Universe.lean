/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based
public import Mathlib.Topology.Constructions

/-!
# Universe lifts of based spaces and maps

Ordinary `ULift` transports a space and its selected point to a larger universe.
Maps between spaces in independent universes can then be regarded as morphisms
of `BasedTopCat` in a common universe. These constructions lift the original
spaces, without replacing them by other homeomorphic models.

Postcomposition on based-homotopy classes is composition in the existing
based-homotopy category.
-/

@[expose] public section

open CategoryTheory

namespace BasedTopCat

/-- A space with its selected point, lifted by ordinary `ULift`. -/
def ofULift.{v, u} (X : Type u) [TopologicalSpace X] (x : X) :
    BasedTopCat.{max u v} :=
  of (ULift.{v} X) (ULift.up x)

/-- The underlying space of a lifted based space is the lift of the original space. -/
theorem ofULift_right.{v, u} (X : Type u) [TopologicalSpace X] (x : X) :
    (ofULift.{v} X x).right = TopCat.of (ULift.{v} X) := rfl

/-- The selected point of a lifted based space is the lifted original point. -/
@[simp]
theorem point_ofULift.{v, u} (X : Type u) [TopologicalSpace X] (x : X) :
    point (ofULift.{v} X x) = ULift.up x := rfl

/-- Lift a continuous based map between independent universes to a common universe. -/
def ofHomULift.{w, u, v} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) :
    ofULift.{max w u v} X x ⟶ ofULift.{max w u v} Y y :=
  ofHom (⟨ULift.map f, continuous_uliftMap f f.continuous⟩ :
    C(ULift.{max w u v} X, ULift.{max w u v} Y)) (congrArg ULift.up h)

/-- Evaluation of a lifted based map is ordinary up/down transport. -/
@[simp]
theorem ofHomULift_apply.{w, u, v} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) (z : ULift.{max w u v} X) :
    (ofHomULift.{w} f h).right.hom z = ULift.up (f z.down) := rfl

/-- The continuous map underlying a lifted based map is ordinary `ULift.map`. -/
theorem ofHomULift_right_hom.{w, u, v} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) :
    (ofHomULift.{w} f h).right.hom =
      (⟨ULift.map f, continuous_uliftMap f f.continuous⟩ :
        C(ULift.{max w u v} X, ULift.{max w u v} Y)) := by
  rfl

/-- Lowering the value of a lifted based map recovers evaluation of the original map. -/
theorem ofHomULift_apply_down.{w, u, v} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (h : f x = y) (z : ULift.{max w u v} X) :
    ((ofHomULift.{w} f h).right.hom z).down = f z.down := by
  rfl

/-- Lifting the identity based map gives the identity morphism. -/
@[simp]
theorem ofHomULift_id.{w, u} {X : Type u} [TopologicalSpace X] (x : X) :
    ofHomULift.{w} (ContinuousMap.id X) (x := x) (y := x) rfl =
      𝟙 (ofULift.{max w u} X x) := by
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  intro z
  rfl

/-- Lifting preserves composition when all maps use the same common universe. -/
theorem ofHomULift_comp.{w, u, v, t} {X : Type u} {Y : Type v} {T : Type t}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    {x : X} {y : Y} {z : T} (f : C(X, Y)) (g : C(Y, T))
    (hf : f x = y) (hg : g y = z) :
    ofHomULift.{max w u v t} (g.comp f) ((congrArg g hf).trans hg) =
      ofHomULift.{max w u v t} f hf ≫ ofHomULift.{max w u v t} g hg := by
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  intro a
  rfl

/-- Every based-homotopy class between lifted spaces has a continuous based representative
between the original spaces. -/
theorem exists_homotopyQuotient_map_ofHomULift_eq.{w, u, v}
    (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y]
    (x : X) (y : Y)
    (q : homotopyQuotient.obj (ofULift.{max w u v} X x) ⟶
      homotopyQuotient.obj (ofULift.{max w u v} Y y)) :
    ∃ (f : C(X, Y)) (h : f x = y),
      homotopyQuotient.map (ofHomULift.{max w u v} f h) = q := by
  obtain ⟨g, rfl⟩ := homotopyQuotient.map_surjective q
  let f : C(X, Y) :=
    ⟨fun z ↦ (g.right.hom (ULift.up z)).down,
      continuous_uliftDown.comp (g.right.hom.continuous.comp continuous_uliftUp)⟩
  have h : f x = y := congrArg ULift.down (map_point g)
  refine ⟨f, h, ?_⟩
  apply congrArg homotopyQuotient.map
  apply Under.UnderMorphism.ext
  apply TopCat.ext
  intro z
  rfl

/-- Lifting preserves and reflects homotopy relative to the selected source point. -/
theorem homotopyRel_ofHomULift_iff.{w, u, v} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f g : C(X, Y)) (hf : f x = y) (hg : g x = y) :
    homotopyRel (ofHomULift.{w} f hf) (ofHomULift.{w} g hg) ↔
      ContinuousMap.HomotopicRel f g {x} := by
  constructor
  · intro H
    let up : C(X, ULift.{max w u v} X) := ⟨ULift.up, continuous_uliftUp⟩
    let down : C(ULift.{max w u v} Y, Y) := ⟨ULift.down, continuous_uliftDown⟩
    have hpoint : Set.MapsTo up {x} {point (ofULift.{max w u v} X x)} := by
      intro z hz
      have hz' : z = x := Set.mem_singleton_iff.mp hz
      subst z
      exact Set.mem_singleton_iff.mpr rfl
    exact (((homotopyRel_iff _ _).mp H).precomp_continuousMap up hpoint).comp_continuousMap
      down
  · intro H
    let down : C(ULift.{max w u v} X, X) := ⟨ULift.down, continuous_uliftDown⟩
    let up : C(Y, ULift.{max w u v} Y) := ⟨ULift.up, continuous_uliftUp⟩
    have hpoint : Set.MapsTo down {point (ofULift.{max w u v} X x)} {x} := by
      intro z hz
      have hz' : z = point (ofULift.{max w u v} X x) := Set.mem_singleton_iff.mp hz
      subst z
      exact Set.mem_singleton_iff.mpr rfl
    exact (H.precomp_continuousMap down hpoint).comp_continuousMap up

/-- Two lifted original based maps have the same class exactly when the original
maps are homotopic relative to their source basepoint. -/
theorem homotopyQuotient_map_ofHomULift_eq_iff.{w, u, v} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (f g : C(X, Y)) (hf : f x = y) (hg : g x = y) :
    homotopyQuotient.map (ofHomULift.{w} f hf) =
        homotopyQuotient.map (ofHomULift.{w} g hg) ↔
      ContinuousMap.HomotopicRel f g {x} := by
  exact (homotopyQuotient_map_eq_iff _ _).trans
    (homotopyRel_ofHomULift_iff.{w} f g hf hg)

/-- Postcomposition of lifted classes agrees with lifting the composite original map. -/
theorem homotopyPostcomp_ofHomULift.{w, u, v, t} {X : Type u} {Y : Type v} {T : Type t}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace T]
    {x : X} {y : Y} {z : T} (f : C(X, Y)) (g : C(Y, T))
    (hf : f x = y) (hg : g y = z) :
    homotopyPostcomp (ofULift.{max w u v t} X x)
        (ofHomULift.{max w u v t} g hg)
        (homotopyQuotient.map (ofHomULift.{max w u v t} f hf)) =
      homotopyQuotient.map
        (ofHomULift.{max w u v t} (g.comp f) ((congrArg g hf).trans hg)) := by
  rw [homotopyPostcomp_apply]
  calc
    _ = homotopyQuotient.map
        (ofHomULift.{max w u v t} f hf ≫ ofHomULift.{max w u v t} g hg) :=
      (homotopyQuotient.map_comp _ _).symm
    _ = _ := congrArg homotopyQuotient.map (ofHomULift_comp.{w} f g hf hg).symm

end BasedTopCat
