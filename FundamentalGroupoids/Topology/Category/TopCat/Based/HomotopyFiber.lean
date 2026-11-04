/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Category.TopCat.Based.Loop
public import FundamentalGroupoids.Topology.Category.TopCat.Based.Universe
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Loop
public import FundamentalGroupoids.Topology.Path
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Based homotopy fibers, nullhomotopies, loop inclusion and lifted sequence maps

The homotopy fiber retains paths from the chosen target point to the image of
its point coordinate. For an arrow of based spaces in a common universe,
`BasedTopCat.homotopyFiberFunctor` selects this original homotopy fiber over the
target basepoint, based at the source basepoint and the constant path. Strict
based squares act on its point coordinate and postcompose its whole forward
path. `BasedTopCat.homotopyFiberProjection` projects naturally to the arrow's
original source based space. The natural transformation
`BasedTopCat.loopToHomotopyFiber` includes target loops by retaining the source
basepoint and the whole original forward loop. Its composite with the natural
projection is constant at the original source basepoint.

The full retained path gives `BasedTopCat.homotopyFiberNullhomotopy`, a homotopy
relative to the selected fiber point from the canonical constant map to the
projection followed by the original arrow. It is strictly natural in based
squares at every time and fiber point. Consequently, projection followed by
the arrow is based homotopic to the constant map, and its image in the
based-homotopy category is the class of that constant map.

Shortening source loops gives
`BasedTopCat.loopMapCompLoopToHomotopyFiberNullhomotopy`, from the canonical
constant map to the loop map followed by the forward loop inclusion, relative
to the constant source loop. At time `s` it retains `γ s` and the whole path
`t ↦ f (γ (s * t))`. This is strictly natural in based squares, and the composite
represents the canonical constant in the based-homotopy category. Both null
triangles are unsigned and use ordinary topologies.

Precomposing source-loop shortening by the existing loop-reversal component gives
`BasedTopCat.loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy`.
It goes from the canonical constant map to the loop map, reversal and forward
loop inclusion. At homotopy time `s`, its point is `γ (1 - s)` and its whole
retained forward path is `t ↦ f (γ (1 - s * t))`. The outer parameter is unchanged.
Every time slice fixes the constant loop, and strict based squares commute with
the whole homotopy at the same time.

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
  `ContinuousMap.HomotopyFiber.map`. Source-loop shortening reuses
  `ContinuousMap.HomotopyFiber.loopInclusionCompLoopMapHomotopy` with Mathlib's
  outer-time symmetry.
* Reversal-precomposed shortening reuses the Formal Frontier Agents formalizations
  of source-loop shortening, based loop maps and reversal, and whole relative-homotopy
  precomposition. The path reversal, homotopy precomposition and endpoint transport
  use Mathlib's path and homotopy APIs, due to Patrick Massot and Shing Tak Lam.
  The strict-arrow formalization is due to Markus Himmel.
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

/-- The continuous map underlying a strict based square is the induced map of homotopy fibers. -/
theorem homotopyFiberFunctor_map_right_hom {f g : Arrow BasedTopCat.{u}} (sq : f ⟶ g) :
    (homotopyFiberFunctor.map sq).right.hom =
      ContinuousMap.HomotopyFiber.map
        (f := f.hom.right.hom) (f' := g.hom.right.hom)
        (b := BasedTopCat.point f.right) (b' := BasedTopCat.point g.right)
        sq.left.right.hom sq.right.right.hom
        (fun e => congrArg (fun k : f.left ⟶ g.right => k.right.hom e) (Arrow.w sq))
        (BasedTopCat.map_point sq.right) :=
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

/-- The retained forward path gives a homotopy from the canonical constant map to the
original projection followed by the arrow, fixing the selected fiber point at every time. -/
noncomputable def homotopyFiberNullhomotopy (f : Arrow BasedTopCat.{u}) :
    ((const (homotopyFiberFunctor.obj f) f.right).right.hom).HomotopyRel
      (((homotopyFiberProjection.app f) ≫ f.hom).right.hom)
      {point (homotopyFiberFunctor.obj f)} :=
  ContinuousMap.HomotopyFiber.pathHomotopyRel
    f.hom.right.hom (point f.right) (point f.left) (map_point f.hom)

/-- At every time and fiber point, the nullhomotopy evaluates the entire retained path. -/
theorem homotopyFiberNullhomotopy_apply (f : Arrow BasedTopCat.{u})
    (p : unitInterval ×
      ContinuousMap.HomotopyFiber f.hom.right.hom (point f.right)) :
    homotopyFiberNullhomotopy f p = ContinuousMap.HomotopyFiber.path p.2 p.1 :=
  ContinuousMap.HomotopyFiber.pathHomotopyRel_apply f.hom.right.hom
    (point f.right) (point f.left) (map_point f.hom) p.1 p.2

/-- Strict based squares commute with the retained-path nullhomotopy at every time
and every point of the original homotopy fiber. -/
theorem homotopyFiberNullhomotopy_naturality
    {f g : Arrow BasedTopCat.{u}} (sq : f ⟶ g) (t : unitInterval)
    (z : ContinuousMap.HomotopyFiber f.hom.right.hom (point f.right)) :
    sq.right.right.hom (homotopyFiberNullhomotopy f (t, z)) =
      homotopyFiberNullhomotopy g
        (t, (homotopyFiberFunctor.map sq).right.hom z) := by
  calc
    sq.right.right.hom (homotopyFiberNullhomotopy f (t, z)) =
        sq.right.right.hom (ContinuousMap.HomotopyFiber.path z t) :=
      congrArg sq.right.right.hom (homotopyFiberNullhomotopy_apply f (t, z))
    _ = ContinuousMap.HomotopyFiber.path
        ((homotopyFiberFunctor.map sq).right.hom z) t :=
      (congrArg (fun γ : C(unitInterval, g.right.right) ↦ γ t)
        (homotopyFiberFunctor_map_path sq z)).symm
    _ = homotopyFiberNullhomotopy g
        (t, (homotopyFiberFunctor.map sq).right.hom z) :=
      (homotopyFiberNullhomotopy_apply g
        (t, (homotopyFiberFunctor.map sq).right.hom z)).symm

/-- Projection followed by the original arrow is based homotopic to the canonical
constant map. -/
theorem homotopyFiberProjection_comp_homotopyRel (f : Arrow BasedTopCat.{u}) :
    homotopyRel ((homotopyFiberProjection.app f) ≫ f.hom)
      (const (homotopyFiberFunctor.obj f) f.right) := by
  exact (homotopyRel_iff _ _).2 ⟨(homotopyFiberNullhomotopy f).symm⟩

/-- In the based-homotopy category, projection followed by the original arrow is
the class of the canonical constant map. -/
theorem homotopyQuotient_map_homotopyFiberProjection_comp (f : Arrow BasedTopCat.{u}) :
    homotopyQuotient.map (homotopyFiberProjection.app f) ≫
        homotopyQuotient.map f.hom =
      homotopyQuotient.map (const (homotopyFiberFunctor.obj f) f.right) := by
  calc
    homotopyQuotient.map (homotopyFiberProjection.app f) ≫
        homotopyQuotient.map f.hom =
        homotopyQuotient.map ((homotopyFiberProjection.app f) ≫ f.hom) :=
      (homotopyQuotient.map_comp _ _).symm
    _ = homotopyQuotient.map (const (homotopyFiberFunctor.obj f) f.right) :=
      (homotopyQuotient_map_eq_iff _ _).2
        ((homotopyRel_iff _ _).1 (homotopyFiberProjection_comp_homotopyRel f))

/-- The natural inclusion of target loops into the ordinary homotopy fiber,
retaining the source basepoint and the entire original forward loop. -/
noncomputable def loopToHomotopyFiber :
    ((Arrow.rightFunc : Arrow BasedTopCat.{u} ⥤ BasedTopCat.{u}) ⋙ loopFunctor) ⟶
      homotopyFiberFunctor where
  app f :=
    BasedTopCat.ofHom
      (ContinuousMap.HomotopyFiber.loopInclusion f.hom.right.hom
        (BasedTopCat.point f.right) (BasedTopCat.point f.left)
        (BasedTopCat.map_point f.hom))
      (ContinuousMap.HomotopyFiber.loopInclusion_refl f.hom.right.hom
        (BasedTopCat.point f.right) (BasedTopCat.point f.left)
        (BasedTopCat.map_point f.hom))
  naturality {f g} sq := by
    apply Under.UnderMorphism.ext
    apply TopCat.ext
    intro γ
    exact congrArg
      (fun k : C(Path (BasedTopCat.point f.right) (BasedTopCat.point f.right),
          ContinuousMap.HomotopyFiber g.hom.right.hom (BasedTopCat.point g.right)) ↦ k γ)
      (ContinuousMap.HomotopyFiber.loopInclusion_naturality_loopMap
        (f := f.hom.right.hom) (f' := g.hom.right.hom)
        (b := BasedTopCat.point f.right) (b' := BasedTopCat.point g.right)
        sq.left.right.hom sq.right.right.hom
        (fun e => congrArg (fun k : f.left ⟶ g.right => k.right.hom e) (Arrow.w sq))
        (BasedTopCat.point f.left) (BasedTopCat.point g.left)
        (BasedTopCat.map_point f.hom) (BasedTopCat.map_point g.hom)
        (BasedTopCat.map_point sq.left) (BasedTopCat.map_point sq.right)).symm

/-- Each component is the whole-forward-loop inclusion of the original homotopy fiber. -/
theorem loopToHomotopyFiber_app_right_hom (f : Arrow BasedTopCat.{u}) :
    (loopToHomotopyFiber.app f).right.hom =
      ContinuousMap.HomotopyFiber.loopInclusion f.hom.right.hom
        (BasedTopCat.point f.right) (BasedTopCat.point f.left)
        (BasedTopCat.map_point f.hom) :=
  rfl

/-- The loop inclusion pairs the source basepoint with the entire original forward loop. -/
theorem loopToHomotopyFiber_app_apply (f : Arrow BasedTopCat.{u})
    (γ : Path (BasedTopCat.point f.right) (BasedTopCat.point f.right)) :
    (loopToHomotopyFiber.app f).right.hom γ =
      ContinuousMap.HomotopyFiber.mk
        (f := f.hom.right.hom) (b := BasedTopCat.point f.right)
        (BasedTopCat.point f.left) γ.toContinuousMap γ.source
        (γ.target.trans (BasedTopCat.map_point f.hom).symm) := by
  rw [loopToHomotopyFiber_app_right_hom]
  exact ContinuousMap.HomotopyFiber.loopInclusion_apply
    (BasedTopCat.point f.left) (BasedTopCat.map_point f.hom) γ

/-- The natural loop inclusion retains the original source basepoint. -/
@[simp]
theorem loopToHomotopyFiber_app_point (f : Arrow BasedTopCat.{u})
    (γ : Path (BasedTopCat.point f.right) (BasedTopCat.point f.right)) :
    ContinuousMap.HomotopyFiber.point
        ((Under.Hom.right (f := loopFunctor.obj f.right) (loopToHomotopyFiber.app f)).hom γ) =
      BasedTopCat.point f.left := by
  exact congrArg ContinuousMap.HomotopyFiber.point (loopToHomotopyFiber_app_apply f γ)

/-- The retained path is the whole original forward loop as a continuous map. -/
@[simp]
theorem loopToHomotopyFiber_app_path (f : Arrow BasedTopCat.{u})
    (γ : Path (BasedTopCat.point f.right) (BasedTopCat.point f.right)) :
    ContinuousMap.HomotopyFiber.path
        ((Under.Hom.right (f := loopFunctor.obj f.right) (loopToHomotopyFiber.app f)).hom γ) =
      γ.toContinuousMap := by
  exact congrArg ContinuousMap.HomotopyFiber.path (loopToHomotopyFiber_app_apply f γ)

/-- Evaluation of the retained path at every time agrees with the original loop. -/
theorem loopToHomotopyFiber_app_path_apply (f : Arrow BasedTopCat.{u})
    (γ : Path (BasedTopCat.point f.right) (BasedTopCat.point f.right)) (t : unitInterval) :
    ContinuousMap.HomotopyFiber.path ((loopToHomotopyFiber.app f).right.hom γ) t = γ t := by
  rw [loopToHomotopyFiber_app_right_hom]
  exact ContinuousMap.HomotopyFiber.loopInclusion_path_apply f.hom.right.hom
    (BasedTopCat.point f.right) (BasedTopCat.point f.left)
    (BasedTopCat.map_point f.hom) γ t

/-- The constant target loop is sent to the selected point of the homotopy fiber. -/
@[simp]
theorem loopToHomotopyFiber_app_refl (f : Arrow BasedTopCat.{u}) :
    (Under.Hom.right (f := loopFunctor.obj f.right) (loopToHomotopyFiber.app f)).hom
        (Path.refl (BasedTopCat.point f.right)) =
      BasedTopCat.point (homotopyFiberFunctor.obj f) := by
  exact loopToHomotopyFiber_app_apply f (Path.refl (BasedTopCat.point f.right))

/-- Every strict based square commutes with the whole-forward-loop inclusion. -/
theorem loopToHomotopyFiber_naturality {f g : Arrow BasedTopCat.{u}} (sq : f ⟶ g) :
    loopToHomotopyFiber.app f ≫ homotopyFiberFunctor.map sq =
      loopFunctor.map sq.right ≫ loopToHomotopyFiber.app g :=
  (loopToHomotopyFiber.naturality sq).symm

/-- The natural loop inclusion followed by the natural fiber projection is constant
at the original source basepoint. -/
theorem loopToHomotopyFiber_comp_homotopyFiberProjection_app_right_hom
    (f : Arrow BasedTopCat.{u}) :
    ((loopToHomotopyFiber ≫ homotopyFiberProjection).app f).right.hom =
      ContinuousMap.const (Path (BasedTopCat.point f.right) (BasedTopCat.point f.right))
        (BasedTopCat.point f.left) := by
  change (homotopyFiberProjection.app f).right.hom.comp
    (loopToHomotopyFiber.app f).right.hom = _
  rw [homotopyFiberProjection_app_right_hom, loopToHomotopyFiber_app_right_hom]
  exact ContinuousMap.HomotopyFiber.point_comp_loopInclusion f.hom.right.hom
    (BasedTopCat.point f.right) (BasedTopCat.point f.left)
    (BasedTopCat.map_point f.hom)

/-- Every loop projects from its included fiber point to the original source basepoint. -/
theorem loopToHomotopyFiber_comp_homotopyFiberProjection_app_apply
    (f : Arrow BasedTopCat.{u})
    (γ : Path (BasedTopCat.point f.right) (BasedTopCat.point f.right)) :
    ((loopToHomotopyFiber ≫ homotopyFiberProjection).app f).right.hom γ =
      BasedTopCat.point f.left := by
  rw [loopToHomotopyFiber_comp_homotopyFiberProjection_app_right_hom]
  rfl

/-- Shortening the source loop gives a homotopy from the canonical constant map to
the loop map followed by the forward loop inclusion, fixing the constant source loop.
This reverses the outer time of
`ContinuousMap.HomotopyFiber.loopInclusionCompLoopMapHomotopy`. -/
noncomputable def loopMapCompLoopToHomotopyFiberNullhomotopy
    (f : Arrow BasedTopCat.{u}) :
    ((const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)).right.hom).HomotopyRel
      (((loopFunctor.map f.hom) ≫ loopToHomotopyFiber.app f).right.hom)
      {point (loopFunctor.obj f.left)} :=
  (ContinuousMap.HomotopyFiber.loopInclusionCompLoopMapHomotopy
    f.hom.right.hom (point f.right) (point f.left) (map_point f.hom)).symm

/-- The retained point follows the source loop at the outer homotopy time. -/
theorem loopMapCompLoopToHomotopyFiberNullhomotopy_point
    (f : Arrow BasedTopCat.{u})
    (p : unitInterval × Path (point f.left) (point f.left)) :
    ContinuousMap.HomotopyFiber.point
        (loopMapCompLoopToHomotopyFiberNullhomotopy f p) = p.2 p.1 := by
  change ContinuousMap.HomotopyFiber.point
    (ContinuousMap.HomotopyFiber.loopInclusionCompLoopMapHomotopy
      f.hom.right.hom (point f.right) (point f.left) (map_point f.hom)
      (unitInterval.symm p.1, p.2)) = _
  simpa only [unitInterval.symm_symm] using
    ContinuousMap.HomotopyFiber.point_loopInclusionCompLoopMapHomotopy
      f.hom.right.hom (point f.right) (point f.left) (map_point f.hom)
      (unitInterval.symm p.1) p.2

/-- Every value of the retained forward path is the mapped source-loop prefix. -/
theorem loopMapCompLoopToHomotopyFiberNullhomotopy_path_apply
    (f : Arrow BasedTopCat.{u}) (s : unitInterval)
    (γ : Path (point f.left) (point f.left)) (t : unitInterval) :
    ContinuousMap.HomotopyFiber.path
        (loopMapCompLoopToHomotopyFiberNullhomotopy f (s, γ)) t =
      f.hom.right.hom (γ (s * t)) := by
  change ContinuousMap.HomotopyFiber.path
    (ContinuousMap.HomotopyFiber.loopInclusionCompLoopMapHomotopy
      f.hom.right.hom (point f.right) (point f.left) (map_point f.hom)
      (unitInterval.symm s, γ)) t = _
  simpa only [unitInterval.symm_symm] using
    ContinuousMap.HomotopyFiber.path_loopInclusionCompLoopMapHomotopy_apply
      f.hom.right.hom (point f.right) (point f.left) (map_point f.hom)
      (unitInterval.symm s) γ t

/-- The whole retained forward path is the mapped initial segment of the source loop. -/
theorem loopMapCompLoopToHomotopyFiberNullhomotopy_path
    (f : Arrow BasedTopCat.{u})
    (p : unitInterval × Path (point f.left) (point f.left)) :
    ContinuousMap.HomotopyFiber.path
        (loopMapCompLoopToHomotopyFiberNullhomotopy f p) =
      f.hom.right.hom.comp
        (ContinuousMap.initialSegment (p.1, p.2.toContinuousMap)) := by
  apply ContinuousMap.ext
  intro t
  exact loopMapCompLoopToHomotopyFiberNullhomotopy_path_apply f p.1 p.2 t

/-- Strict based squares commute with source-loop shortening at every outer time,
for every source loop and its whole retained forward path. -/
theorem loopMapCompLoopToHomotopyFiberNullhomotopy_naturality
    {f g : Arrow BasedTopCat.{u}} (sq : f ⟶ g) (s : unitInterval)
    (γ : Path (point f.left) (point f.left)) :
    (homotopyFiberFunctor.map sq).right.hom
        (loopMapCompLoopToHomotopyFiberNullhomotopy f (s, γ)) =
      loopMapCompLoopToHomotopyFiberNullhomotopy g
        (s, (loopFunctor.map sq.left).right.hom γ) := by
  apply ContinuousMap.HomotopyFiber.ext
  · calc
      ContinuousMap.HomotopyFiber.point
          ((homotopyFiberFunctor.map sq).right.hom
            (loopMapCompLoopToHomotopyFiberNullhomotopy f (s, γ))) =
          sq.left.right.hom (ContinuousMap.HomotopyFiber.point
            (loopMapCompLoopToHomotopyFiberNullhomotopy f (s, γ))) :=
        homotopyFiberFunctor_map_point sq _
      _ = sq.left.right.hom (γ s) :=
        congrArg sq.left.right.hom
          (loopMapCompLoopToHomotopyFiberNullhomotopy_point f (s, γ))
      _ = Path.toContinuousMap (x := point g.left) (y := point g.left)
          ((loopFunctor.map sq.left).right.hom γ) s :=
        (loopFunctor_map_apply_apply sq.left γ s).symm
      _ = ContinuousMap.HomotopyFiber.point
          (loopMapCompLoopToHomotopyFiberNullhomotopy g
            (s, (loopFunctor.map sq.left).right.hom γ)) :=
        (loopMapCompLoopToHomotopyFiberNullhomotopy_point g
          (s, (loopFunctor.map sq.left).right.hom γ)).symm
  · apply ContinuousMap.ext
    intro t
    calc
      ContinuousMap.HomotopyFiber.path
          ((homotopyFiberFunctor.map sq).right.hom
            (loopMapCompLoopToHomotopyFiberNullhomotopy f (s, γ))) t =
          sq.right.right.hom (ContinuousMap.HomotopyFiber.path
            (loopMapCompLoopToHomotopyFiberNullhomotopy f (s, γ)) t) :=
        congrArg (fun η : C(unitInterval, g.right.right) ↦ η t)
          (homotopyFiberFunctor_map_path sq _)
      _ = sq.right.right.hom (f.hom.right.hom (γ (s * t))) :=
        congrArg sq.right.right.hom
          (loopMapCompLoopToHomotopyFiberNullhomotopy_path_apply f s γ t)
      _ = g.hom.right.hom (sq.left.right.hom (γ (s * t))) :=
        (congrArg (fun k : f.left ⟶ g.right ↦ k.right.hom (γ (s * t)))
          (Arrow.w sq)).symm
      _ = g.hom.right.hom
          (Path.toContinuousMap (x := point g.left) (y := point g.left)
            ((loopFunctor.map sq.left).right.hom γ) (s * t)) :=
        congrArg g.hom.right.hom (loopFunctor_map_apply_apply sq.left γ (s * t)).symm
      _ = ContinuousMap.HomotopyFiber.path
          (loopMapCompLoopToHomotopyFiberNullhomotopy g
            (s, (loopFunctor.map sq.left).right.hom γ)) t :=
        (loopMapCompLoopToHomotopyFiberNullhomotopy_path_apply g s
          ((loopFunctor.map sq.left).right.hom γ) t).symm

/-- The loop map followed by the forward loop inclusion is based homotopic to the
canonical constant map. -/
theorem loopMap_comp_loopToHomotopyFiber_homotopyRel
    (f : Arrow BasedTopCat.{u}) :
    homotopyRel ((loopFunctor.map f.hom) ≫ loopToHomotopyFiber.app f)
      (const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)) := by
  exact (homotopyRel_iff _ _).2
    ⟨(loopMapCompLoopToHomotopyFiberNullhomotopy f).symm⟩

/-- In the based-homotopy category, the loop map followed by the forward loop inclusion
is the class of the canonical constant map. -/
theorem homotopyQuotient_map_loopMap_comp_loopToHomotopyFiber
    (f : Arrow BasedTopCat.{u}) :
    homotopyQuotient.map (loopFunctor.map f.hom) ≫
        homotopyQuotient.map (loopToHomotopyFiber.app f) =
      homotopyQuotient.map
        (const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)) := by
  calc
    homotopyQuotient.map (loopFunctor.map f.hom) ≫
        homotopyQuotient.map (loopToHomotopyFiber.app f) =
        homotopyQuotient.map ((loopFunctor.map f.hom) ≫ loopToHomotopyFiber.app f) :=
      (homotopyQuotient.map_comp _ _).symm
    _ = homotopyQuotient.map
        (const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)) :=
      (homotopyQuotient_map_eq_iff _ _).2
        ((homotopyRel_iff _ _).1 (loopMap_comp_loopToHomotopyFiber_homotopyRel f))

/-- Precomposing source-loop shortening by loop reversal gives a homotopy from
 the canonical constant map to the loop map, reversal, and forward loop inclusion,
 relative to the constant source loop. The homotopy parameter is unchanged. -/
noncomputable def loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy
    (f : Arrow BasedTopCat.{u}) :
    ((const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)).right.hom).HomotopyRel
      (((loopFunctor.map f.hom) ≫ loopReversal.hom.app f.right ≫
        loopToHomotopyFiber.app f).right.hom)
      {point (loopFunctor.obj f.left)} := by
  let r_f := (loopReversal.hom.app f.left).right.hom
  let H_f := loopMapCompLoopToHomotopyFiberNullhomotopy f
  have hbase_f : Set.MapsTo r_f {point (loopFunctor.obj f.left)}
      {point (loopFunctor.obj f.left)} := by
    intro γ hγ
    obtain rfl : γ = point (loopFunctor.obj f.left) := Set.mem_singleton_iff.mp hγ
    exact Set.mem_singleton_iff.mpr (map_point (loopReversal.hom.app f.left))
  have hconst_f :
      ((const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)).right.hom).comp r_f =
        (const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)).right.hom := by
    simpa only [Under.comp_right, TopCat.hom_comp] using
      congrArg
        (fun k : loopFunctor.obj f.left ⟶ homotopyFiberFunctor.obj f ↦ k.right.hom)
        (comp_const (Z := homotopyFiberFunctor.obj f) (loopReversal.hom.app f.left))
  have htarget_f :
      (((loopFunctor.map f.hom) ≫ loopToHomotopyFiber.app f).right.hom).comp r_f =
        (((loopFunctor.map f.hom) ≫ loopReversal.hom.app f.right ≫
          loopToHomotopyFiber.app f).right.hom) := by
    have hcomp :
        loopReversal.hom.app f.left ≫
            (loopFunctor.map f.hom ≫ loopToHomotopyFiber.app f) =
          loopFunctor.map f.hom ≫ loopReversal.hom.app f.right ≫
            loopToHomotopyFiber.app f := by
      calc
        loopReversal.hom.app f.left ≫
            (loopFunctor.map f.hom ≫ loopToHomotopyFiber.app f) =
            (loopReversal.hom.app f.left ≫ loopFunctor.map f.hom) ≫
              loopToHomotopyFiber.app f :=
          (Category.assoc (loopReversal.hom.app f.left)
            (loopFunctor.map f.hom) (loopToHomotopyFiber.app f)).symm
        _ = (loopFunctor.map f.hom ≫ loopReversal.hom.app f.right) ≫
            loopToHomotopyFiber.app f :=
          congrArg
            (fun k : loopFunctor.obj f.left ⟶ loopFunctor.obj f.right ↦
              k ≫ loopToHomotopyFiber.app f)
            (loopReversal.hom.naturality f.hom).symm
        _ = loopFunctor.map f.hom ≫ loopReversal.hom.app f.right ≫
            loopToHomotopyFiber.app f :=
          Category.assoc (loopFunctor.map f.hom)
            (loopReversal.hom.app f.right) (loopToHomotopyFiber.app f)
    exact congrArg
      (fun k : loopFunctor.obj f.left ⟶ homotopyFiberFunctor.obj f ↦ k.right.hom)
      hcomp
  exact (H_f.precomp r_f hbase_f).cast hconst_f htarget_f

/-- The whole fiber value is source-loop shortening evaluated on the reversed loop. -/
theorem loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_apply
    (f : Arrow BasedTopCat.{u})
    (p : unitInterval × Path (point f.left) (point f.left)) :
    loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f p =
      loopMapCompLoopToHomotopyFiberNullhomotopy f (p.1, p.2.symm) := by
  rfl

/-- The retained point follows the reversed source loop at the homotopy time. -/
theorem loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_point
    (f : Arrow BasedTopCat.{u})
    (p : unitInterval × Path (point f.left) (point f.left)) :
    ContinuousMap.HomotopyFiber.point
        (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f p) =
      p.2 (unitInterval.symm p.1) := by
  exact (congrArg
    (ContinuousMap.HomotopyFiber.point (f := f.hom.right.hom) (b := point f.right))
    (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_apply f p)).trans
      ((loopMapCompLoopToHomotopyFiberNullhomotopy_point f (p.1, p.2.symm)).trans
        (Path.symm_apply p.2 p.1))

/-- The whole retained forward path is the mapped initial segment of the reversed loop. -/
theorem loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_path
    (f : Arrow BasedTopCat.{u})
    (p : unitInterval × Path (point f.left) (point f.left)) :
    ContinuousMap.HomotopyFiber.path
        (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f p) =
      f.hom.right.hom.comp
        (ContinuousMap.initialSegment (p.1, (p.2.symm).toContinuousMap)) := by
  exact (congrArg
    (ContinuousMap.HomotopyFiber.path (f := f.hom.right.hom) (b := point f.right))
    (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_apply f p)).trans
      (loopMapCompLoopToHomotopyFiberNullhomotopy_path f (p.1, p.2.symm))

/-- Every path value uses reversal after multiplication of the two interval parameters. -/
theorem loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_path_apply
    (f : Arrow BasedTopCat.{u}) (s : unitInterval)
    (γ : Path (point f.left) (point f.left)) (t : unitInterval) :
    ContinuousMap.HomotopyFiber.path
        (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f (s, γ)) t =
      f.hom.right.hom (γ (unitInterval.symm (s * t))) := by
  exact (congrArg
    (fun z : ContinuousMap.HomotopyFiber f.hom.right.hom (point f.right) ↦
      ContinuousMap.HomotopyFiber.path z t)
    (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_apply f (s, γ))).trans
      ((loopMapCompLoopToHomotopyFiberNullhomotopy_path_apply f s γ.symm t).trans
        (congrArg f.hom.right.hom (Path.symm_apply γ (s * t))))

/-- At time zero the whole fiber value is the selected constant-path point. -/
@[simp]
theorem loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_zero
    (f : Arrow BasedTopCat.{u})
    (γ : Path (point f.left) (point f.left)) :
    loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f (0, γ) =
      point (homotopyFiberFunctor.obj f) := by
  exact ((loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f).apply_zero γ).trans
    (const_apply (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f) γ)

/-- At time one the whole fiber value is the reversed mapped loop at the source basepoint. -/
@[simp]
theorem loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_one
    (f : Arrow BasedTopCat.{u})
    (γ : Path (point f.left) (point f.left)) :
    loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f (1, γ) =
      (((loopFunctor.map f.hom) ≫ loopReversal.hom.app f.right ≫
        loopToHomotopyFiber.app f).right.hom) γ := by
  exact (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f).apply_one γ

/-- Every time slice fixes the constant source loop at the selected fiber point. -/
@[simp]
theorem loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_refl
    (f : Arrow BasedTopCat.{u}) (s : unitInterval) :
    loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f
        (s, Path.refl (point f.left)) =
      point (homotopyFiberFunctor.obj f) := by
  exact ((loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f).eq_fst s
    (x := Path.refl (point f.left))
    (Set.mem_singleton_iff.mpr (point_loopFunctor_obj f.left).symm)).trans
      (const_apply (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)
        (Path.refl (point f.left)))

/-- Strict based squares commute with the whole reversed-loop nullhomotopy
 at the same homotopy time. -/
theorem loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_naturality
    {f g : Arrow BasedTopCat.{u}} (sq : f ⟶ g) (s : unitInterval)
    (γ : Path (point f.left) (point f.left)) :
    (homotopyFiberFunctor.map sq).right.hom
        (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f (s, γ)) =
      loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy g
        (s, (loopFunctor.map sq.left).right.hom γ) := by
  calc
    (homotopyFiberFunctor.map sq).right.hom
        (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f (s, γ)) =
        (homotopyFiberFunctor.map sq).right.hom
          (loopMapCompLoopToHomotopyFiberNullhomotopy f (s, γ.symm)) :=
      congrArg (homotopyFiberFunctor.map sq).right.hom
        (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_apply f (s, γ))
    _ = loopMapCompLoopToHomotopyFiberNullhomotopy g
        (s, (loopFunctor.map sq.left).right.hom γ.symm) :=
      loopMapCompLoopToHomotopyFiberNullhomotopy_naturality sq s γ.symm
    _ = loopMapCompLoopToHomotopyFiberNullhomotopy g
        (s, ((loopFunctor.map sq.left).right.hom γ).symm) :=
      congrArg
        (fun δ : Path (point g.left) (point g.left) ↦
          loopMapCompLoopToHomotopyFiberNullhomotopy g (s, δ))
        (ContinuousMap.loopMap_symm sq.left.right.hom
          (point f.left) (point g.left) (map_point sq.left) γ)
    _ = loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy g
        (s, (loopFunctor.map sq.left).right.hom γ) :=
      (loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy_apply g
        (s, (loopFunctor.map sq.left).right.hom γ)).symm

/-- The loop map, reversal, and forward loop inclusion are based homotopic
 to the canonical constant map. -/
theorem loopMap_comp_loopReversal_comp_loopToHomotopyFiber_homotopyRel
    (f : Arrow BasedTopCat.{u}) :
    homotopyRel ((loopFunctor.map f.hom) ≫ loopReversal.hom.app f.right ≫
      loopToHomotopyFiber.app f)
      (const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)) := by
  exact (homotopyRel_iff _ _).2
    ⟨(loopMapCompLoopReversalCompLoopToHomotopyFiberNullhomotopy f).symm⟩

/-- In the based-homotopy category, the loop map, reversal, and forward loop
 inclusion have the class of the canonical constant map. -/
theorem homotopyQuotient_map_loopMap_comp_loopReversal_comp_loopToHomotopyFiber
    (f : Arrow BasedTopCat.{u}) :
    homotopyQuotient.map (loopFunctor.map f.hom) ≫
        homotopyQuotient.map (loopReversal.hom.app f.right) ≫
        homotopyQuotient.map (loopToHomotopyFiber.app f) =
      homotopyQuotient.map
        (const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)) := by
  calc
    homotopyQuotient.map (loopFunctor.map f.hom) ≫
        homotopyQuotient.map (loopReversal.hom.app f.right) ≫
        homotopyQuotient.map (loopToHomotopyFiber.app f) =
        homotopyQuotient.map (loopFunctor.map f.hom) ≫
          homotopyQuotient.map (loopReversal.hom.app f.right ≫
            loopToHomotopyFiber.app f) :=
      congrArg
        (fun k : homotopyQuotient.obj (loopFunctor.obj f.right) ⟶
            homotopyQuotient.obj (homotopyFiberFunctor.obj f) ↦
          homotopyQuotient.map (loopFunctor.map f.hom) ≫ k)
        (homotopyQuotient.map_comp (loopReversal.hom.app f.right)
          (loopToHomotopyFiber.app f)).symm
    _ = homotopyQuotient.map
        ((loopFunctor.map f.hom) ≫ loopReversal.hom.app f.right ≫
          loopToHomotopyFiber.app f) :=
      (homotopyQuotient.map_comp (loopFunctor.map f.hom)
        (loopReversal.hom.app f.right ≫ loopToHomotopyFiber.app f)).symm
    _ = homotopyQuotient.map
        (const (loopFunctor.obj f.left) (homotopyFiberFunctor.obj f)) :=
      (homotopyQuotient_map_eq_iff _ _).2
        ((homotopyRel_iff _ _).1
          (loopMap_comp_loopReversal_comp_loopToHomotopyFiber_homotopyRel f))

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
