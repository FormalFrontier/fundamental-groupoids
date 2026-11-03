/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Fiber.Naturality
public import FundamentalGroupoids.CategoryTheory.Category.Pointed
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Data.ULift

/-!
# The pointed homotopy-fiber sequence

`HomotopyGroup.homotopyFiberSequence` is a chain complex of pointed types with
terms `πₙ B`, `πₙ E`, and `πₙ (HomotopyFiber f b)` in degrees `3n`, `3n + 1`,
and `3n + 2`, respectively. The fiber is based at its specified constant-path
point. The differentials are based postcomposition by `f`, fiber projection,
and the connecting function. The latter puts the last coordinate in forward
time: its representative retains the source point and the entire path
`t ↦ p (Fin.snoc a t)`. Strict based squares induce chain maps.

Carriers are lifted into one ambient universe without lifting the spaces or
rebuilding their homotopy groups. Source and base universes remain independent.
The degreewise maps of a strict based square likewise allow four independent
space universes.

## Implementation notes

Zero morphisms are the canonical constant pointed maps. This construction
asserts that adjacent differentials compose to zero, not exactness. In
particular, the terminal degree-zero term retains all path components of `B`;
the incoming differential need not be surjective. No group structure on path
components or commutativity of the fundamental group is used.

Only ordinary product, subspace and compact-open topologies are used. No
comparison with kified spaces, sphere-domain classes or signed connecting maps
is asserted.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8, §6,
  printed pp. 61–62, for the homotopy-fiber sequence context.
* Mathlib's generalized loops and homotopy groups, due to Roberto Alvarez,
  and its pointed types and fixed-endpoint paths.
* The based-postcomposition, coordinate-transport, loop-iteration,
  loop-inclusion and raw homotopy-fiber exactness APIs in this library.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology

section

universe v uX uY uE uB uE' uB'

namespace HomotopyGroup

private def lastCoordinateEquiv (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit :=
  (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm.trans
    (Equiv.sumCongr (Equiv.refl (Fin n)) finOneEquiv)

private theorem lastCoordinateEquiv_castSucc (n : ℕ) (i : Fin n) :
    lastCoordinateEquiv n i.castSucc = Sum.inl i := by
  simp [lastCoordinateEquiv]

private theorem lastCoordinateEquiv_last (n : ℕ) :
    lastCoordinateEquiv n (Fin.last n) = Sum.inr () := by
  simp [lastCoordinateEquiv]

private theorem lastCoordinateEquiv_snoc (n : ℕ)
    (a : Fin n → unitInterval) (t : unitInterval) :
    (fun i => Sum.elim a (fun _ : Unit => t) (lastCoordinateEquiv n i)) =
      Fin.snoc a t := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [lastCoordinateEquiv_last, Sum.elim_inr, Fin.snoc_last]
  · rw [lastCoordinateEquiv_castSucc, Sum.elim_inl, Fin.snoc_castSucc]

section Connecting

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]

-- This is the existing constant-Unit-fiber composite, not a new choice of inclusion.
private def fiberLoopInclusion (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    C(Path b b, ContinuousMap.HomotopyFiber f b) :=
  (ContinuousMap.HomotopyFiber.map
    (f := ContinuousMap.const Unit b) (f' := f) (b := b) (b' := b)
    (ContinuousMap.const Unit e₀) (ContinuousMap.id B) (fun _ => h) rfl).comp
      (((ContinuousMap.HomotopyFiber.constHomeomorph Unit b b).symm :
          C(Unit × Path b b,
            ContinuousMap.HomotopyFiber (ContinuousMap.const Unit b) b)).comp
        ((ContinuousMap.const (Path b b) ()).prodMk
          (ContinuousMap.id (Path b b))))

private theorem fiberLoopInclusion_refl
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    fiberLoopInclusion f b e₀ h (Path.refl b) =
      ContinuousMap.HomotopyFiber.const e₀ h :=
  ContinuousMap.HomotopyFiber.loopInclusion_apply e₀ h (Path.refl b)

private def finiteConnecting (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    HomotopyGroup (Fin (n + 1)) B b →
      HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
        (ContinuousMap.HomotopyFiber.const e₀ h) :=
  mapFun (Fin n) (fiberLoopInclusion f b e₀ h) (fiberLoopInclusion_refl f b e₀ h) ∘
    mapFun (Fin n) (genLoopHomeoOfUnique Unit b : C(GenLoop Unit B b, Path b b))
      (genLoopHomeoOfUnique_const Unit b) ∘
    (genLoopEquiv (Fin n) Unit b).symm ∘ congr b (lastCoordinateEquiv n)

/-- The finite-coordinate connecting representative in the ordinary homotopy fiber.
At each outer coordinate it retains `e₀` and the whole forward path obtained
by putting the final cube coordinate in the time slot. -/
@[no_expose]
def _root_.GenLoop.homotopyFiberConnecting (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (p : GenLoop (Fin (n + 1)) B b) :
    GenLoop (Fin n) (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h) :=
  GenLoop.map (fiberLoopInclusion f b e₀ h) (fiberLoopInclusion_refl f b e₀ h)
    (GenLoop.map (genLoopHomeoOfUnique Unit b : C(GenLoop Unit B b, Path b b))
      (genLoopHomeoOfUnique_const Unit b)
      ((GenLoop.genLoopGenLoopEquiv b (M := Fin n) (N := Unit)).symm
        (GenLoop.congr b (lastCoordinateEquiv n) p)))

private theorem finiteConnecting_class (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (p : GenLoop (Fin (n + 1)) B b) :
    finiteConnecting n f b e₀ h (⟦p⟧ : HomotopyGroup (Fin (n + 1)) B b) =
      (⟦GenLoop.homotopyFiberConnecting n f b e₀ h p⟧ :
        HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
          (ContinuousMap.HomotopyFiber.const e₀ h)) := by
  change mapFun (Fin n) (fiberLoopInclusion f b e₀ h)
      (fiberLoopInclusion_refl f b e₀ h)
      (mapFun (Fin n) (genLoopHomeoOfUnique Unit b : C(GenLoop Unit B b, Path b b))
        (genLoopHomeoOfUnique_const Unit b)
        ((genLoopEquiv (Fin n) Unit b).symm
          (congr b (lastCoordinateEquiv n)
            (⟦p⟧ : HomotopyGroup (Fin (n + 1)) B b)))) = _
  simp only [congr_class, genLoopEquiv_symm_class, mapFun_class,
    GenLoop.homotopyFiberConnecting]
  rfl

/-- The connecting representative retains the specified point of the total space. -/
@[simp]
theorem _root_.GenLoop.homotopyFiberConnecting_point (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (p : GenLoop (Fin (n + 1)) B b) (a : Fin n → unitInterval) :
    ContinuousMap.HomotopyFiber.point
      (GenLoop.homotopyFiberConnecting n f b e₀ h p a) = e₀ :=
  congrArg ContinuousMap.HomotopyFiber.point
    (ContinuousMap.HomotopyFiber.loopInclusion_apply e₀ h
      (genLoopHomeoOfUnique Unit b
        (((GenLoop.genLoopGenLoopEquiv b (M := Fin n) (N := Unit)).symm
          (GenLoop.congr b (lastCoordinateEquiv n) p)) a)))

/-- Every time value of the connecting representative is the original cube
with the final coordinate filled by that time, without reversal. -/
@[simp]
theorem _root_.GenLoop.homotopyFiberConnecting_path_apply (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (p : GenLoop (Fin (n + 1)) B b) (a : Fin n → unitInterval)
    (t : unitInterval) :
    ContinuousMap.HomotopyFiber.path
      (GenLoop.homotopyFiberConnecting n f b e₀ h p a) t = p (Fin.snoc a t) := by
  change p (fun i => Sum.elim a (fun _ : Unit => t) (lastCoordinateEquiv n i)) = _
  rw [lastCoordinateEquiv_snoc]

/-- The connecting representative of the constant cube is the constant cube
at the specified constant-path point of the fiber. -/
@[simp]
theorem _root_.GenLoop.homotopyFiberConnecting_const (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    GenLoop.homotopyFiberConnecting n f b e₀ h GenLoop.const = GenLoop.const := by
  apply GenLoop.ext
  intro a
  apply ContinuousMap.HomotopyFiber.ext
  · simpa only [GenLoop.const_apply, ContinuousMap.HomotopyFiber.point_const] using
      (GenLoop.homotopyFiberConnecting_point n f b e₀ h GenLoop.const a)
  · apply ContinuousMap.ext
    intro t
    simpa only [GenLoop.const_apply, ContinuousMap.HomotopyFiber.path_const,
      ContinuousMap.const_apply] using
      (GenLoop.homotopyFiberConnecting_path_apply n f b e₀ h GenLoop.const a t)

private theorem finiteConnecting_const (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    finiteConnecting n f b e₀ h
        (⟦GenLoop.const⟧ : HomotopyGroup (Fin (n + 1)) B b) =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n)
        (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h)) := by
  have hiter : (genLoopEquiv (Fin n) Unit b).symm
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n ⊕ Unit) B b) =
        (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) (GenLoop Unit B b) GenLoop.const) :=
    (genLoopEquiv (Fin n) Unit b).symm_apply_eq.mpr
      (genLoopEquiv_const (Fin n) Unit b).symm
  change mapFun (Fin n) (fiberLoopInclusion f b e₀ h)
      (fiberLoopInclusion_refl f b e₀ h)
      (mapFun (Fin n) (genLoopHomeoOfUnique Unit b : C(GenLoop Unit B b, Path b b))
        (genLoopHomeoOfUnique_const Unit b)
        ((genLoopEquiv (Fin n) Unit b).symm
          (congr b (lastCoordinateEquiv n)
            (⟦GenLoop.const⟧ : HomotopyGroup (Fin (n + 1)) B b)))) = _
  simp only [congr_const, hiter, mapFun_const]
  rfl

-- Only the image-to-preimage directions are used here, to compute the three
-- adjacent composites. These are not new exactness proofs.
private theorem projection_map_composite (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (a : HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h)) :
    mapFun (Fin n) f h
        (mapFun (Fin n) (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
          (ContinuousMap.HomotopyFiber.point_const e₀ h) a) =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) B b) :=
  (Set.ext_iff.mp (range_mapFun_homotopyFiber_point (Fin n) f b e₀ h) _).mp ⟨a, rfl⟩

private theorem connecting_projection_composite (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (a : HomotopyGroup (Fin (n + 1)) B b) :
    mapFun (Fin n) (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const e₀ h) (finiteConnecting n f b e₀ h a) =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) E e₀) := by
  apply (Set.ext_iff.mp (range_mapFun_homotopyFiber_loop (Fin n) f b e₀ h) _).mp
  exact ⟨_, rfl⟩

private theorem map_connecting_composite (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (a : HomotopyGroup (Fin (n + 1)) E e₀) :
    finiteConnecting n f b e₀ h (mapFun (Fin (n + 1)) f h a) =
      (⟦GenLoop.const⟧ : HomotopyGroup (Fin n)
        (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h)) := by
  apply (Set.ext_iff.mp
    (range_mapFun_eq_preimage_homotopyFiber_loop (Fin n) f b e₀ h) _).mp
  exact ⟨congr e₀ (lastCoordinateEquiv n) a,
    (congr_mapFun (lastCoordinateEquiv n) f h a).symm⟩

end Connecting

private def liftedHomotopy (n : ℕ) {X : Type uX} [TopologicalSpace X] (x : X) :
    Pointed.{max v uX} :=
  Pointed.of (ULift.up (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) X x) :
    ULift.{v} (HomotopyGroup (Fin n) X x))

private def liftedHomotopyMap (n : ℕ) {X : Type uX} {Y : Type uY}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (g : C(X, Y)) (hg : g x = y) :
    liftedHomotopy.{max v uX uY} n x ⟶ liftedHomotopy.{max v uX uY} n y where
  toFun := ULift.map (mapFun (Fin n) g hg)
  map_point := congrArg ULift.up (mapFun_const (Fin n) g hg)

private theorem liftedHomotopyMap_apply (n : ℕ) {X : Type uX} {Y : Type uY}
    [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
    (g : C(X, Y)) (hg : g x = y)
    (a : ULift.{max v uX uY} (HomotopyGroup (Fin n) X x)) :
    (liftedHomotopyMap.{v} n g hg).toFun a =
      ULift.up (mapFun (Fin n) g hg a.down) :=
  rfl

section Grading

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]

private def sequenceObject (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (k : ℕ) :
    Pointed.{max v uE uB} :=
  if k % 3 = 0 then liftedHomotopy.{max v uE uB} (k / 3) b
  else if k % 3 = 1 then liftedHomotopy.{max v uE uB} (k / 3) e₀
  else liftedHomotopy.{max v uE uB} (k / 3) (ContinuousMap.HomotopyFiber.const e₀ h)

private theorem sequenceObject_base (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) (n : ℕ) :
    sequenceObject.{v} f b e₀ h (3 * n) = liftedHomotopy.{max v uE uB} n b := by
  have hm : (3 * n) % 3 = 0 := by omega
  have hd : (3 * n) / 3 = n := by omega
  simp [sequenceObject, hm, hd]

private theorem sequenceObject_total (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) (n : ℕ) :
    sequenceObject.{v} f b e₀ h (3 * n + 1) =
      liftedHomotopy.{max v uE uB} n e₀ := by
  have hm : (3 * n + 1) % 3 = 1 := by omega
  have hd : (3 * n + 1) / 3 = n := by omega
  simp [sequenceObject, hm, hd]

private theorem sequenceObject_fiber (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) (n : ℕ) :
    sequenceObject.{v} f b e₀ h (3 * n + 2) =
      liftedHomotopy.{max v uE uB} n (ContinuousMap.HomotopyFiber.const e₀ h) := by
  have hm : (3 * n + 2) % 3 = 2 := by omega
  have hd : (3 * n + 2) / 3 = n := by omega
  simp [sequenceObject, hm, hd]

private def liftedConnecting (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    liftedHomotopy.{max v uE uB} (n + 1) b ⟶
      liftedHomotopy.{max v uE uB} n (ContinuousMap.HomotopyFiber.const e₀ h) where
  toFun := ULift.map (finiteConnecting n f b e₀ h)
  map_point := congrArg ULift.up (finiteConnecting_const n f b e₀ h)

private def sequenceDifferential (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (k : ℕ) : sequenceObject.{v} f b e₀ h (k + 1) ⟶ sequenceObject.{v} f b e₀ h k := by
  by_cases h0 : k % 3 = 0
  · have hm : (k + 1) % 3 = 1 := by omega
    have hd : (k + 1) / 3 = k / 3 := by omega
    simpa [sequenceObject, h0, hm, hd] using
      (liftedHomotopyMap.{max v uE uB} (k / 3) f h)
  · by_cases h1 : k % 3 = 1
    · have hm : (k + 1) % 3 = 2 := by omega
      have hd : (k + 1) / 3 = k / 3 := by omega
      simpa [sequenceObject, h0, h1, hm, hd] using
        (liftedHomotopyMap.{max v uE uB} (k / 3)
          (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
          (ContinuousMap.HomotopyFiber.point_const e₀ h))
    · have h2 : k % 3 = 2 := by omega
      have hm : (k + 1) % 3 = 0 := by omega
      have hd : (k + 1) / 3 = k / 3 + 1 := by omega
      simpa [sequenceObject, h0, h1, h2, hm, hd] using
        (liftedConnecting.{v} (k / 3) f b e₀ h)

private theorem liftedConnecting_apply (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (a : ULift.{max v uE uB} (HomotopyGroup (Fin (n + 1)) B b)) :
    (liftedConnecting.{v} n f b e₀ h).toFun a =
      ULift.up (finiteConnecting n f b e₀ h a.down) :=
  rfl

-- Changing the grade changes both ends of an arrow. Eliminate the grade
-- equality before comparing the dependent morphisms.
private theorem liftedHomotopyMap_grade_heq (m n : ℕ)
    {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (g : C(X, Y)) (hg : g x = y) (hmn : m = n) :
    HEq (liftedHomotopyMap.{v} m g hg) (liftedHomotopyMap.{v} n g hg) := by
  subst n
  rfl

private theorem liftedConnecting_grade_heq (m n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (hmn : m = n) :
    HEq (liftedConnecting.{v} m f b e₀ h) (liftedConnecting.{v} n f b e₀ h) := by
  subst n
  rfl

-- The characteristic arrows are stated heterogeneously so that their source
-- and target grades can be identified explicitly when composing them.
private theorem sequenceDifferential_base_heq
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (n : ℕ) :
    HEq (sequenceDifferential.{v} f b e₀ h (3 * n))
      (liftedHomotopyMap.{max v uE uB} n f h) := by
  have hm : (3 * n) % 3 = 0 := by omega
  have hd : (3 * n) / 3 = n := by omega
  simpa [sequenceDifferential, hm] using
    (liftedHomotopyMap_grade_heq.{max v uE uB} ((3 * n) / 3) n f h hd)

private theorem sequenceDifferential_total_heq
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (n : ℕ) :
    HEq (sequenceDifferential.{v} f b e₀ h (3 * n + 1))
      (liftedHomotopyMap.{max v uE uB} n
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const e₀ h)) := by
  have hm : (3 * n + 1) % 3 = 1 := by omega
  have hd : (3 * n + 1) / 3 = n := by omega
  simpa [sequenceDifferential, hm] using
    (liftedHomotopyMap_grade_heq.{max v uE uB} ((3 * n + 1) / 3) n
      (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
      (ContinuousMap.HomotopyFiber.point_const e₀ h) hd)

private theorem sequenceDifferential_fiber_heq
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (n : ℕ) :
    HEq (sequenceDifferential.{v} f b e₀ h (3 * n + 2))
      (liftedConnecting.{v} n f b e₀ h) := by
  have hm : (3 * n + 2) % 3 = 2 := by omega
  have hd : (3 * n + 2) / 3 = n := by omega
  simpa [sequenceDifferential, hm] using
    (liftedConnecting_grade_heq.{v} ((3 * n + 2) / 3) n f b e₀ h hd)

-- Compute the composites on their characteristic carriers, before transporting
-- them to sequence grades. No categorical zero morphism is needed.
private theorem lifted_projection_map_composite (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (a : ULift.{max v uE uB} (HomotopyGroup (Fin n)
      (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h))) :
    (liftedHomotopyMap.{max v uE uB} n f h).toFun
        ((liftedHomotopyMap.{max v uE uB} n
          (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
          (ContinuousMap.HomotopyFiber.point_const e₀ h)).toFun a) =
      (liftedHomotopy.{max v uE uB} n b).point := by
  change ULift.up (mapFun (Fin n) f h
      (mapFun (Fin n) (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const e₀ h) a.down)) =
    ULift.up (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) B b)
  exact congrArg ULift.up (projection_map_composite n f b e₀ h a.down)

private theorem lifted_connecting_projection_composite (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (a : ULift.{max v uE uB} (HomotopyGroup (Fin (n + 1)) B b)) :
    (liftedHomotopyMap.{max v uE uB} n
        (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const e₀ h)).toFun
        ((liftedConnecting.{v} n f b e₀ h).toFun a) =
      (liftedHomotopy.{max v uE uB} n e₀).point := by
  change ULift.up
      (mapFun (Fin n) (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const e₀ h)
        (finiteConnecting n f b e₀ h a.down)) =
    ULift.up (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) E e₀)
  exact congrArg ULift.up (connecting_projection_composite n f b e₀ h a.down)

private theorem lifted_map_connecting_composite (n : ℕ)
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (a : ULift.{max v uE uB} (HomotopyGroup (Fin (n + 1)) E e₀)) :
    (liftedConnecting.{v} n f b e₀ h).toFun
        ((liftedHomotopyMap.{max v uE uB} (n + 1) f h).toFun a) =
      (liftedHomotopy.{max v uE uB} n (ContinuousMap.HomotopyFiber.const e₀ h)).point := by
  change ULift.up (finiteConnecting n f b e₀ h
      (mapFun (Fin (n + 1)) f h a.down)) =
    ULift.up (⟦GenLoop.const⟧ : HomotopyGroup (Fin n)
      (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h))
  exact congrArg ULift.up (map_connecting_composite n f b e₀ h a.down)

/-- Every adjacent composite sends each element to the target's distinguished point. -/
private theorem sequenceDifferential_comp_apply
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) (k : ℕ)
    (a : sequenceObject.{v} f b e₀ h (k + 2)) :
    (sequenceDifferential.{v} f b e₀ h k).toFun
        ((sequenceDifferential.{v} f b e₀ h (k + 1)).toFun a) =
      (sequenceObject.{v} f b e₀ h k).point := by
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n := ⟨k / 3, by omega⟩
    have p0 := sequenceObject_base.{v} f b e₀ h n
    have p1 := sequenceObject_total.{v} f b e₀ h n
    have p2 := sequenceObject_fiber.{v} f b e₀ h n
    have hcomp :
        sequenceDifferential.{v} f b e₀ h (3 * n + 1) ≫
            sequenceDifferential.{v} f b e₀ h (3 * n) =
          eqToHom p2 ≫
            (liftedHomotopyMap.{max v uE uB} n
                (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
                (ContinuousMap.HomotopyFiber.point_const e₀ h) ≫
              liftedHomotopyMap.{max v uE uB} n f h) ≫ eqToHom p0.symm :=
      (conj_eqToHom_iff_heq _ _ p2 p0).mpr
        (heq_comp p2 p1 p0 (sequenceDifferential_total_heq.{v} f b e₀ h n)
          (sequenceDifferential_base_heq.{v} f b e₀ h n))
    change (sequenceDifferential.{v} f b e₀ h (3 * n + 1) ≫
      sequenceDifferential.{v} f b e₀ h (3 * n)).toFun a = _
    rw [hcomp]
    simpa only [Pointed.Hom.comp_toFun', Function.comp_apply] using
      (congrArg (eqToHom p0.symm).toFun
        (lifted_projection_map_composite.{v} n f b e₀ h ((eqToHom p2).toFun a))).trans
          (eqToHom p0.symm).map_point
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n + 1 := ⟨k / 3, by omega⟩
    have p0 := sequenceObject_total.{v} f b e₀ h n
    have p1 := sequenceObject_fiber.{v} f b e₀ h n
    have p2 := sequenceObject_base.{v} f b e₀ h (n + 1)
    have hcomp :
        sequenceDifferential.{v} f b e₀ h (3 * n + 2) ≫
            sequenceDifferential.{v} f b e₀ h (3 * n + 1) =
          eqToHom p2 ≫
            (liftedConnecting.{v} n f b e₀ h ≫
              liftedHomotopyMap.{max v uE uB} n
                (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
                (ContinuousMap.HomotopyFiber.point_const e₀ h)) ≫ eqToHom p0.symm :=
      (conj_eqToHom_iff_heq _ _ p2 p0).mpr
        (heq_comp p2 p1 p0 (sequenceDifferential_fiber_heq.{v} f b e₀ h n)
          (sequenceDifferential_total_heq.{v} f b e₀ h n))
    change (sequenceDifferential.{v} f b e₀ h (3 * n + 2) ≫
      sequenceDifferential.{v} f b e₀ h (3 * n + 1)).toFun a = _
    rw [hcomp]
    simpa only [Pointed.Hom.comp_toFun', Function.comp_apply] using
      (congrArg (eqToHom p0.symm).toFun
        (lifted_connecting_projection_composite.{v} n f b e₀ h
          ((eqToHom p2).toFun a))).trans (eqToHom p0.symm).map_point
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n + 2 := ⟨k / 3, by omega⟩
    have p0 := sequenceObject_fiber.{v} f b e₀ h n
    have p1 := sequenceObject_base.{v} f b e₀ h (n + 1)
    have p2 := sequenceObject_total.{v} f b e₀ h (n + 1)
    have hcomp :
        sequenceDifferential.{v} f b e₀ h (3 * n + 3) ≫
            sequenceDifferential.{v} f b e₀ h (3 * n + 2) =
          eqToHom p2 ≫
            (liftedHomotopyMap.{max v uE uB} (n + 1) f h ≫
              liftedConnecting.{v} n f b e₀ h) ≫ eqToHom p0.symm :=
      (conj_eqToHom_iff_heq _ _ p2 p0).mpr
        (heq_comp p2 p1 p0 (sequenceDifferential_base_heq.{v} f b e₀ h (n + 1))
          (sequenceDifferential_fiber_heq.{v} f b e₀ h n))
    change (sequenceDifferential.{v} f b e₀ h (3 * n + 3) ≫
      sequenceDifferential.{v} f b e₀ h (3 * n + 2)).toFun a = _
    rw [hcomp]
    simpa only [Pointed.Hom.comp_toFun', Function.comp_apply] using
      (congrArg (eqToHom p0.symm).toFun
        (lifted_map_connecting_composite.{v} n f b e₀ h ((eqToHom p2).toFun a))).trans
          (eqToHom p0.symm).map_point

end Grading

section Square

variable {E : Type uE} {B : Type uB} {E' : Type uE'} {B' : Type uB'}
variable [TopologicalSpace E] [TopologicalSpace B]
variable [TopologicalSpace E'] [TopologicalSpace B']
variable {f : C(E, B)} {f' : C(E', B')}

private theorem finiteConnecting_naturality (n : ℕ)
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (a : HomotopyGroup (Fin (n + 1)) B b) :
    mapFun (Fin n) (ContinuousMap.HomotopyFiber.map α β w hb)
        (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he)
        (finiteConnecting n f b e₀ h a) =
      finiteConnecting n f' b' e₀' h' (mapFun (Fin (n + 1)) β hb a) := by
  have hnat := congrFun
    (mapFun_homotopyFiber_loop_naturality (Fin n) α β w e₀ e₀' h h' he hb)
    (congr b (lastCoordinateEquiv n) a)
  simpa only [finiteConnecting, Function.comp_apply, congr_mapFun, fiberLoopInclusion] using hnat

private def sequenceSquareComponent
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (k : ℕ) :
    sequenceObject.{max v uE uB uE' uB'} f b e₀ h k ⟶
      sequenceObject.{max v uE uB uE' uB'} f' b' e₀' h' k := by
  by_cases h0 : k % 3 = 0
  · simpa [sequenceObject, h0] using
      (liftedHomotopyMap.{max v uE uB uE' uB'} (k / 3) β hb)
  · by_cases h1 : k % 3 = 1
    · simpa [sequenceObject, h0, h1] using
        (liftedHomotopyMap.{max v uE uB uE' uB'} (k / 3) α he)
    · simpa [sequenceObject, h0, h1] using
        (liftedHomotopyMap.{max v uE uB uE' uB'} (k / 3)
          (ContinuousMap.HomotopyFiber.map α β w hb)
          (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he))

private theorem mapFun_square_comm (n : ℕ)
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (a : HomotopyGroup (Fin n) E e₀) :
    mapFun (Fin n) f' h' (mapFun (Fin n) α he a) =
      mapFun (Fin n) β hb (mapFun (Fin n) f h a) := by
  have hw : f'.comp α = β.comp f := by
    apply ContinuousMap.ext
    intro e
    exact w e
  have hmaps := mapFun_congr (Fin n) (x := e₀) (y := b') hw
    ((congrArg f' he).trans h') ((congrArg β h).trans hb)
  rw [mapFun_comp (Fin n) f' h' α he,
    mapFun_comp (Fin n) β hb f h] at hmaps
  exact congrFun hmaps a

private theorem mapFun_homotopyFiber_point_square_comm (n : ℕ)
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b')
    (a : HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
      (ContinuousMap.HomotopyFiber.const e₀ h)) :
    mapFun (Fin n) (ContinuousMap.HomotopyFiber.point (f := f') (b := b'))
        (ContinuousMap.HomotopyFiber.point_const e₀' h')
        (mapFun (Fin n) (ContinuousMap.HomotopyFiber.map α β w hb)
          (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he) a) =
      mapFun (Fin n) α he
        (mapFun (Fin n) (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
          (ContinuousMap.HomotopyFiber.point_const e₀ h) a) := by
  have hw :
      (ContinuousMap.HomotopyFiber.point (f := f') (b := b')).comp
          (ContinuousMap.HomotopyFiber.map α β w hb) =
        α.comp (ContinuousMap.HomotopyFiber.point (f := f) (b := b)) := by
    apply ContinuousMap.ext
    intro z
    exact ContinuousMap.HomotopyFiber.point_map
      (f := f) (f' := f') (b := b) (b' := b') α β w hb z
  have hmaps := mapFun_congr (Fin n)
    (x := ContinuousMap.HomotopyFiber.const e₀ h) (y := e₀') hw
    ((congrArg (ContinuousMap.HomotopyFiber.point (f := f') (b := b'))
      (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he)).trans
        (ContinuousMap.HomotopyFiber.point_const e₀' h'))
    ((congrArg α (ContinuousMap.HomotopyFiber.point_const e₀ h)).trans he)
  rw [mapFun_comp (Fin n)
      (ContinuousMap.HomotopyFiber.point (f := f') (b := b'))
      (ContinuousMap.HomotopyFiber.point_const e₀' h')
      (ContinuousMap.HomotopyFiber.map α β w hb)
      (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he),
    mapFun_comp (Fin n) α he
      (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
      (ContinuousMap.HomotopyFiber.point_const e₀ h)] at hmaps
  exact congrFun hmaps a

-- Normalize the degree separately: it changes both endpoints of the morphism.
private theorem sequenceSquareComponent_base_heq
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (n : ℕ) :
    HEq (sequenceSquareComponent.{v} α β w b b' e₀ e₀' h h' he hb (3 * n))
      (liftedHomotopyMap.{max v uE uB uE' uB'} n β hb) := by
  have hm : (3 * n) % 3 = 0 := by omega
  have hd : (3 * n) / 3 = n := by omega
  have hdegree (m : ℕ) (hmn : m = n) :
      HEq (liftedHomotopyMap.{max v uE uB uE' uB'} m β hb)
        (liftedHomotopyMap.{max v uE uB uE' uB'} n β hb) := by
    subst m
    rfl
  refine HEq.trans ?_ (hdegree _ hd)
  simp [sequenceSquareComponent, hm]

private theorem sequenceSquareComponent_total_heq
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (n : ℕ) :
    HEq (sequenceSquareComponent.{v} α β w b b' e₀ e₀' h h' he hb (3 * n + 1))
      (liftedHomotopyMap.{max v uE uB uE' uB'} n α he) := by
  have hm : (3 * n + 1) % 3 = 1 := by omega
  have hd : (3 * n + 1) / 3 = n := by omega
  have hdegree (m : ℕ) (hmn : m = n) :
      HEq (liftedHomotopyMap.{max v uE uB uE' uB'} m α he)
        (liftedHomotopyMap.{max v uE uB uE' uB'} n α he) := by
    subst m
    rfl
  refine HEq.trans ?_ (hdegree _ hd)
  simp [sequenceSquareComponent, hm]

private theorem sequenceSquareComponent_fiber_heq
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (n : ℕ) :
    HEq (sequenceSquareComponent.{v} α β w b b' e₀ e₀' h h' he hb (3 * n + 2))
      (liftedHomotopyMap.{max v uE uB uE' uB'} n
        (ContinuousMap.HomotopyFiber.map α β w hb)
        (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he)) := by
  have hm : (3 * n + 2) % 3 = 2 := by omega
  have hd : (3 * n + 2) / 3 = n := by omega
  have hdegree (m : ℕ) (hmn : m = n) :
      HEq (liftedHomotopyMap.{max v uE uB uE' uB'} m
          (ContinuousMap.HomotopyFiber.map α β w hb)
          (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he))
        (liftedHomotopyMap.{max v uE uB uE' uB'} n
          (ContinuousMap.HomotopyFiber.map α β w hb)
          (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he)) := by
    subst m
    rfl
  refine HEq.trans ?_ (hdegree _ hd)
  simp [sequenceSquareComponent, hm]

/-- The components of a strict based square commute pointwise with every differential. -/
private theorem sequenceSquareComponent_comm
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (k : ℕ)
    (a : sequenceObject.{max v uE uB uE' uB'} f b e₀ h (k + 1)) :
    (sequenceDifferential.{max v uE uB uE' uB'} f' b' e₀' h' k).toFun
        ((sequenceSquareComponent.{v} α β w b b' e₀ e₀' h h' he hb (k + 1)).toFun a) =
      (sequenceSquareComponent.{v} α β w b b' e₀ e₀' h h' he hb k).toFun
        ((sequenceDifferential.{max v uE uB uE' uB'} f b e₀ h k).toFun a) := by
  -- Compare the pointed morphisms before evaluating at the dependent carrier.
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n := ⟨k / 3, by omega⟩
    have hraw :
        liftedHomotopyMap.{max v uE uB uE' uB'} n α he ≫
            liftedHomotopyMap.{max v uE uB uE' uB'} n f' h' =
          liftedHomotopyMap.{max v uE uB uE' uB'} n f h ≫
            liftedHomotopyMap.{max v uE uB uE' uB'} n β hb := by
      apply Pointed.Hom.ext
      exact funext fun (x : ULift.{max v uE uB uE' uB'}
          (HomotopyGroup (Fin n) E e₀)) =>
        congrArg ULift.up (mapFun_square_comm n α β w b b' e₀ e₀' h h' he hb x.down)
    have hleft := heq_comp
      (sequenceObject_total.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceObject_total.{max v uE uB uE' uB'} f' b' e₀' h' n)
      (sequenceObject_base.{max v uE uB uE' uB'} f' b' e₀' h' n)
      (sequenceSquareComponent_total_heq.{v} α β w b b' e₀ e₀' h h' he hb n)
      (sequenceDifferential_base_heq.{max v uE uB uE' uB'} f' b' e₀' h' n)
    have hright := heq_comp
      (sequenceObject_total.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceObject_base.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceObject_base.{max v uE uB uE' uB'} f' b' e₀' h' n)
      (sequenceDifferential_base_heq.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceSquareComponent_base_heq.{v} α β w b b' e₀ e₀' h h' he hb n)
    have hcomm := eq_of_heq (hleft.trans ((heq_of_eq hraw).trans hright.symm))
    exact congrFun (congrArg Pointed.Hom.toFun hcomm) a
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n + 1 := ⟨k / 3, by omega⟩
    have hraw :
        liftedHomotopyMap.{max v uE uB uE' uB'} n
              (ContinuousMap.HomotopyFiber.map α β w hb)
              (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he) ≫
            liftedHomotopyMap.{max v uE uB uE' uB'} n
              (ContinuousMap.HomotopyFiber.point (f := f') (b := b'))
              (ContinuousMap.HomotopyFiber.point_const e₀' h') =
          liftedHomotopyMap.{max v uE uB uE' uB'} n
              (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
              (ContinuousMap.HomotopyFiber.point_const e₀ h) ≫
            liftedHomotopyMap.{max v uE uB uE' uB'} n α he := by
      apply Pointed.Hom.ext
      exact funext fun (x : ULift.{max v uE uB uE' uB'}
          (HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
            (ContinuousMap.HomotopyFiber.const e₀ h))) =>
        congrArg ULift.up
          (mapFun_homotopyFiber_point_square_comm n α β w b b' e₀ e₀' h h' he hb x.down)
    have hleft := heq_comp
      (sequenceObject_fiber.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceObject_fiber.{max v uE uB uE' uB'} f' b' e₀' h' n)
      (sequenceObject_total.{max v uE uB uE' uB'} f' b' e₀' h' n)
      (sequenceSquareComponent_fiber_heq.{v} α β w b b' e₀ e₀' h h' he hb n)
      (sequenceDifferential_total_heq.{max v uE uB uE' uB'} f' b' e₀' h' n)
    have hright := heq_comp
      (sequenceObject_fiber.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceObject_total.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceObject_total.{max v uE uB uE' uB'} f' b' e₀' h' n)
      (sequenceDifferential_total_heq.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceSquareComponent_total_heq.{v} α β w b b' e₀ e₀' h h' he hb n)
    have hcomm := eq_of_heq (hleft.trans ((heq_of_eq hraw).trans hright.symm))
    exact congrFun (congrArg Pointed.Hom.toFun hcomm) a
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n + 2 := ⟨k / 3, by omega⟩
    have hraw :
        liftedHomotopyMap.{max v uE uB uE' uB'} (n + 1) β hb ≫
            liftedConnecting.{max v uE uB uE' uB'} n f' b' e₀' h' =
          liftedConnecting.{max v uE uB uE' uB'} n f b e₀ h ≫
            liftedHomotopyMap.{max v uE uB uE' uB'} n
              (ContinuousMap.HomotopyFiber.map α β w hb)
              (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he) := by
      apply Pointed.Hom.ext
      exact funext fun (x : ULift.{max v uE uB uE' uB'}
          (HomotopyGroup (Fin (n + 1)) B b)) =>
        congrArg ULift.up
          (finiteConnecting_naturality n α β w b b' e₀ e₀' h h' he hb x.down).symm
    have hleft := heq_comp
      (sequenceObject_base.{max v uE uB uE' uB'} f b e₀ h (n + 1))
      (sequenceObject_base.{max v uE uB uE' uB'} f' b' e₀' h' (n + 1))
      (sequenceObject_fiber.{max v uE uB uE' uB'} f' b' e₀' h' n)
      (sequenceSquareComponent_base_heq.{v} α β w b b' e₀ e₀' h h' he hb (n + 1))
      (sequenceDifferential_fiber_heq.{max v uE uB uE' uB'} f' b' e₀' h' n)
    have hright := heq_comp
      (sequenceObject_base.{max v uE uB uE' uB'} f b e₀ h (n + 1))
      (sequenceObject_fiber.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceObject_fiber.{max v uE uB uE' uB'} f' b' e₀' h' n)
      (sequenceDifferential_fiber_heq.{max v uE uB uE' uB'} f b e₀ h n)
      (sequenceSquareComponent_fiber_heq.{v} α β w b b' e₀ e₀' h h' he hb n)
    have hcomm := eq_of_heq (hleft.trans ((heq_of_eq hraw).trans hright.symm))
    exact congrFun (congrArg Pointed.Hom.toFun hcomm) a

end Square

end HomotopyGroup

end

namespace HomotopyGroup

/-- The homotopy-fiber sequence as a chain complex of pointed types. The terms
in degrees `3n`, `3n + 1`, and `3n + 2` are the lifted homotopy quotients of
`B`, `E`, and the ordinary homotopy fiber, respectively. The connecting map
uses the final cube coordinate in forward time. The auxiliary lift universe
is the first universe parameter. -/
@[no_expose]
def homotopyFiberSequence.{v, uE, uB}
    {E : Type uE} {B : Type uB} [TopologicalSpace E] [TopologicalSpace B]
    (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    ChainComplex Pointed.{max v uE uB} ℕ :=
  ChainComplex.of (sequenceObject.{v} f b e₀ h) (sequenceDifferential.{v} f b e₀ h)
    (fun k => (Pointed.comp_eq_zero_iff _ _).mpr
      (sequenceDifferential_comp_apply.{v} f b e₀ h k))

/-- A strict continuous square preserving the specified points induces a chain
map of homotopy-fiber sequences. All four space universes are independent;
both complexes use their common ambient lift universe. The auxiliary lift
universe is the first universe parameter. -/
@[no_expose]
def homotopyFiberSequenceMap.{v, uE, uB, uE', uB'}
    {E : Type uE} {B : Type uB} {E' : Type uE'} {B' : Type uB'}
    [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace E'] [TopologicalSpace B'] {f : C(E, B)} {f' : C(E', B')}
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') :
    homotopyFiberSequence.{max v uE uB uE' uB'} f b e₀ h ⟶
      homotopyFiberSequence.{max v uE uB uE' uB'} f' b' e₀' h' :=
  ChainComplex.ofHom
    (sequenceSquareComponent.{v} α β w b b' e₀ e₀' h h' he hb)
    (fun k => by
      simp only [homotopyFiberSequence, ChainComplex.of_d]
      apply Pointed.Hom.ext
      exact funext (sequenceSquareComponent_comm.{v} α β w b b' e₀ e₀' h h' he hb k))

section Characteristics

universe v uE uB uE' uB'

variable {E : Type uE} {B : Type uB}
variable [TopologicalSpace E] [TopologicalSpace B]

/-- The term in degree `3n` is the lifted homotopy quotient of the base. -/
@[no_expose]
def homotopyFiberSequenceBaseIso (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (n : ℕ) :
    (homotopyFiberSequence.{v} f b e₀ h).X (3 * n) ≅
      Pointed.of (ULift.up (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) B b) :
        ULift.{max v uE uB} (HomotopyGroup (Fin n) B b)) :=
  eqToIso (sequenceObject_base.{v} f b e₀ h n)

/-- The term in degree `3n + 1` is the lifted homotopy quotient of the total space. -/
@[no_expose]
def homotopyFiberSequenceTotalIso (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (n : ℕ) :
    (homotopyFiberSequence.{v} f b e₀ h).X (3 * n + 1) ≅
      Pointed.of (ULift.up (⟦GenLoop.const⟧ : HomotopyGroup (Fin n) E e₀) :
        ULift.{max v uE uB} (HomotopyGroup (Fin n) E e₀)) :=
  eqToIso (sequenceObject_total.{v} f b e₀ h n)

/-- The term in degree `3n + 2` is the lifted homotopy quotient of the fiber,
based at its specified constant-path point. -/
@[no_expose]
def homotopyFiberSequenceFiberIso (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b)
    (n : ℕ) :
    (homotopyFiberSequence.{v} f b e₀ h).X (3 * n + 2) ≅
      Pointed.of (ULift.up (⟦GenLoop.const⟧ : HomotopyGroup (Fin n)
        (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h)) :
        ULift.{max v uE uB} (HomotopyGroup (Fin n)
          (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h))) :=
  eqToIso (sequenceObject_fiber.{v} f b e₀ h n)

private theorem pointed_conjugate_apply {W X Y Z : Pointed.{v}}
    (p : W = Y) (q : X = Z) (f : W ⟶ X) (g : Y ⟶ Z) (hfg : HEq f g) (a : Y) :
    (eqToHom q).toFun (f.toFun ((eqToHom p.symm).toFun a)) = g.toFun a := by
  have hf := (conj_eqToHom_iff_heq f g p q).mpr hfg
  have hc : eqToHom p.symm ≫ f ≫ eqToHom q = g := by
    rw [hf]
    simp
  exact congrFun (congrArg Pointed.Hom.toFun hc) a

private theorem homotopyFiberSequence_d_heq (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) (i j : ℕ) (hij : i = j + 1) :
    HEq ((homotopyFiberSequence.{v} f b e₀ h).d i j)
      (sequenceDifferential.{v} f b e₀ h j) := by
  subst i
  exact heq_of_eq (ChainComplex.of_d (sequenceObject.{v} f b e₀ h)
    (sequenceDifferential.{v} f b e₀ h) j)

/-- Under the term identifications, the differential from total space to base
is based postcomposition by `f`, on every homotopy class. -/
theorem homotopyFiberSequence_d_base_apply (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) (n : ℕ)
    (a : ULift.{max v uE uB} (HomotopyGroup (Fin n) E e₀)) :
    (homotopyFiberSequenceBaseIso.{v} f b e₀ h n).hom.toFun
        ((homotopyFiberSequence.{v} f b e₀ h).d (3 * n + 1) (3 * n)
          ((homotopyFiberSequenceTotalIso.{v} f b e₀ h n).inv.toFun a)) =
      ULift.up (mapFun (Fin n) f h a.down) := by
  exact pointed_conjugate_apply
    (sequenceObject_total.{v} f b e₀ h n) (sequenceObject_base.{v} f b e₀ h n) _ _
    ((homotopyFiberSequence_d_heq.{v} f b e₀ h (3 * n + 1) (3 * n) rfl).trans
      (sequenceDifferential_base_heq.{v} f b e₀ h n)) a

/-- Under the term identifications, the differential from fiber to total space
is based postcomposition by fiber projection, on every homotopy class. -/
theorem homotopyFiberSequence_d_total_apply (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) (n : ℕ)
    (a : ULift.{max v uE uB} (HomotopyGroup (Fin n)
      (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h))) :
    (homotopyFiberSequenceTotalIso.{v} f b e₀ h n).hom.toFun
        ((homotopyFiberSequence.{v} f b e₀ h).d (3 * n + 2) (3 * n + 1)
          ((homotopyFiberSequenceFiberIso.{v} f b e₀ h n).inv.toFun a)) =
      ULift.up (mapFun (Fin n) (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const e₀ h) a.down) := by
  exact pointed_conjugate_apply
    (sequenceObject_fiber.{v} f b e₀ h n) (sequenceObject_total.{v} f b e₀ h n) _ _
    ((homotopyFiberSequence_d_heq.{v} f b e₀ h (3 * n + 2) (3 * n + 1) rfl).trans
      (sequenceDifferential_total_heq.{v} f b e₀ h n)) a

/-- The connecting differential takes a representative cube to the class of
its forward connecting representative, retaining the entire path at every
outer coordinate. -/
theorem homotopyFiberSequence_d_fiber_class (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) (n : ℕ) (p : GenLoop (Fin (n + 1)) B b) :
    (homotopyFiberSequenceFiberIso.{v} f b e₀ h n).hom.toFun
        ((homotopyFiberSequence.{v} f b e₀ h).d (3 * (n + 1)) (3 * n + 2)
          ((homotopyFiberSequenceBaseIso.{v} f b e₀ h (n + 1)).inv.toFun
            (ULift.up (⟦p⟧ : HomotopyGroup (Fin (n + 1)) B b)))) =
      ULift.up (⟦GenLoop.homotopyFiberConnecting n f b e₀ h p⟧ :
        HomotopyGroup (Fin n) (ContinuousMap.HomotopyFiber f b)
          (ContinuousMap.HomotopyFiber.const e₀ h)) := by
  have hd := pointed_conjugate_apply
    (sequenceObject_base.{v} f b e₀ h (n + 1)) (sequenceObject_fiber.{v} f b e₀ h n) _ _
    ((homotopyFiberSequence_d_heq.{v} f b e₀ h (3 * (n + 1)) (3 * n + 2)
        (by omega)).trans (sequenceDifferential_fiber_heq.{v} f b e₀ h n))
    (ULift.up (⟦p⟧ : HomotopyGroup (Fin (n + 1)) B b))
  exact hd.trans (congrArg ULift.up (finiteConnecting_class n f b e₀ h p))

/-- Postcomposition by `f` computes the total-to-base differential on cube classes. -/
theorem homotopyFiberSequence_d_base_class (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) (n : ℕ) (p : GenLoop (Fin n) E e₀) :
    (homotopyFiberSequenceBaseIso.{v} f b e₀ h n).hom.toFun
        ((homotopyFiberSequence.{v} f b e₀ h).d (3 * n + 1) (3 * n)
          ((homotopyFiberSequenceTotalIso.{v} f b e₀ h n).inv.toFun
            (ULift.up (⟦p⟧ : HomotopyGroup (Fin n) E e₀)))) =
      ULift.up (⟦GenLoop.map f h p⟧ : HomotopyGroup (Fin n) B b) :=
  homotopyFiberSequence_d_base_apply.{v} f b e₀ h n (ULift.up ⟦p⟧)

/-- Fiber projection computes the fiber-to-total differential on cube classes. -/
theorem homotopyFiberSequence_d_total_class (f : C(E, B)) (b : B) (e₀ : E)
    (h : f e₀ = b) (n : ℕ) (p : GenLoop (Fin n)
      (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h)) :
    (homotopyFiberSequenceTotalIso.{v} f b e₀ h n).hom.toFun
        ((homotopyFiberSequence.{v} f b e₀ h).d (3 * n + 2) (3 * n + 1)
          ((homotopyFiberSequenceFiberIso.{v} f b e₀ h n).inv.toFun
            (ULift.up (⟦p⟧ : HomotopyGroup (Fin n)
              (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h))))) =
      ULift.up (⟦GenLoop.map (ContinuousMap.HomotopyFiber.point (f := f) (b := b))
        (ContinuousMap.HomotopyFiber.point_const e₀ h) p⟧ : HomotopyGroup (Fin n) E e₀) :=
  homotopyFiberSequence_d_total_apply.{v} f b e₀ h n (ULift.up ⟦p⟧)

section Square

variable {E' : Type uE'} {B' : Type uB'} [TopologicalSpace E'] [TopologicalSpace B']
variable {f : C(E, B)} {f' : C(E', B')}

/-- The base component of the chain map is postcomposition by the base-space map. -/
theorem homotopyFiberSequenceMap_base_apply
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (n : ℕ)
    (a : ULift.{max v uE uB uE' uB'} (HomotopyGroup (Fin n) B b)) :
    (homotopyFiberSequenceBaseIso.{max v uE uB uE' uB'} f' b' e₀' h' n).hom.toFun
        (((homotopyFiberSequenceMap.{v} α β w b b' e₀ e₀' h h' he hb).f (3 * n)).toFun
          ((homotopyFiberSequenceBaseIso.{max v uE uB uE' uB'} f b e₀ h n).inv.toFun a)) =
      ULift.up (mapFun (Fin n) β hb a.down) := by
  exact pointed_conjugate_apply
    (sequenceObject_base.{max v uE uB uE' uB'} f b e₀ h n)
    (sequenceObject_base.{max v uE uB uE' uB'} f' b' e₀' h' n) _ _
    (sequenceSquareComponent_base_heq.{v} α β w b b' e₀ e₀' h h' he hb n) a

/-- The total-space component of the chain map is postcomposition by the total-space map. -/
theorem homotopyFiberSequenceMap_total_apply
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (n : ℕ)
    (a : ULift.{max v uE uB uE' uB'} (HomotopyGroup (Fin n) E e₀)) :
    (homotopyFiberSequenceTotalIso.{max v uE uB uE' uB'} f' b' e₀' h' n).hom.toFun
        (((homotopyFiberSequenceMap.{v} α β w b b' e₀ e₀' h h' he hb).f (3 * n + 1)).toFun
          ((homotopyFiberSequenceTotalIso.{max v uE uB uE' uB'} f b e₀ h n).inv.toFun a)) =
      ULift.up (mapFun (Fin n) α he a.down) := by
  exact pointed_conjugate_apply
    (sequenceObject_total.{max v uE uB uE' uB'} f b e₀ h n)
    (sequenceObject_total.{max v uE uB uE' uB'} f' b' e₀' h' n) _ _
    (sequenceSquareComponent_total_heq.{v} α β w b b' e₀ e₀' h h' he hb n) a

/-- The fiber component of the chain map is induced by the ordinary fiber map,
which retains both the mapped point and the whole postcomposed path. -/
theorem homotopyFiberSequenceMap_fiber_apply
    (α : C(E, E')) (β : C(B, B')) (w : ∀ e, f' (α e) = β (f e))
    (b : B) (b' : B') (e₀ : E) (e₀' : E') (h : f e₀ = b) (h' : f' e₀' = b')
    (he : α e₀ = e₀') (hb : β b = b') (n : ℕ)
    (a : ULift.{max v uE uB uE' uB'} (HomotopyGroup (Fin n)
      (ContinuousMap.HomotopyFiber f b) (ContinuousMap.HomotopyFiber.const e₀ h))) :
    (homotopyFiberSequenceFiberIso.{max v uE uB uE' uB'} f' b' e₀' h' n).hom.toFun
        (((homotopyFiberSequenceMap.{v} α β w b b' e₀ e₀' h h' he hb).f (3 * n + 2)).toFun
          ((homotopyFiberSequenceFiberIso.{max v uE uB uE' uB'} f b e₀ h n).inv.toFun a)) =
      ULift.up (mapFun (Fin n) (ContinuousMap.HomotopyFiber.map α β w hb)
        (ContinuousMap.HomotopyFiber.map_const_of_point_eq α β w hb e₀ e₀' h h' he)
        a.down) := by
  exact pointed_conjugate_apply
    (sequenceObject_fiber.{max v uE uB uE' uB'} f b e₀ h n)
    (sequenceObject_fiber.{max v uE uB uE' uB'} f' b' e₀' h' n) _ _
    (sequenceSquareComponent_fiber_heq.{v} α β w b b' e₀ e₀' h h' he hb n) a

end Square

private theorem pointed_id_heq {X Y : Pointed.{v}} (p : X = Y) :
    HEq (𝟙 X) (𝟙 Y) := by
  subst Y
  rfl

private theorem liftedHomotopyMap_congr (n : ℕ)
    {X : Type uE} {Y : Type uB} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} {f g : C(X, Y)} (hfg : f = g)
    (hf : f x = y) (hg : g x = y) :
    liftedHomotopyMap.{v} n f hf = liftedHomotopyMap.{v} n g hg := by
  apply Pointed.Hom.ext
  funext a
  exact congrArg ULift.up (congrFun (mapFun_congr (Fin n) hfg hf hg) a.down)

private theorem liftedHomotopyMap_id (n : ℕ) {X : Type uE} [TopologicalSpace X]
    (x : X) : liftedHomotopyMap.{v} n (ContinuousMap.id X) (x := x) rfl = 𝟙 _ := by
  apply Pointed.Hom.ext
  funext a
  exact congrArg ULift.up (congrFun (mapFun_id (x := x) (Fin n)) a.down)

/-- The identity based square induces the identity chain map. -/
@[simp]
theorem homotopyFiberSequenceMap_id (f : C(E, B)) (b : B) (e₀ : E) (h : f e₀ = b) :
    homotopyFiberSequenceMap.{v} (f := f) (f' := f)
        (ContinuousMap.id E) (ContinuousMap.id B) (fun _ => rfl) b b e₀ e₀ h h rfl rfl =
      𝟙 (homotopyFiberSequence.{max v uE uB} f b e₀ h) := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.id_f]
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n := ⟨k / 3, by omega⟩
    exact eq_of_heq
      ((sequenceSquareComponent_base_heq.{v} (f := f) (f' := f)
          (ContinuousMap.id E) (ContinuousMap.id B) (fun _ => rfl)
          b b e₀ e₀ h h rfl rfl n).trans
        ((heq_of_eq (liftedHomotopyMap_id.{max v uE uB} n b)).trans
          (pointed_id_heq (sequenceObject_base.{v} f b e₀ h n)).symm))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n + 1 := ⟨k / 3, by omega⟩
    exact eq_of_heq
      ((sequenceSquareComponent_total_heq.{v} (f := f) (f' := f)
          (ContinuousMap.id E) (ContinuousMap.id B) (fun _ => rfl)
          b b e₀ e₀ h h rfl rfl n).trans
        ((heq_of_eq (liftedHomotopyMap_id.{max v uE uB} n e₀)).trans
          (pointed_id_heq (sequenceObject_total.{v} f b e₀ h n)).symm))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n + 2 := ⟨k / 3, by omega⟩
    have hc := sequenceSquareComponent_fiber_heq.{v}
      (ContinuousMap.id E) (ContinuousMap.id B) (f := f) (f' := f) (fun _ => rfl)
      b b e₀ e₀ h h rfl rfl n
    have hmap := liftedHomotopyMap_congr.{max v uE uB} n
      (ContinuousMap.HomotopyFiber.map_id (f := f) (b := b))
      (ContinuousMap.HomotopyFiber.map_const_of_point_eq
        (ContinuousMap.id E) (ContinuousMap.id B) (fun _ => rfl) rfl e₀ e₀ h h rfl)
      rfl
    exact eq_of_heq (hc.trans ((heq_of_eq hmap).trans
      ((heq_of_eq (liftedHomotopyMap_id.{max v uE uB} n
        (ContinuousMap.HomotopyFiber.const e₀ h))).trans
          (pointed_id_heq (sequenceObject_fiber.{v} f b e₀ h n)).symm)))

section Composition

universe uE'' uB'' uX uY uZ

private theorem liftedHomotopyMap_comp (n : ℕ)
    {X : Type uX} {Y : Type uY} {Z : Type uZ}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {x : X} {y : Y} {z : Z} (g : C(Y, Z)) (hg : g y = z)
    (f : C(X, Y)) (hf : f x = y) :
    liftedHomotopyMap.{max v uX uY uZ} n (g.comp f) ((congrArg g hf).trans hg) =
      liftedHomotopyMap.{max v uX uY uZ} n f hf ≫
        liftedHomotopyMap.{max v uX uY uZ} n g hg := by
  apply Pointed.Hom.ext
  funext a
  exact congrArg ULift.up (congrFun (mapFun_comp (Fin n) g hg f hf) a.down)

variable {E' : Type uE'} {B' : Type uB'} {E'' : Type uE''} {B'' : Type uB''}
variable [TopologicalSpace E'] [TopologicalSpace B']
variable [TopologicalSpace E''] [TopologicalSpace B'']
variable {f : C(E, B)} {f' : C(E', B')} {f'' : C(E'', B'')}

/-- Chain maps of homotopy-fiber sequences respect composition of strict based
squares. The three pairs of spaces may have six independent universes, and all
three sequences are formed in their common ambient lift universe. -/
theorem homotopyFiberSequenceMap_comp
    (α : C(E, E')) (β : C(B, B')) (α' : C(E', E'')) (β' : C(B', B''))
    (w : ∀ e, f' (α e) = β (f e)) (w' : ∀ e, f'' (α' e) = β' (f' e))
    (b : B) (b' : B') (b'' : B'') (e₀ : E) (e₀' : E') (e₀'' : E'')
    (h : f e₀ = b) (h' : f' e₀' = b') (h'' : f'' e₀'' = b'')
    (he : α e₀ = e₀') (hb : β b = b') (he' : α' e₀' = e₀'') (hb' : β' b' = b'') :
    homotopyFiberSequenceMap.{max v uE uB uE' uB' uE'' uB''}
        (α'.comp α) (β'.comp β) (fun e => (w' (α e)).trans (congrArg β' (w e)))
        b b'' e₀ e₀'' h h'' ((congrArg α' he).trans he') ((congrArg β' hb).trans hb') =
      homotopyFiberSequenceMap.{max v uE uB uE' uB' uE'' uB''}
          α β w b b' e₀ e₀' h h' he hb ≫
        homotopyFiberSequenceMap.{max v uE uB uE' uB' uE'' uB''}
          α' β' w' b' b'' e₀' e₀'' h' h'' he' hb' := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f]
  rcases (show k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 by omega) with h0 | h1 | h2
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n := ⟨k / 3, by omega⟩
    have hleft := sequenceSquareComponent_base_heq.{max v uE uB uE' uB' uE'' uB''}
      (α'.comp α) (β'.comp β) (fun e => (w' (α e)).trans (congrArg β' (w e)))
      b b'' e₀ e₀'' h h'' ((congrArg α' he).trans he') ((congrArg β' hb).trans hb') n
    have hright := heq_comp
      (sequenceObject_base.{max v uE uB uE' uB' uE'' uB''} f b e₀ h n)
      (sequenceObject_base.{max v uE uB uE' uB' uE'' uB''} f' b' e₀' h' n)
      (sequenceObject_base.{max v uE uB uE' uB' uE'' uB''} f'' b'' e₀'' h'' n)
      (sequenceSquareComponent_base_heq.{max v uE uB uE' uB' uE'' uB''}
        α β w b b' e₀ e₀' h h' he hb n)
      (sequenceSquareComponent_base_heq.{max v uE uB uE' uB' uE'' uB''}
        α' β' w' b' b'' e₀' e₀'' h' h'' he' hb' n)
    exact eq_of_heq (hleft.trans
      ((heq_of_eq (liftedHomotopyMap_comp.{max v uE uB uE' uB' uE'' uB''}
        n β' hb' β hb)).trans hright.symm))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n + 1 := ⟨k / 3, by omega⟩
    have hleft := sequenceSquareComponent_total_heq.{max v uE uB uE' uB' uE'' uB''}
      (α'.comp α) (β'.comp β) (fun e => (w' (α e)).trans (congrArg β' (w e)))
      b b'' e₀ e₀'' h h'' ((congrArg α' he).trans he') ((congrArg β' hb).trans hb') n
    have hright := heq_comp
      (sequenceObject_total.{max v uE uB uE' uB' uE'' uB''} f b e₀ h n)
      (sequenceObject_total.{max v uE uB uE' uB' uE'' uB''} f' b' e₀' h' n)
      (sequenceObject_total.{max v uE uB uE' uB' uE'' uB''} f'' b'' e₀'' h'' n)
      (sequenceSquareComponent_total_heq.{max v uE uB uE' uB' uE'' uB''}
        α β w b b' e₀ e₀' h h' he hb n)
      (sequenceSquareComponent_total_heq.{max v uE uB uE' uB' uE'' uB''}
        α' β' w' b' b'' e₀' e₀'' h' h'' he' hb' n)
    exact eq_of_heq (hleft.trans
      ((heq_of_eq (liftedHomotopyMap_comp.{max v uE uB uE' uB' uE'' uB''}
        n α' he' α he)).trans hright.symm))
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = 3 * n + 2 := ⟨k / 3, by omega⟩
    have hleft := sequenceSquareComponent_fiber_heq.{max v uE uB uE' uB' uE'' uB''}
      (α'.comp α) (β'.comp β) (fun e => (w' (α e)).trans (congrArg β' (w e)))
      b b'' e₀ e₀'' h h'' ((congrArg α' he).trans he') ((congrArg β' hb).trans hb') n
    -- Compare fully typed based maps; rewriting the continuous map alone would
    -- leave its basedness proof with the wrong dependent type.
    have hmap := liftedHomotopyMap_congr.{max v uE uB uE' uB' uE'' uB''} n
      (ContinuousMap.HomotopyFiber.map_comp α β α' β' w w' hb hb').symm
      (ContinuousMap.HomotopyFiber.map_const_of_point_eq (α'.comp α) (β'.comp β)
        (fun e => (w' (α e)).trans (congrArg β' (w e))) ((congrArg β' hb).trans hb')
        e₀ e₀'' h h'' ((congrArg α' he).trans he'))
      ((congrArg (ContinuousMap.HomotopyFiber.map α' β' w' hb')
        (ContinuousMap.HomotopyFiber.map_const_of_point_eq
          α β w hb e₀ e₀' h h' he)).trans
        (ContinuousMap.HomotopyFiber.map_const_of_point_eq
          α' β' w' hb' e₀' e₀'' h' h'' he'))
    have hright := heq_comp
      (sequenceObject_fiber.{max v uE uB uE' uB' uE'' uB''} f b e₀ h n)
      (sequenceObject_fiber.{max v uE uB uE' uB' uE'' uB''} f' b' e₀' h' n)
      (sequenceObject_fiber.{max v uE uB uE' uB' uE'' uB''} f'' b'' e₀'' h'' n)
      (sequenceSquareComponent_fiber_heq.{max v uE uB uE' uB' uE'' uB''}
        α β w b b' e₀ e₀' h h' he hb n)
      (sequenceSquareComponent_fiber_heq.{max v uE uB uE' uB' uE'' uB''}
        α' β' w' b' b'' e₀' e₀'' h' h'' he' hb' n)
    exact eq_of_heq (hleft.trans ((heq_of_eq hmap).trans
      ((heq_of_eq (liftedHomotopyMap_comp.{max v uE uB uE' uB' uE'' uB''} n
        (ContinuousMap.HomotopyFiber.map α' β' w' hb')
        (ContinuousMap.HomotopyFiber.map_const_of_point_eq
          α' β' w' hb' e₀' e₀'' h' h'' he')
        (ContinuousMap.HomotopyFiber.map α β w hb)
        (ContinuousMap.HomotopyFiber.map_const_of_point_eq
          α β w hb e₀ e₀' h h' he))).trans hright.symm)))

end Composition

end Characteristics

end HomotopyGroup
