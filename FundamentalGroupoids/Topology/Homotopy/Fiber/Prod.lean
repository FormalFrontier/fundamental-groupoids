/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber

/-!
# Products of ordinary homotopy fibers

`ContinuousMap.HomotopyFiber.prodHomeomorph f g y z` identifies the ordinary
homotopy fiber of `f.prodMap g` over `(y, z)` with the product of the two fibers.
It retains both source points and splits the entire compact-open path by the
two projections. Its inverse pairs the two paths at the same original time.
The comparison commutes with both fiber projections and is natural for two
arbitrary continuous commuting squares.

The four ambient universes are independent, as are all eight in the naturality
law. Only arbitrary topologies and the specified target points are required.
The spaces carry the original product/subspace and compact-open topologies.
The path-pairing continuity argument uses Mathlib's bundled evaluation and
currying operations; local compactness is used only for the interval, not for
any ambient space. No path quotient or change of time parameter is involved.

## References

* `FundamentalGroupoids.Topology.Homotopy.Fiber`, for the retained-point model,
  its coordinate and constructor API, and maps of continuous commuting squares.
* Mathlib's compact-open continuous-map API, for evaluation, currying and products.
-/

@[expose] public section

noncomputable section

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

universe uX₁ uY₁ uX₂ uY₂ vX₁ vY₁ vX₂ vY₂

variable {X₁ : Type uX₁} {Y₁ : Type uY₁} {X₂ : Type uX₂} {Y₂ : Type uY₂}
variable [TopologicalSpace X₁] [TopologicalSpace Y₁]
variable [TopologicalSpace X₂] [TopologicalSpace Y₂]

/-- Pair two compact-open paths by pairing their values at the same time. -/
private def pairPaths (A : Type uY₁) (B : Type uY₂)
    [TopologicalSpace A] [TopologicalSpace B] :
    C(C(I, A) × C(I, B), C(I, A × B)) :=
  let ev₁ : C((C(I, A) × C(I, B)) × I, A) :=
    ((ContinuousMap.id C(I, A)).uncurry).comp
      (((ContinuousMap.fst : C(C(I, A) × C(I, B), C(I, A))).comp
        (ContinuousMap.fst : C((C(I, A) × C(I, B)) × I, C(I, A) × C(I, B)))).prodMk
          (ContinuousMap.snd : C((C(I, A) × C(I, B)) × I, I)))
  let ev₂ : C((C(I, A) × C(I, B)) × I, B) :=
    ((ContinuousMap.id C(I, B)).uncurry).comp
      (((ContinuousMap.snd : C(C(I, A) × C(I, B), C(I, B))).comp
        (ContinuousMap.fst : C((C(I, A) × C(I, B)) × I, C(I, A) × C(I, B)))).prodMk
          (ContinuousMap.snd : C((C(I, A) × C(I, B)) × I, I)))
  (ev₁.prodMk ev₂).curry

private theorem pairPaths_apply (p : C(I, Y₁)) (q : C(I, Y₂)) :
    pairPaths Y₁ Y₂ (p, q) = p.prodMk q := by
  apply ContinuousMap.ext
  intro t
  rfl

variable (f : C(X₁, Y₁)) (g : C(X₂, Y₂)) (y : Y₁) (z : Y₂)

/-- Split an ordinary homotopy fiber of a product into its two ordinary fibers,
retaining both source points and both full paths. The inverse pairs paths at the
same original time. -/
def prodHomeomorph :
    HomotopyFiber (f.prodMap g) (y, z) ≃ₜ HomotopyFiber f y × HomotopyFiber g z where
  toFun :=
    (map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
      ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl).prodMk
    (map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
      ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl)
  invFun := fun p =>
    mk (point p.1, point p.2) ((path p.1).prodMk (path p.2))
      (Prod.ext (path_zero p.1) (path_zero p.2))
      (Prod.ext (path_one p.1) (path_one p.2))
  left_inv := by
    intro p
    apply ext
    · exact Prod.ext
        (point_map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
          ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl p)
        (point_map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
          ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl p)
    · apply ContinuousMap.ext
      intro t
      exact Prod.ext
        (eval_map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
          ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl p t)
        (eval_map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
          ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl p t)
  right_inv := by
    intro p
    let q : HomotopyFiber (f.prodMap g) (y, z) :=
      mk (point p.1, point p.2) ((path p.1).prodMk (path p.2))
        (Prod.ext (path_zero p.1) (path_zero p.2))
        (Prod.ext (path_one p.1) (path_one p.2))
    apply Prod.ext
    · apply ext
      · exact point_map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
          ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl _
      · apply ContinuousMap.ext
        intro t
        exact eval_map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
          ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl q t
    · apply ext
      · exact point_map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
          ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl _
      · apply ContinuousMap.ext
        intro t
        exact eval_map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
          ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl q t
  continuous_toFun :=
    ((map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
      ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl).prodMk
    (map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
      ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl)).continuous
  continuous_invFun := by
    apply continuous_iff.2
    constructor
    · exact ((point (f := f) (b := y)).continuous.comp continuous_fst).prodMk
        ((point (f := g) (b := z)).continuous.comp continuous_snd)
    · have h : Continuous (fun p : HomotopyFiber f y × HomotopyFiber g z =>
          pairPaths Y₁ Y₂ (path p.1, path p.2)) :=
        ((pairPaths Y₁ Y₂).comp
          (((path (f := f) (b := y)).comp ContinuousMap.fst).prodMk
            ((path (f := g) (b := z)).comp ContinuousMap.snd))).continuous
      simpa only [path_mk, pairPaths_apply] using h

/-- The first forward fiber is exactly the existing map for the two first projections. -/
@[simp]
theorem prodHomeomorph_fst (p : HomotopyFiber (f.prodMap g) (y, z)) :
    (prodHomeomorph f g y z p).1 =
      map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
        ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl p := by
  rfl

/-- The second forward fiber is exactly the existing map for the two second projections. -/
@[simp]
theorem prodHomeomorph_snd (p : HomotopyFiber (f.prodMap g) (y, z)) :
    (prodHomeomorph f g y z p).2 =
      map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
        ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl p := by
  rfl

/-- The first forward retained point is the original first source coordinate. -/
theorem point_prodHomeomorph_fst (p : HomotopyFiber (f.prodMap g) (y, z)) :
    point (prodHomeomorph f g y z p).1 = (point p).1 := by
  exact point_map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
    ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl p

/-- The second forward retained point is the original second source coordinate. -/
theorem point_prodHomeomorph_snd (p : HomotopyFiber (f.prodMap g) (y, z)) :
    point (prodHomeomorph f g y z p).2 = (point p).2 := by
  exact point_map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
    ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl p

/-- The first forward whole compact-open path is postcomposition by the first projection. -/
theorem path_prodHomeomorph_fst (p : HomotopyFiber (f.prodMap g) (y, z)) :
    path (prodHomeomorph f g y z p).1 =
      (ContinuousMap.fst : C(Y₁ × Y₂, Y₁)).comp (path p) := by
  exact path_map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
    ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl p

/-- The second forward whole compact-open path is postcomposition by the second projection. -/
theorem path_prodHomeomorph_snd (p : HomotopyFiber (f.prodMap g) (y, z)) :
    path (prodHomeomorph f g y z p).2 =
      (ContinuousMap.snd : C(Y₁ × Y₂, Y₂)).comp (path p) := by
  exact path_map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
    ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl p

/-- The first component is evaluated at the original time. -/
theorem eval_prodHomeomorph_fst (p : HomotopyFiber (f.prodMap g) (y, z)) (t : I) :
    eval t (prodHomeomorph f g y z p).1 = (eval t p).1 := by
  exact eval_map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
    ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl p t

/-- The second component is evaluated at the original time. -/
theorem eval_prodHomeomorph_snd (p : HomotopyFiber (f.prodMap g) (y, z)) (t : I) :
    eval t (prodHomeomorph f g y z p).2 = (eval t p).2 := by
  exact eval_map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
    ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl p t

/-- The inverse retains the pair of the two source points. -/
@[simp]
theorem point_prodHomeomorph_symm (a : HomotopyFiber f y) (b : HomotopyFiber g z) :
    point ((prodHomeomorph f g y z).symm (a, b)) = (point a, point b) := by
  rfl

/-- The inverse pairs the two entire compact-open paths, not just their endpoints. -/
@[simp]
theorem path_prodHomeomorph_symm (a : HomotopyFiber f y) (b : HomotopyFiber g z) :
    path ((prodHomeomorph f g y z).symm (a, b)) = (path a).prodMk (path b) := by
  rfl

/-- The two forward evaluations recover the original product value at every time. -/
theorem eval_prodHomeomorph (p : HomotopyFiber (f.prodMap g) (y, z)) (t : I) :
    (eval t (prodHomeomorph f g y z p).1, eval t (prodHomeomorph f g y z p).2) =
      eval t p := by
  exact Prod.ext (eval_prodHomeomorph_fst f g y z p t)
    (eval_prodHomeomorph_snd f g y z p t)

/-- The inverse evaluates the two paths at one and the same original time. -/
theorem eval_prodHomeomorph_symm (a : HomotopyFiber f y) (b : HomotopyFiber g z) (t : I) :
    eval t ((prodHomeomorph f g y z).symm (a, b)) = (eval t a, eval t b) := by
  simp only [eval_apply, path_prodHomeomorph_symm, ContinuousMap.prod_eval]

/-- The first continuous-map projection square is the existing fiber map. -/
theorem fst_comp_prodHomeomorph :
    (ContinuousMap.fst : C(HomotopyFiber f y × HomotopyFiber g z, HomotopyFiber f y)).comp
        (prodHomeomorph f g y z :
          C(HomotopyFiber (f.prodMap g) (y, z), HomotopyFiber f y × HomotopyFiber g z)) =
      map (f := f.prodMap g) (f' := f) (b := (y, z)) (b' := y)
        ContinuousMap.fst ContinuousMap.fst (fun _ => rfl) rfl := by
  apply ContinuousMap.ext
  intro p
  exact prodHomeomorph_fst f g y z p

/-- The second continuous-map projection square is the existing fiber map. -/
theorem snd_comp_prodHomeomorph :
    (ContinuousMap.snd : C(HomotopyFiber f y × HomotopyFiber g z, HomotopyFiber g z)).comp
        (prodHomeomorph f g y z :
          C(HomotopyFiber (f.prodMap g) (y, z), HomotopyFiber f y × HomotopyFiber g z)) =
      map (f := f.prodMap g) (f' := g) (b := (y, z)) (b' := z)
        ContinuousMap.snd ContinuousMap.snd (fun _ => rfl) rfl := by
  apply ContinuousMap.ext
  intro p
  exact prodHomeomorph_snd f g y z p

/-- The product comparison is natural for two arbitrary continuous commuting squares,
with all eight coordinate spaces in independent universes. -/
theorem prodHomeomorph_naturality
    {X₁' : Type vX₁} {Y₁' : Type vY₁} {X₂' : Type vX₂} {Y₂' : Type vY₂}
    [TopologicalSpace X₁'] [TopologicalSpace Y₁']
    [TopologicalSpace X₂'] [TopologicalSpace Y₂']
    {f' : C(X₁', Y₁')} {g' : C(X₂', Y₂')} {y' : Y₁'} {z' : Y₂'}
    (F₁ : C(X₁, X₁')) (G₁ : C(Y₁, Y₁')) (F₂ : C(X₂, X₂')) (G₂ : C(Y₂, Y₂'))
    (w₁ : ∀ x, f' (F₁ x) = G₁ (f x)) (w₂ : ∀ x, g' (F₂ x) = G₂ (g x))
    (h₁ : G₁ y = y') (h₂ : G₂ z = z') :
    (prodHomeomorph f' g' y' z' :
        C(HomotopyFiber (f'.prodMap g') (y', z'),
          HomotopyFiber f' y' × HomotopyFiber g' z')).comp
      (map (f := f.prodMap g) (f' := f'.prodMap g') (b := (y, z)) (b' := (y', z'))
        (F₁.prodMap F₂) (G₁.prodMap G₂)
        (fun x => Prod.ext (w₁ x.1) (w₂ x.2)) (Prod.ext h₁ h₂)) =
      ((map (f := f) (f' := f') (b := y) (b' := y') F₁ G₁ w₁ h₁).prodMap
        (map (f := g) (f' := g') (b := z) (b' := z') F₂ G₂ w₂ h₂)).comp
        (prodHomeomorph f g y z :
          C(HomotopyFiber (f.prodMap g) (y, z), HomotopyFiber f y × HomotopyFiber g z)) := by
  let M := map (f := f.prodMap g) (f' := f'.prodMap g') (b := (y, z)) (b' := (y', z'))
    (F₁.prodMap F₂) (G₁.prodMap G₂)
    (fun x => Prod.ext (w₁ x.1) (w₂ x.2)) (Prod.ext h₁ h₂)
  apply ContinuousMap.ext
  intro p
  have hp : point (M p) = (F₁.prodMap F₂) (point p) :=
    point_map (f := f.prodMap g) (f' := f'.prodMap g') (b := (y, z)) (b' := (y', z'))
      (F₁.prodMap F₂) (G₁.prodMap G₂)
      (fun x => Prod.ext (w₁ x.1) (w₂ x.2)) (Prod.ext h₁ h₂) p
  have hγ : path (M p) = (G₁.prodMap G₂).comp (path p) :=
    path_map (f := f.prodMap g) (f' := f'.prodMap g') (b := (y, z)) (b' := (y', z'))
      (F₁.prodMap F₂) (G₁.prodMap G₂)
      (fun x => Prod.ext (w₁ x.1) (w₂ x.2)) (Prod.ext h₁ h₂) p
  apply Prod.ext
  · apply ext
    · calc
        point (prodHomeomorph f' g' y' z' (M p)).1 = (point (M p)).1 :=
          point_prodHomeomorph_fst f' g' y' z' (M p)
        _ = F₁ ((point p).1) := congrArg Prod.fst hp
        _ = F₁ (point (prodHomeomorph f g y z p).1) :=
          congrArg F₁ (point_prodHomeomorph_fst f g y z p).symm
        _ = point (map F₁ G₁ w₁ h₁ (prodHomeomorph f g y z p).1) :=
          (point_map F₁ G₁ w₁ h₁ _).symm
    · apply ContinuousMap.ext
      intro t
      calc
        path (prodHomeomorph f' g' y' z' (M p)).1 t = (path (M p) t).1 :=
          eval_prodHomeomorph_fst f' g' y' z' (M p) t
        _ = G₁ ((path p t).1) := congrArg (fun γ : C(I, Y₁' × Y₂') => (γ t).1) hγ
        _ = G₁ (path (prodHomeomorph f g y z p).1 t) :=
          congrArg G₁ (eval_prodHomeomorph_fst f g y z p t).symm
        _ = path (map F₁ G₁ w₁ h₁ (prodHomeomorph f g y z p).1) t :=
          (eval_map F₁ G₁ w₁ h₁ (prodHomeomorph f g y z p).1 t).symm
  · apply ext
    · calc
        point (prodHomeomorph f' g' y' z' (M p)).2 = (point (M p)).2 :=
          point_prodHomeomorph_snd f' g' y' z' (M p)
        _ = F₂ ((point p).2) := congrArg Prod.snd hp
        _ = F₂ (point (prodHomeomorph f g y z p).2) :=
          congrArg F₂ (point_prodHomeomorph_snd f g y z p).symm
        _ = point (map F₂ G₂ w₂ h₂ (prodHomeomorph f g y z p).2) :=
          (point_map F₂ G₂ w₂ h₂ _).symm
    · apply ContinuousMap.ext
      intro t
      calc
        path (prodHomeomorph f' g' y' z' (M p)).2 t = (path (M p) t).2 :=
          eval_prodHomeomorph_snd f' g' y' z' (M p) t
        _ = G₂ ((path p t).2) := congrArg (fun γ : C(I, Y₁' × Y₂') => (γ t).2) hγ
        _ = G₂ (path (prodHomeomorph f g y z p).2 t) :=
          congrArg G₂ (eval_prodHomeomorph_snd f g y z p t).symm
        _ = path (map F₂ G₂ w₂ h₂ (prodHomeomorph f g y z p).2) t :=
          (eval_map F₂ G₂ w₂ h₂ (prodHomeomorph f g y z p).2 t).symm

end ContinuousMap.HomotopyFiber
