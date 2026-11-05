/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Homeomorph
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Homotopy
public import Mathlib.Topology.Homeomorph.Lemmas

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

`ContinuousMap.HomotopyFiber.compFstHomeomorph (Z := Z) f b` separates a
free source factor from the fiber of `f.comp ContinuousMap.fst`, giving the
product of the original fiber of `f` with `Z`. It keeps both source coordinates
and the entire original path at the same time. The three space universes are
independent, as are all six in its naturality law for an arbitrary continuous
square and arbitrary map of the free factor. For `f = id`, the full identity-fiber
factor remains; this comparison does not contract it.

The free-factor comparison composes the existing canonical pullback provider,
a restricted inverse product associator, Mathlib's set-product homeomorphism,
and the inverse canonical provider. No new continuity or inverse construction
is needed.

## References

* `FundamentalGroupoids.Topology.Homotopy.Fiber`, for the retained-point model,
  its coordinate and constructor API, and maps of continuous commuting squares.
* Mathlib's compact-open continuous-map API, for evaluation, currying and products.
* `ContinuousMap.HomotopyFiber.pullbackHomeomorph` and its point/path API;
  Mathlib's `Homeomorph.subtype`, `prodAssoc`, `Set.prod` and `Set.univ`, for
  separating a free source coordinate.
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

namespace ContinuousMap.HomotopyFiber

universe uX uY uZ vX vY vZ

variable {X : Type uX} {Y : Type uY} {Z : Type uZ}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (f : C(X, Y)) (b : Y)

-- Local notation only for the existing canonical provider's target expressions.
local notation "P_b" => {γ : C(I, Y) // γ 0 = b}
local notation "S" =>
  ((fun p : P_b × X => terminalEvaluation b (Prod.fst p) = f (Prod.snd p)) : Set (P_b × X))

/-- Separate a free source factor while retaining the original fiber and its full path.
The construction composes the canonical pullback providers with Mathlib homeomorphisms. -/
def compFstHomeomorph :
    HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b ≃ₜ
      HomotopyFiber f b × Z :=
  let h_iff : ∀ q : P_b × (X × Z),
      terminalEvaluation b q.1 = (f.comp (ContinuousMap.fst : C(X × Z, X))) q.2 ↔
        ((Homeomorph.prodAssoc P_b X Z).symm q) ∈ Set.prod S (Set.univ : Set Z) := by
    intro q
    change (terminalEvaluation b q.1 = f q.2.1) ↔
      (terminalEvaluation b q.1 = f q.2.1) ∧ True
    exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  (pullbackHomeomorph (f.comp (ContinuousMap.fst : C(X × Z, X))) b).trans
    ((Homeomorph.subtype
      (p := fun q : P_b × (X × Z) =>
        terminalEvaluation b q.1 = (f.comp (ContinuousMap.fst : C(X × Z, X))) q.2)
      (q := fun r : (P_b × X) × Z => r ∈ Set.prod S (Set.univ : Set Z))
      (Homeomorph.prodAssoc P_b X Z).symm h_iff).trans
      ((Homeomorph.Set.prod S (Set.univ : Set Z)).trans
        ((pullbackHomeomorph f b).symm.prodCongr (Homeomorph.Set.univ Z))))

/-- The first forward fiber is the existing map for first projection and identity. -/
@[simp]
theorem compFstHomeomorph_fst
    (p : HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b) :
    (compFstHomeomorph (Z := Z) f b p).1 =
      map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
        (b := b) (b' := b) (ContinuousMap.fst : C(X × Z, X))
        (ContinuousMap.id Y) (fun _ => rfl) rfl p := by
  apply ext
  · calc
      point (compFstHomeomorph (Z := Z) f b p).1 =
          ((pullbackHomeomorph (f.comp (ContinuousMap.fst : C(X × Z, X))) b p).1.2).1 :=
        pullbackHomeomorph_symm_point (f := f) (b := b) _
      _ = (point p).1 := congrArg Prod.fst (pullbackHomeomorph_point p)
      _ = point (map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
          (b := b) (b' := b) ContinuousMap.fst (ContinuousMap.id Y)
          (fun _ => rfl) rfl p) :=
        (point_map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
          (b := b) (b' := b) (ContinuousMap.fst : C(X × Z, X))
          (ContinuousMap.id Y) (fun _ : X × Z => rfl) rfl p).symm
  · calc
      path (compFstHomeomorph (Z := Z) f b p).1 =
          (pullbackHomeomorph (f.comp (ContinuousMap.fst : C(X × Z, X))) b p).1.1.1 :=
        pullbackHomeomorph_symm_path (f := f) (b := b) _
      _ = path p := pullbackHomeomorph_path p
      _ = (ContinuousMap.id Y).comp (path p) := (ContinuousMap.id_comp (path p)).symm
      _ = path (map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
          (b := b) (b' := b) ContinuousMap.fst (ContinuousMap.id Y)
          (fun _ => rfl) rfl p) :=
        (path_map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
          (b := b) (b' := b) (ContinuousMap.fst : C(X × Z, X))
          (ContinuousMap.id Y) (fun _ : X × Z => rfl) rfl p).symm

/-- The forward free coordinate is the original second source coordinate. -/
@[simp]
theorem compFstHomeomorph_snd
    (p : HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b) :
    (compFstHomeomorph (Z := Z) f b p).2 = (point p).2 := by
  exact congrArg Prod.snd (pullbackHomeomorph_point p)

/-- The point of the first forward fiber is the original first source coordinate. -/
theorem point_compFstHomeomorph_fst
    (p : HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b) :
    point (compFstHomeomorph (Z := Z) f b p).1 = (point p).1 := by
  calc
    point (compFstHomeomorph (Z := Z) f b p).1 =
        point (map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
          (b := b) (b' := b) (ContinuousMap.fst : C(X × Z, X))
          (ContinuousMap.id Y) (fun _ : X × Z => rfl) rfl p) :=
      congrArg (fun a : HomotopyFiber f b => point a) (compFstHomeomorph_fst f b p)
    _ = (point p).1 :=
      point_map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
        (b := b) (b' := b) (ContinuousMap.fst : C(X × Z, X))
        (ContinuousMap.id Y) (fun _ : X × Z => rfl) rfl p

/-- The first forward fiber retains the entire original compact-open path. -/
theorem path_compFstHomeomorph_fst
    (p : HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b) :
    path (compFstHomeomorph (Z := Z) f b p).1 = path p := by
  calc
    path (compFstHomeomorph (Z := Z) f b p).1 =
        path (map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
          (b := b) (b' := b) (ContinuousMap.fst : C(X × Z, X))
          (ContinuousMap.id Y) (fun _ : X × Z => rfl) rfl p) :=
      congrArg (fun a : HomotopyFiber f b => path a) (compFstHomeomorph_fst f b p)
    _ = (ContinuousMap.id Y).comp (path p) :=
      path_map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
        (b := b) (b' := b) (ContinuousMap.fst : C(X × Z, X))
        (ContinuousMap.id Y) (fun _ : X × Z => rfl) rfl p
    _ = path p := ContinuousMap.id_comp (path p)

/-- Forward evaluation uses the same original time, at every time. -/
theorem eval_compFstHomeomorph_fst
    (p : HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b) (t : I) :
    eval t (compFstHomeomorph (Z := Z) f b p).1 = eval t p := by
  exact congrArg (fun γ : C(I, Y) => γ t) (path_compFstHomeomorph_fst f b p)

/-- The inverse retains the first fiber's point and the specified free coordinate. -/
@[simp]
theorem point_compFstHomeomorph_symm (a : HomotopyFiber f b) (z : Z) :
    point ((compFstHomeomorph (Z := Z) f b).symm (a, z)) = (point a, z) := by
  calc
    point ((compFstHomeomorph (Z := Z) f b).symm (a, z)) =
        ((pullbackHomeomorph f b a).1.2, z) :=
      pullbackHomeomorph_symm_point
        (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (b := b) _
    _ = (point a, z) := congrArg (fun x : X => (x, z)) (pullbackHomeomorph_point a)

/-- The inverse retains the entire original compact-open path. -/
@[simp]
theorem path_compFstHomeomorph_symm (a : HomotopyFiber f b) (z : Z) :
    path ((compFstHomeomorph (Z := Z) f b).symm (a, z)) = path a := by
  calc
    path ((compFstHomeomorph (Z := Z) f b).symm (a, z)) =
        (pullbackHomeomorph f b a).1.1.1 :=
      pullbackHomeomorph_symm_path
        (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (b := b) _
    _ = path a := pullbackHomeomorph_path a

/-- Inverse evaluation also uses the same original time, at every time. -/
theorem eval_compFstHomeomorph_symm (a : HomotopyFiber f b) (z : Z) (t : I) :
    eval t ((compFstHomeomorph (Z := Z) f b).symm (a, z)) = eval t a := by
  exact congrArg (fun γ : C(I, Y) => γ t) (path_compFstHomeomorph_symm f b a z)

/-- The whole first continuous-map projection is the existing fiber map. -/
theorem fst_comp_compFstHomeomorph :
    (ContinuousMap.fst : C(HomotopyFiber f b × Z, HomotopyFiber f b)).comp
        (compFstHomeomorph (Z := Z) f b :
          C(HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b,
            HomotopyFiber f b × Z)) =
      map (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (f' := f)
        (b := b) (b' := b) (ContinuousMap.fst : C(X × Z, X))
        (ContinuousMap.id Y) (fun _ => rfl) rfl := by
  apply ContinuousMap.ext
  intro p
  exact compFstHomeomorph_fst f b p

/-- The whole second continuous-map projection recovers the free source coordinate. -/
theorem snd_comp_compFstHomeomorph :
    (ContinuousMap.snd : C(HomotopyFiber f b × Z, Z)).comp
        (compFstHomeomorph (Z := Z) f b :
          C(HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b,
            HomotopyFiber f b × Z)) =
      (ContinuousMap.snd : C(X × Z, Z)).comp
        (point (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (b := b)) := by
  apply ContinuousMap.ext
  intro p
  exact compFstHomeomorph_snd f b p

/-- The whole original-point diagram retains both source coordinates. -/
theorem point_comp_compFstHomeomorph :
    ((point (f := f) (b := b)).prodMap (ContinuousMap.id Z)).comp
        (compFstHomeomorph (Z := Z) f b :
          C(HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b,
            HomotopyFiber f b × Z)) =
      (point (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (b := b) :
        C(HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b, X × Z)) := by
  apply ContinuousMap.ext
  intro p
  exact Prod.ext (point_compFstHomeomorph_fst f b p) (compFstHomeomorph_snd f b p)

/-- The whole path diagram preserves the original bundled compact-open path map. -/
theorem path_comp_compFstHomeomorph :
    ((path (f := f) (b := b) : C(HomotopyFiber f b, C(I, Y))).comp
        (ContinuousMap.fst : C(HomotopyFiber f b × Z, HomotopyFiber f b))).comp
        (compFstHomeomorph (Z := Z) f b :
          C(HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b,
            HomotopyFiber f b × Z)) =
      (path (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (b := b) :
        C(HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b, C(I, Y))) := by
  apply ContinuousMap.ext
  intro p
  exact path_compFstHomeomorph_fst f b p

/-- Naturality for an arbitrary continuous commuting square and arbitrary free map,
with six independently universe-polymorphic spaces and no embedding assumptions. -/
theorem compFstHomeomorph_naturality
    {X' : Type vX} {Y' : Type vY} {Z' : Type vZ}
    [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace Z']
    {f' : C(X', Y')} {b' : Y'}
    (F : C(X, X')) (G : C(Y, Y')) (H : C(Z, Z'))
    (w : ∀ x, f' (F x) = G (f x)) (hb : G b = b') :
    (compFstHomeomorph (Z := Z') f' b' :
        C(HomotopyFiber (f'.comp (ContinuousMap.fst : C(X' × Z', X'))) b',
          HomotopyFiber f' b' × Z')).comp
      (map (f := f.comp (ContinuousMap.fst : C(X × Z, X)))
        (f' := f'.comp (ContinuousMap.fst : C(X' × Z', X')))
        (b := b) (b' := b') (F.prodMap H) G (fun p => w p.1) hb) =
      ((map (f := f) (f' := f') (b := b) (b' := b') F G w hb).prodMap H).comp
        (compFstHomeomorph (Z := Z) f b :
          C(HomotopyFiber (f.comp (ContinuousMap.fst : C(X × Z, X))) b,
            HomotopyFiber f b × Z)) := by
  let M := map (f := f.comp (ContinuousMap.fst : C(X × Z, X)))
    (f' := f'.comp (ContinuousMap.fst : C(X' × Z', X')))
    (b := b) (b' := b') (F.prodMap H) G (fun p => w p.1) hb
  apply ContinuousMap.ext
  intro p
  have hp : point (M p) = (F.prodMap H) (point p) :=
    point_map (f := f.comp (ContinuousMap.fst : C(X × Z, X)))
      (f' := f'.comp (ContinuousMap.fst : C(X' × Z', X')))
      (b := b) (b' := b') (F.prodMap H) G (fun p => w p.1) hb p
  have hγ : path (M p) = G.comp (path p) :=
    path_map (f := f.comp (ContinuousMap.fst : C(X × Z, X)))
      (f' := f'.comp (ContinuousMap.fst : C(X' × Z', X')))
      (b := b) (b' := b') (F.prodMap H) G (fun p => w p.1) hb p
  apply Prod.ext
  · apply ext
    · calc
        point (compFstHomeomorph (Z := Z') f' b' (M p)).1 = (point (M p)).1 :=
          point_compFstHomeomorph_fst f' b' (M p)
        _ = F ((point p).1) := congrArg Prod.fst hp
        _ = F (point (compFstHomeomorph (Z := Z) f b p).1) :=
          congrArg F (point_compFstHomeomorph_fst f b p).symm
        _ = point (map F G w hb (compFstHomeomorph (Z := Z) f b p).1) :=
          (point_map F G w hb (compFstHomeomorph (Z := Z) f b p).1).symm
    · calc
        path (compFstHomeomorph (Z := Z') f' b' (M p)).1 = path (M p) :=
          path_compFstHomeomorph_fst f' b' (M p)
        _ = G.comp (path p) := hγ
        _ = G.comp (path (compFstHomeomorph (Z := Z) f b p).1) :=
          congrArg (fun γ : C(I, Y) => G.comp γ) (path_compFstHomeomorph_fst f b p).symm
        _ = path (map F G w hb (compFstHomeomorph (Z := Z) f b p).1) :=
          (path_map F G w hb (compFstHomeomorph (Z := Z) f b p).1).symm
  · calc
      (compFstHomeomorph (Z := Z') f' b' (M p)).2 = (point (M p)).2 :=
        compFstHomeomorph_snd f' b' (M p)
      _ = H ((point p).2) := congrArg Prod.snd hp
      _ = H (compFstHomeomorph (Z := Z) f b p).2 :=
        congrArg H (compFstHomeomorph_snd f b p).symm

/-- The forward comparison splits a canonical constructor without changing its path. -/
theorem compFstHomeomorph_mk (x : X) (z : Z) (γ : C(I, Y))
    (h₀ : γ 0 = b) (h₁ : γ 1 = f x) :
    compFstHomeomorph (Z := Z) f b
        (mk (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (b := b)
          (x, z) γ h₀ h₁) =
      (mk (f := f) (b := b) x γ h₀ h₁, z) := by
  apply Prod.ext
  · apply ext
    · exact point_compFstHomeomorph_fst f b (mk (x, z) γ h₀ h₁)
    · exact path_compFstHomeomorph_fst f b (mk (x, z) γ h₀ h₁)
  · exact compFstHomeomorph_snd f b (mk (x, z) γ h₀ h₁)

/-- The inverse comparison rejoins a canonical constructor and the free coordinate. -/
theorem compFstHomeomorph_symm_mk (x : X) (z : Z) (γ : C(I, Y))
    (h₀ : γ 0 = b) (h₁ : γ 1 = f x) :
    (compFstHomeomorph (Z := Z) f b).symm
        (mk (f := f) (b := b) x γ h₀ h₁, z) =
      mk (f := f.comp (ContinuousMap.fst : C(X × Z, X))) (b := b)
        (x, z) γ h₀ h₁ := by
  apply ext
  · exact point_compFstHomeomorph_symm f b (mk x γ h₀ h₁) z
  · exact path_compFstHomeomorph_symm f b (mk x γ h₀ h₁) z

end ContinuousMap.HomotopyFiber

/-!
## Dependent products

The ordinary homotopy fiber of a dependent product map is homeomorphic to
the dependent product of the coordinate fibers. The comparison retains every
source coordinate and the entire path at the original time. It preserves the
specified original constant points, is natural for arbitrary families of
commuting squares, and agrees with the binary comparison through `piFinTwo`.

* The comparison commutes with transport by a family of homotopies, its reverse,
  and the chosen left and right inverse homotopies as whole continuous maps,
  preserving every outer homotopy time and inner path time.
-/

namespace ContinuousMap.HomotopyFiber

universe uκ uEπ uBπ vEπ vBπ

section Pi

variable {κ : Type uκ} {E : κ → Type uEπ} {B : κ → Type uBπ}
variable [∀ k, TopologicalSpace (E k)] [∀ k, TopologicalSpace (B k)]
variable (f : ∀ k, C(E k, B k)) (b : ∀ k, B k)

-- Implementation aliases for the existing projection-map and transpose composites.
private def piForward :
    C(HomotopyFiber (ContinuousMap.piMap f) b, ∀ k, HomotopyFiber (f k) (b k)) :=
  ContinuousMap.pi fun k =>
    map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
      (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl

private def piInverse :
    C((∀ k, HomotopyFiber (f k) (b k)), HomotopyFiber (ContinuousMap.piMap f) b) where
  toFun z :=
    mk (fun k => point (z k)) (ContinuousMap.pi fun k => path (z k))
      (funext fun k => path_zero (z k))
      (funext fun k => path_one (z k))
  continuous_toFun := by
    apply continuous_iff.2
    constructor
    · exact (ContinuousMap.pi fun k =>
        (point (f := f k) (b := b k)).comp (ContinuousMap.eval k)).continuous
    · exact ((ContinuousMap.pi fun k =>
        ((path (f := f k) (b := b k)).comp (ContinuousMap.eval k)).uncurry).curry).continuous

private theorem pi_left_inv : Function.LeftInverse (piInverse f b) (piForward f b) := by
  intro p
  apply ext
  · funext k
    exact point_map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
      (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl p
  · apply ContinuousMap.ext
    intro t
    funext k
    exact eval_map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
      (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl p t

private theorem pi_right_inv : Function.RightInverse (piInverse f b) (piForward f b) := by
  intro z
  funext k
  apply ext
  · exact point_map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
      (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl (piInverse f b z)
  · apply ContinuousMap.ext
    intro t
    exact eval_map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
      (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl (piInverse f b z) t

/-- Split an ordinary homotopy fiber of a dependent product map into its coordinate
fibers. The forward map retains every source coordinate and projects the entire
path; the inverse retains the whole point family and assembles the paths at the
same time, with the ordinary compact-open and dependent-product topologies. -/
-- Keep the private inverse-law proofs out of the exposed constructor body.
@[no_expose]
def piHomeomorph :
    HomotopyFiber (ContinuousMap.piMap f) b ≃ₜ ∀ k, HomotopyFiber (f k) (b k) where
  toFun := piForward f b
  invFun := piInverse f b
  left_inv := pi_left_inv f b
  right_inv := pi_right_inv f b
  continuous_toFun := (piForward f b).continuous
  continuous_invFun := (piInverse f b).continuous

-- Private proved characteristic bridges allow the public constructor to stay opaque.
private theorem piHomeomorph_apply_proof
    (p : HomotopyFiber (ContinuousMap.piMap f) b) (k : κ) :
    piHomeomorph f b p k =
      map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
        (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl p := by
  rfl

/-- Each whole forward coordinate is the existing map of fibers for the projections. -/
@[simp]
theorem piHomeomorph_apply (p : HomotopyFiber (ContinuousMap.piMap f) b) (k : κ) :
    piHomeomorph f b p k =
      map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
        (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl p :=
  piHomeomorph_apply_proof f b p k

private theorem piHomeomorph_toContinuousMap_proof :
    (piHomeomorph f b :
      C(HomotopyFiber (ContinuousMap.piMap f) b, ∀ k, HomotopyFiber (f k) (b k))) =
      ContinuousMap.pi (fun k =>
        map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
          (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl) := by
  rfl

/-- The whole forward continuous map is the product of the existing fiber maps. -/
theorem piHomeomorph_toContinuousMap :
    (piHomeomorph f b :
      C(HomotopyFiber (ContinuousMap.piMap f) b, ∀ k, HomotopyFiber (f k) (b k))) =
      ContinuousMap.pi (fun k =>
        map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
          (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl) :=
  piHomeomorph_toContinuousMap_proof f b

/-- Each forward fiber retains the corresponding original source coordinate. -/
theorem point_piHomeomorph (p : HomotopyFiber (ContinuousMap.piMap f) b) (k : κ) :
    point (piHomeomorph f b p k) = point p k := by
  rw [piHomeomorph_apply]
  exact point_map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
    (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl p

/-- Each forward fiber retains the whole postcomposed compact-open path. -/
theorem path_piHomeomorph (p : HomotopyFiber (ContinuousMap.piMap f) b) (k : κ) :
    path (piHomeomorph f b p k) = (ContinuousMap.eval k).comp (path p) := by
  rw [piHomeomorph_apply]
  exact path_map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
    (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl p

/-- Forward path evaluation keeps the original time and selects one coordinate. -/
theorem eval_piHomeomorph (p : HomotopyFiber (ContinuousMap.piMap f) b) (k : κ) (t : I) :
    eval t (piHomeomorph f b p k) = eval t p k := by
  exact congrArg (fun γ : C(I, B k) => γ t) (path_piHomeomorph f b p k)

private theorem point_piHomeomorph_symm_proof (z : ∀ k, HomotopyFiber (f k) (b k)) :
    point ((piHomeomorph f b).symm z) = fun k => point (z k) := by
  rfl

/-- The inverse retains the entire family of source points. -/
@[simp]
theorem point_piHomeomorph_symm (z : ∀ k, HomotopyFiber (f k) (b k)) :
    point ((piHomeomorph f b).symm z) = fun k => point (z k) :=
  point_piHomeomorph_symm_proof f b z

private theorem path_piHomeomorph_symm_proof (z : ∀ k, HomotopyFiber (f k) (b k)) :
    path ((piHomeomorph f b).symm z) = ContinuousMap.pi (fun k => path (z k)) := by
  rfl

/-- The inverse assembles the whole compact-open path at the same original time. -/
@[simp]
theorem path_piHomeomorph_symm (z : ∀ k, HomotopyFiber (f k) (b k)) :
    path ((piHomeomorph f b).symm z) = ContinuousMap.pi (fun k => path (z k)) :=
  path_piHomeomorph_symm_proof f b z

/-- Inverse evaluation assembles every coordinate at one and the same time. -/
theorem eval_piHomeomorph_symm (z : ∀ k, HomotopyFiber (f k) (b k)) (t : I) :
    eval t ((piHomeomorph f b).symm z) = fun k => eval t (z k) := by
  exact congrArg (fun γ : C(I, ∀ k, B k) => γ t) (path_piHomeomorph_symm f b z)

/-- Each whole bundled projection square is the existing map of ordinary fibers. -/
theorem eval_comp_piHomeomorph (k : κ) :
    (ContinuousMap.eval k :
      C((∀ j, HomotopyFiber (f j) (b j)), HomotopyFiber (f k) (b k))).comp
        (piHomeomorph f b :
          C(HomotopyFiber (ContinuousMap.piMap f) b, ∀ j, HomotopyFiber (f j) (b j))) =
      map (f := ContinuousMap.piMap f) (f' := f k) (b := b) (b' := b k)
        (ContinuousMap.eval k) (ContinuousMap.eval k) (fun _ => rfl) rfl := by
  apply ContinuousMap.ext
  intro p
  exact piHomeomorph_apply f b p k

/-- The forward comparison preserves the specified family of original constant points. -/
theorem piHomeomorph_const (e₀ : ∀ k, E k) (h : ∀ k, f k (e₀ k) = b k) :
    piHomeomorph f b (const e₀ (funext h)) = fun k => const (e₀ k) (h k) := by
  funext k
  apply ext
  · simpa only [point_const] using point_piHomeomorph f b (const e₀ (funext h)) k
  · apply ContinuousMap.ext
    intro t
    simpa only [eval_apply, path_const, ContinuousMap.const_apply] using
      eval_piHomeomorph f b (const e₀ (funext h)) k t

/-- The inverse comparison preserves the same specified original constant points. -/
theorem piHomeomorph_symm_const (e₀ : ∀ k, E k) (h : ∀ k, f k (e₀ k) = b k) :
    (piHomeomorph f b).symm (fun k => const (e₀ k) (h k)) =
      const e₀ (funext h) := by
  rw [← piHomeomorph_const f b e₀ h]
  exact (piHomeomorph f b).symm_apply_apply (const e₀ (funext h))

section Homotopy

variable {f b} {g : ∀ i, C(E i, B i)}

/-- The dependent-product comparison commutes with transport by a family of homotopies
as an equality of whole continuous maps of homotopy fibers. -/
theorem piHomeomorph_comp_homotopyMap
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) :
    (piHomeomorph g b :
        C(HomotopyFiber (ContinuousMap.piMap g) b, ∀ i, HomotopyFiber (g i) (b i))).comp
      (homotopyMap (ContinuousMap.Homotopy.piMap H) b) =
      (ContinuousMap.piMap (fun i => homotopyMap (H i) (b i))).comp
        (piHomeomorph f b :
          C(HomotopyFiber (ContinuousMap.piMap f) b, ∀ i, HomotopyFiber (f i) (b i))) := by
  apply ContinuousMap.ext
  intro z
  funext i
  have h := congrArg (fun M : C(_, _) => M z)
    (map_comp_homotopyMap (b := b) (b' := b i)
      (ContinuousMap.Homotopy.piMap H) (H i)
      (ContinuousMap.eval i) (ContinuousMap.eval i)
      (fun _ => rfl) (fun _ => rfl) rfl (fun _ _ => rfl))
  exact (piHomeomorph_apply g b _ i).trans
    (h.trans (congrArg (homotopyMap (H i) (b i))
      (piHomeomorph_apply f b z i).symm))

/-- The dependent-product comparison commutes with transport by the reversed family
of homotopies, using the reverse of the product homotopy. -/
theorem piHomeomorph_comp_homotopyMap_symm
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) :
    (piHomeomorph f b :
        C(HomotopyFiber (ContinuousMap.piMap f) b, ∀ i, HomotopyFiber (f i) (b i))).comp
      (homotopyMap (ContinuousMap.Homotopy.piMap H).symm b) =
      (ContinuousMap.piMap (fun i => homotopyMap (H i).symm (b i))).comp
        (piHomeomorph g b :
          C(HomotopyFiber (ContinuousMap.piMap g) b, ∀ i, HomotopyFiber (g i) (b i))) := by
  apply ContinuousMap.ext
  intro z
  funext i
  have h := congrArg (fun M : C(_, _) => M z)
    (map_comp_homotopyMap (b := b) (b' := b i)
      (ContinuousMap.Homotopy.piMap H).symm (H i).symm
      (ContinuousMap.eval i) (ContinuousMap.eval i)
      (fun _ => rfl) (fun _ => rfl) rfl (fun _ _ => rfl))
  exact (piHomeomorph_apply f b _ i).trans
    (h.trans (congrArg (homotopyMap (H i).symm (b i))
      (piHomeomorph_apply g b z i).symm))

/-- The dependent-product comparison intertwines the chosen left inverse homotopy
with the product of the coordinate left inverse homotopies at every time. -/
theorem piHomeomorph_comp_homotopyMapLeftHomotopy
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) :
    (piHomeomorph f b :
        C(HomotopyFiber (ContinuousMap.piMap f) b, ∀ i, HomotopyFiber (f i) (b i))).comp
      (homotopyMapLeftHomotopy (ContinuousMap.Homotopy.piMap H) b).toContinuousMap =
      (ContinuousMap.Homotopy.piMap (fun i =>
        homotopyMapLeftHomotopy (H i) (b i))).toContinuousMap.comp
          ((ContinuousMap.id I).prodMap
            (piHomeomorph f b :
              C(HomotopyFiber (ContinuousMap.piMap f) b,
                ∀ i, HomotopyFiber (f i) (b i)))) := by
  apply ContinuousMap.ext
  rintro ⟨s, z⟩
  funext i
  have h := congrArg (fun M : C(_, _) => M (s, z))
    (map_comp_homotopyMapLeftHomotopy (b := b) (b' := b i)
      (ContinuousMap.Homotopy.piMap H) (H i)
      (ContinuousMap.eval i) (ContinuousMap.eval i)
      (fun _ => rfl) (fun _ => rfl) rfl (fun _ _ => rfl))
  exact (piHomeomorph_apply f b _ i).trans
    (h.trans (congrArg (fun w => homotopyMapLeftHomotopy (H i) (b i) (s, w))
      (piHomeomorph_apply f b z i).symm))

/-- The dependent-product comparison intertwines the chosen right inverse homotopy
with the product of the coordinate right inverse homotopies at every time. -/
theorem piHomeomorph_comp_homotopyMapRightHomotopy
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) :
    (piHomeomorph g b :
        C(HomotopyFiber (ContinuousMap.piMap g) b, ∀ i, HomotopyFiber (g i) (b i))).comp
      (homotopyMapRightHomotopy (ContinuousMap.Homotopy.piMap H) b).toContinuousMap =
      (ContinuousMap.Homotopy.piMap (fun i =>
        homotopyMapRightHomotopy (H i) (b i))).toContinuousMap.comp
          ((ContinuousMap.id I).prodMap
            (piHomeomorph g b :
              C(HomotopyFiber (ContinuousMap.piMap g) b,
                ∀ i, HomotopyFiber (g i) (b i)))) := by
  apply ContinuousMap.ext
  rintro ⟨s, z⟩
  funext i
  have h := congrArg (fun M : C(_, _) => M (s, z))
    (map_comp_homotopyMapRightHomotopy (b := b) (b' := b i)
      (ContinuousMap.Homotopy.piMap H) (H i)
      (ContinuousMap.eval i) (ContinuousMap.eval i)
      (fun _ => rfl) (fun _ => rfl) rfl (fun _ _ => rfl))
  exact (piHomeomorph_apply g b _ i).trans
    (h.trans (congrArg (fun w => homotopyMapRightHomotopy (H i) (b i) (s, w))
      (piHomeomorph_apply g b z i).symm))

/-- Each coordinate of the chosen left inverse homotopy is the chosen coordinate
homotopy on the corresponding whole fiber element. -/
theorem piHomeomorph_homotopyMapLeftHomotopy_apply
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) (s : I)
    (z : HomotopyFiber (ContinuousMap.piMap f) b) (i : κ) :
    piHomeomorph f b
        (homotopyMapLeftHomotopy (ContinuousMap.Homotopy.piMap H) b (s, z)) i =
      homotopyMapLeftHomotopy (H i) (b i) (s, piHomeomorph f b z i) := by
  exact congrArg
    (fun M : C(I × HomotopyFiber (ContinuousMap.piMap f) b,
        ∀ j, HomotopyFiber (f j) (b j)) => M (s, z) i)
    (piHomeomorph_comp_homotopyMapLeftHomotopy H)

/-- Each coordinate of the chosen right inverse homotopy is the chosen coordinate
homotopy on the corresponding whole fiber element. -/
theorem piHomeomorph_homotopyMapRightHomotopy_apply
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) (s : I)
    (z : HomotopyFiber (ContinuousMap.piMap g) b) (i : κ) :
    piHomeomorph g b
        (homotopyMapRightHomotopy (ContinuousMap.Homotopy.piMap H) b (s, z)) i =
      homotopyMapRightHomotopy (H i) (b i) (s, piHomeomorph g b z i) := by
  exact congrArg
    (fun M : C(I × HomotopyFiber (ContinuousMap.piMap g) b,
        ∀ j, HomotopyFiber (g j) (b j)) => M (s, z) i)
    (piHomeomorph_comp_homotopyMapRightHomotopy H)

/-- The left inverse comparison preserves the entire retained coordinate path
at every outer homotopy time. -/
theorem path_piHomeomorph_homotopyMapLeftHomotopy
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) (s : I)
    (z : HomotopyFiber (ContinuousMap.piMap f) b) (i : κ) :
    path (piHomeomorph f b
        (homotopyMapLeftHomotopy (ContinuousMap.Homotopy.piMap H) b (s, z)) i) =
      path (homotopyMapLeftHomotopy (H i) (b i) (s, piHomeomorph f b z i)) := by
  exact congrArg (path (f := f i) (b := b i))
    (piHomeomorph_homotopyMapLeftHomotopy_apply H s z i)

/-- The right inverse comparison preserves the entire retained coordinate path
at every outer homotopy time. -/
theorem path_piHomeomorph_homotopyMapRightHomotopy
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) (s : I)
    (z : HomotopyFiber (ContinuousMap.piMap g) b) (i : κ) :
    path (piHomeomorph g b
        (homotopyMapRightHomotopy (ContinuousMap.Homotopy.piMap H) b (s, z)) i) =
      path (homotopyMapRightHomotopy (H i) (b i) (s, piHomeomorph g b z i)) := by
  exact congrArg (path (f := g i) (b := b i))
    (piHomeomorph_homotopyMapRightHomotopy_apply H s z i)

/-- The left inverse comparison preserves each coordinate path value at arbitrary
outer homotopy time and inner path time. -/
theorem eval_piHomeomorph_homotopyMapLeftHomotopy
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) (s : I)
    (z : HomotopyFiber (ContinuousMap.piMap f) b) (i : κ) (t : I) :
    eval t (piHomeomorph f b
        (homotopyMapLeftHomotopy (ContinuousMap.Homotopy.piMap H) b (s, z)) i) =
      eval t (homotopyMapLeftHomotopy (H i) (b i) (s, piHomeomorph f b z i)) := by
  exact congrArg (fun γ : C(I, B i) => γ t)
    (path_piHomeomorph_homotopyMapLeftHomotopy H s z i)

/-- The right inverse comparison preserves each coordinate path value at arbitrary
outer homotopy time and inner path time. -/
theorem eval_piHomeomorph_homotopyMapRightHomotopy
    (H : ∀ i, ContinuousMap.Homotopy (f i) (g i)) (s : I)
    (z : HomotopyFiber (ContinuousMap.piMap g) b) (i : κ) (t : I) :
    eval t (piHomeomorph g b
        (homotopyMapRightHomotopy (ContinuousMap.Homotopy.piMap H) b (s, z)) i) =
      eval t (homotopyMapRightHomotopy (H i) (b i) (s, piHomeomorph g b z i)) := by
  exact congrArg (fun γ : C(I, B i) => γ t)
    (path_piHomeomorph_homotopyMapRightHomotopy H s z i)

end Homotopy

section Naturality

variable {E' : κ → Type vEπ} {B' : κ → Type vBπ}
variable [∀ k, TopologicalSpace (E' k)] [∀ k, TopologicalSpace (B' k)]
variable {f' : ∀ k, C(E' k, B' k)} {b' : ∀ k, B' k}

/-- The dependent-product comparison is natural for arbitrary families of continuous
commuting squares and specified target-anchor equalities. The index, source and
target family universe levels are independent. -/
theorem piHomeomorph_naturality
    (F : ∀ k, C(E k, E' k)) (G : ∀ k, C(B k, B' k))
    (w : ∀ k e, f' k (F k e) = G k (f k e)) (hb : ∀ k, G k (b k) = b' k) :
    (piHomeomorph f' b' :
        C(HomotopyFiber (ContinuousMap.piMap f') b', ∀ k, HomotopyFiber (f' k) (b' k))).comp
      (map (f := ContinuousMap.piMap f) (f' := ContinuousMap.piMap f')
        (b := b) (b' := b') (ContinuousMap.piMap F) (ContinuousMap.piMap G)
        (fun e => funext (fun k => w k (e k))) (funext hb)) =
      (ContinuousMap.piMap fun k =>
        map (f := f k) (f' := f' k) (b := b k) (b' := b' k) (F k) (G k) (w k) (hb k)).comp
        (piHomeomorph f b :
          C(HomotopyFiber (ContinuousMap.piMap f) b, ∀ k, HomotopyFiber (f k) (b k))) := by
  let M := map (f := ContinuousMap.piMap f) (f' := ContinuousMap.piMap f')
    (b := b) (b' := b') (ContinuousMap.piMap F) (ContinuousMap.piMap G)
    (fun e => funext (fun k => w k (e k))) (funext hb)
  apply ContinuousMap.ext
  intro p
  have hp : point (M p) = (ContinuousMap.piMap F) (point p) :=
    point_map (ContinuousMap.piMap F) (ContinuousMap.piMap G)
      (fun e => funext (fun k => w k (e k))) (funext hb) p
  have hγ : path (M p) = (ContinuousMap.piMap G).comp (path p) :=
    path_map (ContinuousMap.piMap F) (ContinuousMap.piMap G)
      (fun e => funext (fun k => w k (e k))) (funext hb) p
  funext k
  apply ext
  · calc
      point (piHomeomorph f' b' (M p) k) = point (M p) k :=
        point_piHomeomorph f' b' (M p) k
      _ = F k (point p k) := congrFun hp k
      _ = F k (point (piHomeomorph f b p k)) :=
        congrArg (F k) (point_piHomeomorph f b p k).symm
      _ = point (map (F k) (G k) (w k) (hb k) (piHomeomorph f b p k)) :=
        (point_map (F k) (G k) (w k) (hb k) _).symm
  · apply ContinuousMap.ext
    intro t
    calc
      path (piHomeomorph f' b' (M p) k) t = path (M p) t k :=
        eval_piHomeomorph f' b' (M p) k t
      _ = G k (path p t k) :=
        congrArg (fun γ : C(I, ∀ j, B' j) => γ t k) hγ
      _ = G k (path (piHomeomorph f b p k) t) :=
        congrArg (G k) (eval_piHomeomorph f b p k t).symm
      _ = path (map (F k) (G k) (w k) (hb k) (piHomeomorph f b p k)) t :=
        (eval_map (F k) (G k) (w k) (hb k) (piHomeomorph f b p k) t).symm

end Naturality
end Pi

section FinTwo

variable {E : Fin 2 → Type uEπ} {B : Fin 2 → Type uBπ}
variable [∀ k, TopologicalSpace (E k)] [∀ k, TopologicalSpace (B k)]
variable (f : ∀ k, C(E k, B k)) (b : ∀ k, B k)

/-- For common-universe two-coordinate families, the dependent-product comparison
agrees with the binary comparison after the coordinate `piFinTwo` homeomorphisms.
This diagram does not restrict the four independent universes of the binary API. -/
theorem piHomeomorph_finTwo :
    let σE := Homeomorph.piFinTwo E
    let σB := Homeomorph.piFinTwo B
    let σHF := Homeomorph.piFinTwo (fun k => HomotopyFiber (f k) (b k))
    let S := homeomorph (f := ContinuousMap.piMap f) (g := (f 0).prodMap (f 1))
      (y := b) (y' := (b 0, b 1)) σE σB (fun _ => rfl) rfl
    S.trans (prodHomeomorph (f 0) (f 1) (b 0) (b 1)) =
      (piHomeomorph f b).trans σHF := by
  let σE := Homeomorph.piFinTwo E
  let σB := Homeomorph.piFinTwo B
  let S := homeomorph (f := ContinuousMap.piMap f) (g := (f 0).prodMap (f 1))
    (y := b) (y' := (b 0, b 1)) σE σB (fun _ => rfl) rfl
  apply Homeomorph.ext
  intro p
  have hp : point (S p) = σE (point p) :=
    point_homeomorph σE σB (fun _ => rfl) rfl p
  have hγ : path (S p) = (σB : C((∀ k, B k), B 0 × B 1)).comp (path p) :=
    path_homeomorph σE σB (fun _ => rfl) rfl p
  apply Prod.ext
  · apply ext
    · calc
        point (prodHomeomorph (f 0) (f 1) (b 0) (b 1) (S p)).1 =
            (point (S p)).1 :=
          point_prodHomeomorph_fst (f 0) (f 1) (b 0) (b 1) (S p)
        _ = point p 0 :=
          congrArg Prod.fst hp
        _ = point (piHomeomorph f b p 0) := (point_piHomeomorph f b p 0).symm
    · apply ContinuousMap.ext
      intro t
      calc
        path (prodHomeomorph (f 0) (f 1) (b 0) (b 1) (S p)).1 t =
            (path (S p) t).1 :=
          eval_prodHomeomorph_fst (f 0) (f 1) (b 0) (b 1) (S p) t
        _ = path p t 0 :=
          congrArg (fun γ : C(I, B 0 × B 1) => (γ t).1) hγ
        _ = path (piHomeomorph f b p 0) t := (eval_piHomeomorph f b p 0 t).symm
  · apply ext
    · calc
        point (prodHomeomorph (f 0) (f 1) (b 0) (b 1) (S p)).2 =
            (point (S p)).2 :=
          point_prodHomeomorph_snd (f 0) (f 1) (b 0) (b 1) (S p)
        _ = point p 1 :=
          congrArg Prod.snd hp
        _ = point (piHomeomorph f b p 1) := (point_piHomeomorph f b p 1).symm
    · apply ContinuousMap.ext
      intro t
      calc
        path (prodHomeomorph (f 0) (f 1) (b 0) (b 1) (S p)).2 t =
            (path (S p) t).2 :=
          eval_prodHomeomorph_snd (f 0) (f 1) (b 0) (b 1) (S p) t
        _ = path p t 1 :=
          congrArg (fun γ : C(I, B 0 × B 1) => (γ t).2) hγ
        _ = path (piHomeomorph f b p 1) t := (eval_piHomeomorph f b p 1 t).symm

end FinTwo

section ProdConst

universe uE₀ uB₀ uE₁ uB₁

variable {E₀ : Type uE₀} {B₀ : Type uB₀} {E₁ : Type uE₁} {B₁ : Type uB₁}
variable [TopologicalSpace E₀] [TopologicalSpace B₀]
variable [TopologicalSpace E₁] [TopologicalSpace B₁]
variable (f : C(E₀, B₀)) (g : C(E₁, B₁)) (b₀ : B₀) (b₁ : B₁)

/-- The binary comparison preserves both specified original constant points, with
all four ambient universes independent. -/
theorem prodHomeomorph_const (e₀ : E₀) (e₁ : E₁)
    (h₀ : f e₀ = b₀) (h₁ : g e₁ = b₁) :
    prodHomeomorph f g b₀ b₁ (const (e₀, e₁) (Prod.ext h₀ h₁)) =
      (const e₀ h₀, const e₁ h₁) := by
  apply Prod.ext
  · apply ext
    · simpa only [point_const] using
        point_prodHomeomorph_fst f g b₀ b₁ (const (e₀, e₁) (Prod.ext h₀ h₁))
    · apply ContinuousMap.ext
      intro t
      simpa only [eval_apply, path_const, ContinuousMap.const_apply] using
        eval_prodHomeomorph_fst f g b₀ b₁ (const (e₀, e₁) (Prod.ext h₀ h₁)) t
  · apply ext
    · simpa only [point_const] using
        point_prodHomeomorph_snd f g b₀ b₁ (const (e₀, e₁) (Prod.ext h₀ h₁))
    · apply ContinuousMap.ext
      intro t
      simpa only [eval_apply, path_const, ContinuousMap.const_apply] using
        eval_prodHomeomorph_snd f g b₀ b₁ (const (e₀, e₁) (Prod.ext h₀ h₁)) t

end ProdConst

end ContinuousMap.HomotopyFiber
