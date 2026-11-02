/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber
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
