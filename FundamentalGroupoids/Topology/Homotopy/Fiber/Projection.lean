/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.Fiber.Prod
public import FundamentalGroupoids.Topology.Homotopy.Fiber.Contractible

/-!
# Strong deformation of a projection homotopy fiber

The ordinary homotopy fiber of the first projection `E × F → E` over `b`
strongly deformation retracts onto the constant-path section parametrized by `F`.
The retraction retains the second source coordinate. At time `u`, the deformation
retains that coordinate and shortens the incoming path to its initial segment of
length `1 - u`. Every point of the section is fixed throughout.

The construction uses the free-factor comparison `compFstHomeomorph` and the
relative contraction `idContraction`. All topologies are the original product,
subspace and compact-open topologies; no nonemptiness assumption on `F` is needed.

## References

* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 7, §3, p. 50:
  time shortening, through the identity-fiber and initial-segment constructions.
* Mathlib's ordinary homotopy, relative homotopy and homotopy-equivalence structures.
-/

@[expose] public section

open unitInterval
open scoped Topology

namespace ContinuousMap.HomotopyFiber

universe uE uF vE vF

variable {E : Type uE} {F : Type uF} [TopologicalSpace E] [TopologicalSpace F]
variable (b : E)

local notation "H" => HomotopyFiber (ContinuousMap.fst : C(E × F, E)) b
local notation "K" => HomotopyFiber (ContinuousMap.id E) b

-- Transport the entire comparison, including its source topology.
private theorem comparison_snd {g : C(E × F, E)}
    (h : (ContinuousMap.id E).comp ContinuousMap.fst = g)
    (z : HomotopyFiber g b) :
    let e : HomotopyFiber g b ≃ₜ K × F :=
      Eq.mp
        (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F) h)
        (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
    (e z).2 = (point z).2 := by
  cases h
  exact compFstHomeomorph_snd (Z := F) (ContinuousMap.id E) b z

private theorem comparison_path {g : C(E × F, E)}
    (h : (ContinuousMap.id E).comp ContinuousMap.fst = g)
    (z : HomotopyFiber g b) :
    let e : HomotopyFiber g b ≃ₜ K × F :=
      Eq.mp
        (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F) h)
        (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
    path (e z).1 = path z := by
  cases h
  exact path_compFstHomeomorph_fst (Z := F) (ContinuousMap.id E) b z

private theorem comparison_eval {g : C(E × F, E)}
    (h : (ContinuousMap.id E).comp ContinuousMap.fst = g)
    (z : HomotopyFiber g b) (t : I) :
    let e : HomotopyFiber g b ≃ₜ K × F :=
      Eq.mp
        (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F) h)
        (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
    eval t (e z).1 = eval t z := by
  cases h
  exact congrArg (fun γ : C(I, E) => γ t)
    (path_compFstHomeomorph_fst (Z := F) (ContinuousMap.id E) b z)

private theorem comparison_symm_point {g : C(E × F, E)}
    (h : (ContinuousMap.id E).comp ContinuousMap.fst = g) (a : K) (y : F) :
    let e : HomotopyFiber g b ≃ₜ K × F :=
      Eq.mp
        (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F) h)
        (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
    point (e.symm (a, y)) = (point a, y) := by
  cases h
  exact point_compFstHomeomorph_symm (Z := F) (ContinuousMap.id E) b a y

private theorem comparison_symm_path {g : C(E × F, E)}
    (h : (ContinuousMap.id E).comp ContinuousMap.fst = g) (a : K) (y : F) :
    let e : HomotopyFiber g b ≃ₜ K × F :=
      Eq.mp
        (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F) h)
        (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
    path (e.symm (a, y)) = path a := by
  cases h
  exact path_compFstHomeomorph_symm (Z := F) (ContinuousMap.id E) b a y

/-- Retain the free source coordinate of the first-projection homotopy fiber. -/
def fstRetraction : C(H, F) :=
  ContinuousMap.snd.comp point

/-- The retraction is the second coordinate of the retained source point. -/
@[simp]
theorem fstRetraction_apply (z : H) : fstRetraction b z = (point z).2 :=
  rfl

/-- Include each free coordinate with source point `(b, y)` and constant incoming path. -/
def fstSection : C(F, H) := by
  let e : H ≃ₜ K × F :=
    Eq.mp
      (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F)
        (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))))
      (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
  exact (e.symm : C(K × F, H)).comp
    ((ContinuousMap.const F (const (f := ContinuousMap.id E) (b := b) b rfl)).prodMk
      (ContinuousMap.id F))

/-- The section is the constant-path fiber constructor. -/
theorem fstSection_apply (y : F) :
    fstSection b y = const (f := (ContinuousMap.fst : C(E × F, E)))
      (b := b) (b, y) rfl := by
  apply ext
  · exact (comparison_symm_point b
      (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))) _ y).trans
      ((Prod.ext (point_const (f := ContinuousMap.id E) (b := b) b rfl) rfl).trans
        (point_const (f := (ContinuousMap.fst : C(E × F, E))) (b := b) (b, y) rfl).symm)
  · exact (comparison_symm_path b
      (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))) _ y).trans
      ((path_const (f := ContinuousMap.id E) (b := b) b rfl).trans
        (path_const (f := (ContinuousMap.fst : C(E × F, E))) (b := b) (b, y) rfl).symm)

/-- The section retains the specified basepoint and the supplied free coordinate. -/
@[simp]
theorem point_fstSection (y : F) : point (fstSection b y) = (b, y) := by
  exact (congrArg (point (f := (ContinuousMap.fst : C(E × F, E))) (b := b))
    (fstSection_apply b y)).trans
    (point_const (f := (ContinuousMap.fst : C(E × F, E))) (b := b) (b, y) rfl)

/-- The complete path of every section point is constant at the basepoint. -/
@[simp]
theorem path_fstSection (y : F) : path (fstSection b y) = ContinuousMap.const I b := by
  exact (congrArg (path (f := (ContinuousMap.fst : C(E × F, E))) (b := b))
    (fstSection_apply b y)).trans
    (path_const (f := (ContinuousMap.fst : C(E × F, E))) (b := b) (b, y) rfl)

/-- Every path evaluation of a section point is the basepoint. -/
theorem eval_fstSection (y : F) (t : I) : eval t (fstSection b y) = b := by
  rw [eval_apply, path_fstSection, ContinuousMap.const_apply]

/-- Section followed by retraction is the identity on the free factor. -/
@[simp]
theorem fstRetraction_comp_fstSection :
    (fstRetraction (F := F) b).comp (fstSection b) = ContinuousMap.id F := by
  apply ContinuousMap.ext
  intro y
  exact congrArg Prod.snd (point_fstSection b y)

/-- The constant-path section is injective. -/
theorem fstSection_injective : Function.Injective (fstSection (F := F) b) := by
  intro y y' h
  have h' := congrArg (fstRetraction b) h
  simpa only [fstRetraction_apply, point_fstSection] using h'

/-- The section image consists exactly of the fiber points with constant entire path. -/
theorem mem_range_fstSection_iff (z : H) :
    z ∈ Set.range (fstSection b) ↔ path z = ContinuousMap.const I b := by
  constructor
  · rintro ⟨y, rfl⟩
    exact path_fstSection b y
  · intro hγ
    refine ⟨fstRetraction b z, ?_⟩
    have hp : (point z).1 = b := by
      have h := path_one z
      rw [hγ] at h
      exact h.symm
    apply ext
    · rw [point_fstSection]
      exact Prod.ext hp.symm rfl
    · exact (path_fstSection b _).trans hγ.symm

/-- Reconstruct a section point from its retained free coordinate. -/
theorem fstSection_fstRetraction_of_mem_range (z : H)
    (hz : z ∈ Set.range (fstSection b)) : fstSection b (fstRetraction b z) = z := by
  rcases hz with ⟨y, rfl⟩
  rw [fstRetraction_apply, point_fstSection]

/-- Shorten the incoming path while retaining the free coordinate, fixing the whole
constant-path section at every time. This transports the identity-fiber contraction
and its time-shortening construction from May, Chapter 7, §3, p. 50. -/
noncomputable def fstDeformation :
    (ContinuousMap.id H).HomotopyRel
      ((fstSection b).comp (fstRetraction b)) (Set.range (fstSection b)) := by
  let e : H ≃ₜ K × F :=
    Eq.mp
      (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F)
        (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))))
      (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
  have hsnd {g : C(E × F, E)}
      (h : (ContinuousMap.id E).comp ContinuousMap.fst = g)
      (z : HomotopyFiber g b) :
      let e₀ : HomotopyFiber g b ≃ₜ K × F :=
        Eq.mp
          (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F) h)
          (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
      (e₀ z).2 = (point z).2 := by
    cases h
    exact compFstHomeomorph_snd (Z := F) (ContinuousMap.id E) b z
  let q : C(I × H, I × K) :=
    (ContinuousMap.fst : C(I × H, I)).prodMk
      ((ContinuousMap.fst : C(K × F, K)).comp
        ((e : C(H, K × F)).comp ContinuousMap.snd))
  let k : C(I × H, H) :=
    (e.symm : C(K × F, H)).comp
      (((idContraction b).toContinuousMap.comp q).prodMk
        ((ContinuousMap.snd : C(K × F, F)).comp
          ((e : C(H, K × F)).comp ContinuousMap.snd)))
  refine { toContinuousMap := k, map_zero_left := ?_, map_one_left := ?_, prop' := ?_ }
  · intro z
    change e.symm (idContraction b (0, (e z).1), (e z).2) = z
    rw [idContraction_zero]
    exact e.symm_apply_apply z
  · intro z
    change e.symm (idContraction b (1, (e z).1), (e z).2) =
      e.symm (const (f := ContinuousMap.id E) (b := b) b rfl, fstRetraction b z)
    rw [idContraction_one,
      hsnd (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))),
      fstRetraction_apply]
    rfl
  · intro u z hz
    rcases hz with ⟨y, rfl⟩
    change e.symm (idContraction b (u, (e (fstSection b y)).1),
      (e (fstSection b y)).2) =
        e.symm (const (f := ContinuousMap.id E) (b := b) b rfl, y)
    have hs : e (fstSection b y) = (const (f := ContinuousMap.id E) (b := b) b rfl, y) :=
      e.apply_symm_apply _
    rw [hs, idContraction_const]
    rfl

private theorem comparison_deformation (u : I) (z : H) :
    let e : H ≃ₜ K × F :=
      Eq.mp
        (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F)
          (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))))
        (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
    e (fstDeformation b (u, z)) =
      (idContraction b (u, (e z).1), (e z).2) := by
  let e : H ≃ₜ K × F :=
    Eq.mp
      (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F)
        (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))))
      (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
  change e (e.symm (idContraction b (u, (e z).1), (e z).2)) = _
  exact e.apply_symm_apply _

/-- The moving source point follows the incoming path backwards and retains the free factor. -/
@[simp]
theorem point_fstDeformation (u : I) (z : H) :
    point (fstDeformation b (u, z)) = (eval (unitInterval.symm u) z, fstRetraction b z) := by
  let e : H ≃ₜ K × F :=
    Eq.mp
      (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F)
        (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))))
      (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
  change point (e.symm (idContraction b (u, (e z).1), (e z).2)) = _
  rw [comparison_symm_point b
      (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))),
    point_idContraction,
    comparison_eval b
      (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))),
    comparison_snd b
      (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))),
    fstRetraction_apply]

/-- The complete deformed path is the existing initial-segment map at complementary time. -/
theorem path_fstDeformation (u : I) (z : H) :
    path (fstDeformation b (u, z)) =
      ContinuousMap.initialSegment (unitInterval.symm u, path z) := by
  let e : H ≃ₜ K × F :=
    Eq.mp
      (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F)
        (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))))
      (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
  change path (e.symm (idContraction b (u, (e z).1), (e z).2)) = _
  rw [comparison_symm_path b
      (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E)))]
  apply ContinuousMap.ext
  intro t
  rw [path_idContraction_apply, comparison_path b
      (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))),
    ContinuousMap.initialSegment_apply]

/-- The deformed path keeps the same multiplicative prefix clock at every path time. -/
@[simp]
theorem path_fstDeformation_apply (u : I) (z : H) (t : I) :
    path (fstDeformation b (u, z)) t = path z (unitInterval.symm u * t) := by
  rw [path_fstDeformation, ContinuousMap.initialSegment_apply]

/-- Evaluation of the deformation is evaluation of the shortened incoming path. -/
theorem eval_fstDeformation (u : I) (z : H) (t : I) :
    eval t (fstDeformation b (u, z)) = eval (unitInterval.symm u * t) z := by
  exact path_fstDeformation_apply b u z t

/-- Reconstruct the deformed point with the original fiber constructor and full shortened path. -/
theorem fstDeformation_apply (u : I) (z : H) :
    fstDeformation b (u, z) =
      mk (eval (unitInterval.symm u) z, fstRetraction b z)
        (ContinuousMap.initialSegment (unitInterval.symm u, path z))
        (by rw [ContinuousMap.initialSegment_apply_zero, path_zero])
        (by rw [ContinuousMap.initialSegment_apply_one]; rfl) := by
  apply ext
  · exact point_fstDeformation b u z
  · exact path_fstDeformation b u z

/-- At time zero the deformation is the identity. -/
theorem fstDeformation_zero (z : H) : fstDeformation b (0, z) = z :=
  (fstDeformation b).apply_zero z

/-- At time one the deformation is section after retraction. -/
theorem fstDeformation_one (z : H) :
    fstDeformation b (1, z) = fstSection b (fstRetraction b z) :=
  (fstDeformation b).apply_one z

/-- The free coordinate is preserved at every deformation time. -/
theorem fstRetraction_fstDeformation (u : I) (z : H) :
    fstRetraction b (fstDeformation b (u, z)) = fstRetraction b z := by
  rw [fstRetraction_apply, point_fstDeformation]

/-- The jointly continuous deformation strictly preserves the whole retraction map. -/
theorem fstRetraction_comp_fstDeformation :
    (fstRetraction (F := F) b).comp (fstDeformation b).toContinuousMap =
      (fstRetraction b).comp ContinuousMap.snd := by
  apply ContinuousMap.ext
  rintro ⟨u, z⟩
  exact fstRetraction_fstDeformation b u z

/-- Every section point is fixed at every deformation time. -/
@[simp]
theorem fstDeformation_fstSection (u : I) (y : F) :
    fstDeformation b (u, fstSection b y) = fstSection b y :=
  (fstDeformation b).eq_fst u ⟨y, rfl⟩

/-- The deformation fixes the section as an equality of jointly continuous maps. -/
theorem fstDeformation_comp_fstSection :
    (fstDeformation (F := F) b).toContinuousMap.comp
        ((ContinuousMap.id I).prodMap (fstSection b)) =
      (fstSection b).comp ContinuousMap.snd := by
  apply ContinuousMap.ext
  rintro ⟨u, y⟩
  exact fstDeformation_fstSection b u y

/-- The first-projection homotopy fiber is homotopy equivalent to the free factor,
with the coordinate retraction and constant-path section as its two maps. -/
noncomputable def fstHomotopyEquiv : ContinuousMap.HomotopyEquiv H F where
  toFun := fstRetraction b
  invFun := fstSection b
  left_inv := ⟨(fstDeformation b).toHomotopy.symm⟩
  right_inv := by
    rw [fstRetraction_comp_fstSection]

/-- The forward bundled map of the equivalence is the coordinate retraction. -/
@[simp]
theorem fstHomotopyEquiv_toFun :
    (fstHomotopyEquiv (F := F) b).toFun = fstRetraction b :=
  rfl

/-- The inverse bundled map of the equivalence is the constant-path section. -/
@[simp]
theorem fstHomotopyEquiv_symm_toFun :
    (fstHomotopyEquiv (F := F) b).symm.toFun = fstSection b :=
  rfl

variable {E' : Type vE} {F' : Type vF}
variable [TopologicalSpace E'] [TopologicalSpace F']

private theorem comparison_naturality (P : C(E, E')) (Q : C(F, F'))
    {g : C(E × F, E)} {g' : C(E' × F', E')}
    (h : (ContinuousMap.id E).comp ContinuousMap.fst = g)
    (h' : (ContinuousMap.id E').comp ContinuousMap.fst = g')
    (w : ∀ x, g' ((P.prodMap Q) x) = P (g x)) :
    let e : HomotopyFiber g b ≃ₜ K × F :=
      Eq.mp
        (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F) h)
        (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
    let e' : HomotopyFiber g' (P b) ≃ₜ
        HomotopyFiber (ContinuousMap.id E') (P b) × F' :=
      Eq.mp
        (congrArg (fun g' : C(E' × F', E') =>
          HomotopyFiber g' (P b) ≃ₜ HomotopyFiber (ContinuousMap.id E') (P b) × F') h')
        (compFstHomeomorph (Z := F') (ContinuousMap.id E') (P b))
    (e' : C(HomotopyFiber g' (P b),
        HomotopyFiber (ContinuousMap.id E') (P b) × F')).comp
        (map (f := g) (f' := g') (b := b) (b' := P b)
          (P.prodMap Q) P w rfl) =
      ((map (f := ContinuousMap.id E) (f' := ContinuousMap.id E')
          (b := b) (b' := P b) P P (fun _ => rfl) rfl).prodMap Q).comp
        (e : C(HomotopyFiber g b, K × F)) := by
  cases h
  cases h'
  exact compFstHomeomorph_naturality (Z := F) (ContinuousMap.id E) b
    (Z' := F') (f' := ContinuousMap.id E') (b' := P b)
    P P Q (fun _ => rfl) rfl

/-- The projection-fiber retraction commutes with maps of both coordinates. -/
theorem fstRetraction_naturality (P : C(E, E')) (Q : C(F, F')) :
    (fstRetraction (F := F') (P b)).comp
        (map (f := (ContinuousMap.fst : C(E × F, E)))
          (f' := (ContinuousMap.fst : C(E' × F', E')))
          (b := b) (b' := P b) (P.prodMap Q) P (fun _ => rfl) rfl) =
      Q.comp (fstRetraction (F := F) b) := by
  apply ContinuousMap.ext
  intro z
  simpa only [ContinuousMap.comp_apply, fstRetraction_apply,
    ContinuousMap.prodMap_apply, Prod.map_apply'] using
    (congrArg Prod.snd
      (point_map (f := (ContinuousMap.fst : C(E × F, E)))
        (f' := (ContinuousMap.fst : C(E' × F', E')))
        (b := b) (b' := P b) (P.prodMap Q) P (fun _ => rfl) rfl z))

/-- The constant-path section commutes with maps of both coordinates. -/
theorem fstSection_naturality (P : C(E, E')) (Q : C(F, F')) :
    (map (f := (ContinuousMap.fst : C(E × F, E)))
        (f' := (ContinuousMap.fst : C(E' × F', E')))
        (b := b) (b' := P b) (P.prodMap Q) P (fun _ => rfl) rfl).comp
        (fstSection (F := F) b) =
      (fstSection (F := F') (P b)).comp Q := by
  apply ContinuousMap.ext
  intro y
  apply ContinuousMap.HomotopyFiber.ext
  · simpa only [ContinuousMap.comp_apply, point_fstSection,
      ContinuousMap.prodMap_apply, Prod.map_apply'] using
      (point_map (f := (ContinuousMap.fst : C(E × F, E)))
        (f' := (ContinuousMap.fst : C(E' × F', E')))
        (b := b) (b' := P b) (P.prodMap Q) P (fun _ => rfl) rfl
        (fstSection (F := F) b y))
  · simpa only [ContinuousMap.comp_apply, path_fstSection,
      ContinuousMap.comp_const] using
      (path_map (f := (ContinuousMap.fst : C(E × F, E)))
        (f' := (ContinuousMap.fst : C(E' × F', E')))
        (b := b) (b' := P b) (P.prodMap Q) P (fun _ => rfl) rfl
        (fstSection (F := F) b y))

/-- The projection-fiber deformation commutes strictly with maps of both coordinates. -/
theorem fstDeformation_naturality (P : C(E, E')) (Q : C(F, F')) :
    (fstDeformation (F := F') (P b)).toContinuousMap.comp
        ((ContinuousMap.id I).prodMap
          (map (f := (ContinuousMap.fst : C(E × F, E)))
            (f' := (ContinuousMap.fst : C(E' × F', E')))
            (b := b) (b' := P b) (P.prodMap Q) P (fun _ => rfl) rfl)) =
      (map (f := (ContinuousMap.fst : C(E × F, E)))
        (f' := (ContinuousMap.fst : C(E' × F', E')))
        (b := b) (b' := P b) (P.prodMap Q) P (fun _ => rfl) rfl).comp
        (fstDeformation (F := F) b).toContinuousMap := by
  let e : H ≃ₜ K × F :=
    Eq.mp
      (congrArg (fun g : C(E × F, E) => HomotopyFiber g b ≃ₜ K × F)
        (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E))))
      (compFstHomeomorph (Z := F) (ContinuousMap.id E) b)
  let e' :
      HomotopyFiber (ContinuousMap.fst : C(E' × F', E')) (P b) ≃ₜ
        HomotopyFiber (ContinuousMap.id E') (P b) × F' :=
    Eq.mp
      (congrArg (fun g : C(E' × F', E') =>
        HomotopyFiber g (P b) ≃ₜ HomotopyFiber (ContinuousMap.id E') (P b) × F')
        (ContinuousMap.id_comp (ContinuousMap.fst : C(E' × F', E'))))
      (compFstHomeomorph (Z := F') (ContinuousMap.id E') (P b))
  let M : C(HomotopyFiber (ContinuousMap.fst : C(E × F, E)) b,
      HomotopyFiber (ContinuousMap.fst : C(E' × F', E')) (P b)) :=
    map (f := (ContinuousMap.fst : C(E × F, E)))
      (f' := (ContinuousMap.fst : C(E' × F', E')))
      (b := b) (b' := P b) (P.prodMap Q) P (fun _ => rfl) rfl
  let N : C(HomotopyFiber (ContinuousMap.id E) b,
      HomotopyFiber (ContinuousMap.id E') (P b)) :=
    map (f := ContinuousMap.id E) (f' := ContinuousMap.id E')
      (b := b) (b' := P b) P P (fun _ => rfl) rfl
  have hE :
      (e' : C(HomotopyFiber (ContinuousMap.fst : C(E' × F', E')) (P b),
        HomotopyFiber (ContinuousMap.id E') (P b) × F')).comp M =
      (N.prodMap Q).comp
        (e : C(HomotopyFiber (ContinuousMap.fst : C(E × F, E)) b,
          HomotopyFiber (ContinuousMap.id E) b × F)) := by
    exact comparison_naturality b P Q
      (ContinuousMap.id_comp (ContinuousMap.fst : C(E × F, E)))
      (ContinuousMap.id_comp (ContinuousMap.fst : C(E' × F', E'))) (fun _ => rfl)
  have hE_apply (z : HomotopyFiber (ContinuousMap.fst : C(E × F, E)) b) :
      e' (M z) = (N ((e z).1), Q ((e z).2)) := by
    simpa only [ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
      Prod.map_apply', ContinuousMap.coe_coe] using
      (congrArg
        (fun k : C(HomotopyFiber (ContinuousMap.fst : C(E × F, E)) b,
          HomotopyFiber (ContinuousMap.id E') (P b) × F') => k z) hE)
  have hD' (u : I)
      (z : HomotopyFiber (ContinuousMap.fst : C(E' × F', E')) (P b)) :
      e' (fstDeformation (F := F') (P b) (u, z)) =
        (idContraction (P b) (u, (e' z).1), (e' z).2) := by
    exact comparison_deformation (F := F') (P b) u z
  apply ContinuousMap.ext
  rintro ⟨u, z⟩
  change fstDeformation (F := F') (P b) (u, M z) =
    M (fstDeformation (F := F) b (u, z))
  apply e'.injective
  calc
    e' (fstDeformation (F := F') (P b) (u, M z)) =
        (idContraction (P b) (u, (e' (M z)).1), (e' (M z)).2) :=
      hD' u (M z)
    _ = (idContraction (P b) (u, N ((e z).1)), Q ((e z).2)) := by
      rw [hE_apply z]
    _ = (N (idContraction b (u, (e z).1)), Q ((e z).2)) :=
      Prod.ext (idContraction_naturality P b (P b) rfl u ((e z).1)).symm rfl
    _ = (N ((e (fstDeformation (F := F) b (u, z))).1),
        Q ((e (fstDeformation (F := F) b (u, z))).2)) := by
      rw [comparison_deformation b u z]
    _ = e' (M (fstDeformation (F := F) b (u, z))) :=
      (hE_apply (fstDeformation (F := F) b (u, z))).symm

end ContinuousMap.HomotopyFiber
