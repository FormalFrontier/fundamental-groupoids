/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.Transport
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.BoundaryHomotopy
public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.BoundaryPath
public import FundamentalGroupoids.FundamentalGroup

/-!
# Change of basepoint on homotopy groups

`HomotopyGroup.equivOfPath` changes the basepoint along a path for every cube
index type. Its underlying function is `HomotopyGroup.pathMap`, and its inverse
is the same construction along the reversed path. Its characteristic property
is existence of a homotopy whose boundary traces the prescribed path.

Transport respects constant classes, composition and endpoint-fixed homotopies
of paths, and commutes with arbitrary continuous maps. For an empty index type,
it preserves the component of the represented point of the target space; this
component need not be the component of the chosen basepoint.

`HomotopyGroup.mulEquivOfPath` retains the given decidable equality and nonempty
index instances and the resulting homotopy-group structures. Concatenation in
these structures traverses the right factor first. In degree one transport
agrees with change of basepoint on the fundamental group, traversing the reverse
basepoint path, the loop, and then the basepoint path.

## References

The construction uses Mathlib's generalized loops, homotopy groups, path
homotopies and fundamental groups, together with the moving-boundary homotopies
and their comparison theorem in the imported modules.
-/

public section

noncomputable section

open scoped unitInterval

universe u v w

namespace HomotopyGroup

variable {N : Type u} {X : Type v} {Y : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable {x y z : X}

/-- Transport along the constant path is the identity on homotopy classes. -/
@[simp]
theorem pathMap_refl (x : X) :
    pathMap (N := N) (Path.refl x) = id := by
  funext a
  refine Quotient.inductionOn a ?_
  intro p
  exact (pathMap_mk_eq_iff (Path.refl x) p p).2
    ⟨⟨ContinuousMap.Homotopy.refl p.val, fun _ s hs =>
      (congrFun (GenLoop.coe_coe p) s).trans (GenLoop.boundary p s hs)⟩⟩

/-- Successive changes of basepoint compose in the order of path traversal. -/
theorem pathMap_trans (γ : Path x y) (δ : Path y z) :
    pathMap (N := N) (γ.trans δ) = pathMap δ ∘ pathMap γ := by
  funext a
  refine Quotient.inductionOn a ?_
  intro p
  change pathMap (γ.trans δ) (⟦p⟧ : HomotopyGroup N X x) =
    pathMap δ (pathMap γ (⟦p⟧ : HomotopyGroup N X x))
  rw [pathMap_class γ p, pathMap_class δ (GenLoop.pathMap γ p)]
  apply (pathMap_mk_eq_iff (γ.trans δ) p
    (GenLoop.pathMap δ (GenLoop.pathMap γ p))).2
  refine ⟨⟨(GenLoop.homotopyAlong γ p).trans
    (GenLoop.homotopyAlong δ (GenLoop.pathMap γ p)), ?_⟩⟩
  exact GenLoop.homotopy_trans_boundary (γ := γ) (δ := δ)
    (GenLoop.homotopyAlong γ p) (GenLoop.homotopyAlong δ (GenLoop.pathMap γ p))
    (GenLoop.homotopyAlong_boundary γ p)
    (GenLoop.homotopyAlong_boundary δ (GenLoop.pathMap γ p))

/-- Transport depends only on the homotopy class of the basepoint path relative
its endpoints. -/
theorem pathMap_eq_of_homotopic {γ δ : Path x y} (h : γ.Homotopic δ) :
    pathMap (N := N) γ = pathMap δ := by
  funext a
  refine Quotient.inductionOn a ?_
  intro p
  rw [pathMap_class δ p]
  apply (pathMap_mk_eq_iff γ p (GenLoop.pathMap δ p)).2
  obtain ⟨H, hH⟩ :=
    (GenLoop.exists_homotopy_boundary_iff_of_homotopic
      (p := p) (q := GenLoop.pathMap δ p) h).mpr
      ⟨GenLoop.homotopyAlong δ p, GenLoop.homotopyAlong_boundary δ p⟩
  exact ⟨⟨H, hH⟩⟩

/-- Reversing the basepoint path undoes transport. -/
@[simp]
theorem pathMap_symm_pathMap (γ : Path x y) (a : HomotopyGroup N X x) :
    pathMap γ.symm (pathMap γ a) = a := by
  calc
    _ = pathMap (γ.trans γ.symm) a := (congrFun (pathMap_trans γ γ.symm) a).symm
    _ = pathMap (Path.refl x) a :=
      congrFun (pathMap_eq_of_homotopic (Path.Homotopic.trans_symm γ)) a
    _ = a := congrFun (pathMap_refl x) a

/-- Transport undoes transport along the reversed basepoint path. -/
@[simp]
theorem pathMap_pathMap_symm (γ : Path x y) (a : HomotopyGroup N X y) :
    pathMap γ (pathMap γ.symm a) = a := by
  calc
    _ = pathMap (γ.symm.trans γ) a := (congrFun (pathMap_trans γ.symm γ) a).symm
    _ = pathMap (Path.refl y) a :=
      congrFun (pathMap_eq_of_homotopic (Path.Homotopic.symm_trans γ)) a
    _ = a := congrFun (pathMap_refl y) a

/-- Change of basepoint along a path on the existing homotopy-group carriers.
The inverse is transport along the reversed path. No condition on the cube
index type is needed. -/
def equivOfPath (γ : Path x y) : HomotopyGroup N X x ≃ HomotopyGroup N X y where
  toFun := pathMap γ
  invFun := pathMap γ.symm
  left_inv := pathMap_symm_pathMap γ
  right_inv := pathMap_pathMap_symm γ

/-- The underlying function is the map induced by the generalized-loop map. -/
theorem coe_equivOfPath (γ : Path x y) :
    (equivOfPath γ : HomotopyGroup N X x → HomotopyGroup N X y) = pathMap γ := by
  rfl

/-- Apply change of basepoint using the component-induced path map. -/
theorem equivOfPath_apply (γ : Path x y) (a : HomotopyGroup N X x) :
    equivOfPath γ a = pathMap γ a := by
  rfl

/-- Apply the inverse using transport along the reversed path. -/
theorem equivOfPath_symm_apply (γ : Path x y) (a : HomotopyGroup N X y) :
    (equivOfPath γ).symm a = pathMap γ.symm a := by
  rfl

/-- Change of basepoint on a representative generalized loop. -/
@[simp]
theorem equivOfPath_class (γ : Path x y) (p : GenLoop N X x) :
    equivOfPath γ (⟦p⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.pathMap γ p⟧ : HomotopyGroup N X y) :=
  pathMap_class γ p

/-- The characteristic property of change of basepoint is a homotopy tracing
exactly the given path on the whole cube boundary. -/
theorem equivOfPath_mk_eq_iff (γ : Path x y)
    (p : GenLoop N X x) (q : GenLoop N X y) :
    equivOfPath γ (⟦p⟧ : HomotopyGroup N X x) = (⟦q⟧ : HomotopyGroup N X y) ↔
      Nonempty {H : ContinuousMap.Homotopy p.val q.val //
        ∀ t s, s ∈ Cube.boundary N → H (t, s) = γ t} :=
  pathMap_mk_eq_iff γ p q

/-- Constant generalized loops represent corresponding classes under transport. -/
theorem equivOfPath_const (γ : Path x y) :
    equivOfPath γ (⟦GenLoop.const⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.const⟧ : HomotopyGroup N X y) := by
  apply (equivOfPath_mk_eq_iff γ GenLoop.const GenLoop.const).2
  let H : ContinuousMap.Homotopy (GenLoop.const : GenLoop N X x).val
      (GenLoop.const : GenLoop N X y).val :=
    { toFun := fun r => γ r.1
      continuous_toFun := γ.continuous.comp continuous_fst
      map_zero_left := fun _ => γ.source
      map_one_left := fun _ => γ.target }
  exact ⟨⟨H, fun _ _ _ => rfl⟩⟩

/-- The constant basepoint path gives the identity equivalence. -/
@[simp]
theorem equivOfPath_refl (x : X) :
    equivOfPath (N := N) (Path.refl x) = Equiv.refl (HomotopyGroup N X x) := by
  apply Equiv.ext
  intro a
  exact congrFun (pathMap_refl x) a

/-- Reversing the path gives the inverse equivalence. -/
@[simp]
theorem equivOfPath_symm (γ : Path x y) :
    equivOfPath (N := N) γ.symm = (equivOfPath γ).symm := by
  apply Equiv.ext
  intro a
  rfl

/-- Change of basepoint respects concatenation of paths. -/
theorem equivOfPath_trans (γ : Path x y) (δ : Path y z) :
    equivOfPath (N := N) (γ.trans δ) = (equivOfPath γ).trans (equivOfPath δ) := by
  apply Equiv.ext
  intro a
  exact congrFun (pathMap_trans γ δ) a

/-- Endpoint-fixed homotopic paths give the same basepoint equivalence. -/
theorem equivOfPath_eq_of_homotopic {γ δ : Path x y} (h : γ.Homotopic δ) :
    equivOfPath (N := N) γ = equivOfPath δ := by
  apply Equiv.ext
  intro a
  exact congrFun (pathMap_eq_of_homotopic h) a

/-- The equivalence is induced by the continuous generalized-loop map on path
components. -/
theorem equivZerothHomotopy_equivOfPath (γ : Path x y) (a : HomotopyGroup N X x) :
    equivZerothHomotopy N y (equivOfPath γ a) =
      ZerothHomotopy.map (GenLoop.pathMap γ) (equivZerothHomotopy N x a) :=
  equivZerothHomotopy_pathMap γ a

/-- Change of basepoint commutes with postcomposition by any continuous map. -/
theorem equivOfPath_mapFun (f : C(X, Y)) (γ : Path x y)
    (a : HomotopyGroup N X x) :
    equivOfPath (γ.map f.continuous) (mapFun N f rfl a) =
      mapFun N f rfl (equivOfPath γ a) := by
  refine Quotient.inductionOn a ?_
  intro p
  change pathMap (γ.map f.continuous) (mapFun N f rfl (⟦p⟧ : HomotopyGroup N X x)) =
    mapFun N f rfl (pathMap γ (⟦p⟧ : HomotopyGroup N X x))
  rw [mapFun_class, pathMap_class γ p, mapFun_class]
  apply (pathMap_mk_eq_iff (γ.map f.continuous)
    (GenLoop.map f rfl p) (GenLoop.map f rfl (GenLoop.pathMap γ p))).2
  let H : ContinuousMap.Homotopy (GenLoop.map f rfl p).val
      (GenLoop.map f rfl (GenLoop.pathMap γ p)).val :=
    (ContinuousMap.Homotopy.refl f).comp (GenLoop.homotopyAlong γ p)
  refine ⟨⟨H, ?_⟩⟩
  intro t s hs
  change f (GenLoop.homotopyAlong γ p (t, s)) = f (γ t)
  exact congrArg f (GenLoop.homotopyAlong_boundary γ p t s hs)

/-- The naturality square as an equality of functions on the homotopy quotient. -/
theorem mapFun_comp_equivOfPath (f : C(X, Y)) (γ : Path x y) :
    mapFun N f (x := y) (y := f y) rfl ∘ equivOfPath γ =
      equivOfPath (γ.map f.continuous) ∘ mapFun N f (x := x) (y := f x) rfl := by
  funext a
  exact (equivOfPath_mapFun f γ a).symm

/-- With no cube coordinates, the boundary condition is vacuous. -/
theorem equivOfPath_mk_eq_iff_of_isEmpty [IsEmpty N] (γ : Path x y)
    (p : GenLoop N X x) (q : GenLoop N X y) :
    equivOfPath γ (⟦p⟧ : HomotopyGroup N X x) = (⟦q⟧ : HomotopyGroup N X y) ↔
      p.val.Homotopic q.val := by
  rw [equivOfPath_mk_eq_iff]
  constructor
  · rintro ⟨⟨H, _⟩⟩
    exact ⟨H⟩
  · rintro ⟨H⟩
    exact ⟨⟨H, fun _ _ ⟨i, _⟩ => isEmptyElim i⟩⟩

/-- For an empty cube index, transport preserves the represented component of
`X`, without identifying it with the component of the chosen basepoint. -/
theorem homotopyGroupEquivZerothHomotopyOfIsEmpty_equivOfPath [IsEmpty N]
    (γ : Path x y) (a : HomotopyGroup N X x) :
    homotopyGroupEquivZerothHomotopyOfIsEmpty N y (equivOfPath γ a) =
      homotopyGroupEquivZerothHomotopyOfIsEmpty N x a := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [equivOfPath_class]
  change ZerothHomotopy.mk (GenLoop.pathMap γ p (0 : N → I)) =
    ZerothHomotopy.mk (p (0 : N → I))
  apply Eq.symm
  apply Quotient.sound
  exact ⟨{
    toFun := fun t => GenLoop.homotopyAlong γ p (t, (0 : N → I))
    continuous_toFun := (GenLoop.homotopyAlong γ p).continuous.comp
      (continuous_id.prodMk continuous_const)
    source' := GenLoop.homotopyAlong_apply_zero γ p _
    target' := GenLoop.homotopyAlong_apply_one γ p _ }⟩

/-- In degree one, transport agrees with fundamental-group change of basepoint.
The chronological order is the reversed path, the loop, and the path. -/
theorem pi1MulEquivFundamentalGroup_equivOfPath (γ : Path x y)
    (a : HomotopyGroup (Fin 1) X x) :
    pi1MulEquivFundamentalGroup (X := X) (x := y) (equivOfPath γ a) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath γ
        (pi1MulEquivFundamentalGroup (X := X) (x := x) a) := by
  refine Quotient.inductionOn a ?_
  intro p
  rw [equivOfPath_class]
  exact pi1MulEquivFundamentalGroup_eq_of_homotopy γ p (GenLoop.pathMap γ p)
    (GenLoop.homotopyAlong γ p) (GenLoop.homotopyAlong_boundary γ p)

section Multiplicative

variable [DecidableEq N] [Nonempty N]

/-- Change of basepoint as a multiplicative equivalence for the given
positive-degree homotopy-group structures. -/
def mulEquivOfPath (γ : Path x y) :
    HomotopyGroup N X x ≃* HomotopyGroup N X y where
  toEquiv := equivOfPath γ
  map_mul' a b := by
    refine Quotient.inductionOn₂
      (motive := fun a b : HomotopyGroup N X x =>
        equivOfPath γ (a * b) = equivOfPath γ a * equivOfPath γ b) a b ?_
    intro p q
    let i : N := Classical.arbitrary N
    have hmulX := HomotopyGroup.mul_spec (N := N) (X := X) (x := x)
      (i := i) (p := p) (q := q)
    have hmulY := HomotopyGroup.mul_spec (N := N) (X := X) (x := y)
      (i := i) (p := GenLoop.pathMap γ p) (q := GenLoop.pathMap γ q)
    have hmoving : pathMap γ (⟦GenLoop.transAt i q p⟧ : HomotopyGroup N X x) =
        (⟦GenLoop.transAt i (GenLoop.pathMap γ q) (GenLoop.pathMap γ p)⟧ :
          HomotopyGroup N X y) := by
      apply (pathMap_mk_eq_iff γ _ _).2
      exact ⟨⟨GenLoop.homotopyTransAt i γ
        (GenLoop.homotopyAlong γ q) (GenLoop.homotopyAlong γ p)
        (GenLoop.homotopyAlong_boundary γ q) (GenLoop.homotopyAlong_boundary γ p),
        GenLoop.homotopyTransAt_boundary i γ
          (GenLoop.homotopyAlong γ q) (GenLoop.homotopyAlong γ p)
          (GenLoop.homotopyAlong_boundary γ q) (GenLoop.homotopyAlong_boundary γ p)⟩⟩
    have hright := congrArg₂ (fun a b : HomotopyGroup N X y => a * b)
      (equivOfPath_class γ p) (equivOfPath_class γ q)
    exact Eq.trans (α := HomotopyGroup N X y) (congrArg (equivOfPath γ) hmulX)
      (Eq.trans (α := HomotopyGroup N X y) hmoving
        (Eq.trans (α := HomotopyGroup N X y) hmulY.symm hright.symm))

/-- Forgetting multiplication gives the all-index basepoint equivalence. -/
theorem mulEquivOfPath_toEquiv (γ : Path x y) :
    (mulEquivOfPath (N := N) γ).toEquiv = equivOfPath γ := by
  rfl

/-- The multiplicative and all-index equivalences have the same action. -/
@[simp]
theorem mulEquivOfPath_apply (γ : Path x y) (a : HomotopyGroup N X x) :
    mulEquivOfPath γ a = equivOfPath γ a := by
  rfl

/-- The constant path gives the identity multiplicative equivalence. -/
@[simp]
theorem mulEquivOfPath_refl (x : X) :
    mulEquivOfPath (N := N) (Path.refl x) = MulEquiv.refl (HomotopyGroup N X x) := by
  apply MulEquiv.ext
  intro a
  exact congrFun (pathMap_refl x) a

/-- Reversing a path gives the inverse multiplicative equivalence. -/
@[simp]
theorem mulEquivOfPath_symm (γ : Path x y) :
    mulEquivOfPath (N := N) γ.symm = (mulEquivOfPath γ).symm := by
  apply MulEquiv.ext
  intro a
  rfl

/-- Multiplicative transport respects concatenation of basepoint paths. -/
theorem mulEquivOfPath_trans (γ : Path x y) (δ : Path y z) :
    mulEquivOfPath (N := N) (γ.trans δ) =
      (mulEquivOfPath γ).trans (mulEquivOfPath δ) := by
  apply MulEquiv.ext
  intro a
  exact congrFun (pathMap_trans γ δ) a

/-- Endpoint-fixed homotopic paths give the same multiplicative equivalence. -/
theorem mulEquivOfPath_eq_of_homotopic {γ δ : Path x y} (h : γ.Homotopic δ) :
    mulEquivOfPath (N := N) γ = mulEquivOfPath δ := by
  apply MulEquiv.ext
  intro a
  exact congrFun (pathMap_eq_of_homotopic h) a

/-- Multiplicative transport commutes with the based homomorphism induced by a
continuous map. -/
theorem mulEquivOfPath_map (f : C(X, Y)) (γ : Path x y)
    (a : HomotopyGroup N X x) :
    mulEquivOfPath (γ.map f.continuous) (map N f rfl a) =
      map N f rfl (mulEquivOfPath γ a) := by
  simpa only [mulEquivOfPath_apply, coe_map_eq_mapFun] using
    equivOfPath_mapFun f γ a

/-- The multiplicative naturality square commutes as a diagram of homomorphisms. -/
theorem map_comp_mulEquivOfPath (f : C(X, Y)) (γ : Path x y) :
    (map N f (x := y) (y := f y) rfl).comp (mulEquivOfPath γ).toMonoidHom =
      (mulEquivOfPath (γ.map f.continuous)).toMonoidHom.comp
        (map N f (x := x) (y := f x) rfl) := by
  apply MonoidHom.ext
  intro a
  exact (mulEquivOfPath_map f γ a).symm

end Multiplicative

/-- The degree-one comparison with the fundamental group intertwines the
multiplicative basepoint equivalences. -/
theorem mulEquivOfPath_trans_pi1MulEquivFundamentalGroup (γ : Path x y) :
    (mulEquivOfPath (N := Fin 1) γ).trans
        (pi1MulEquivFundamentalGroup (X := X) (x := y)) =
      (pi1MulEquivFundamentalGroup (X := X) (x := x)).trans
        (FundamentalGroup.fundamentalGroupMulEquivOfPath γ) := by
  apply MulEquiv.ext
  intro a
  exact pi1MulEquivFundamentalGroup_equivOfPath γ a

end HomotopyGroup
