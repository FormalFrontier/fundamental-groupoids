/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import FundamentalGroupoids.Topology.Homotopy.HomotopyGroup.BasepointEquiv
public import Mathlib.Algebra.Group.Action.End

/-!
# Fundamental-group actions on homotopy groups

Path-induced change of basepoint descends to an action of the fundamental
group on the generalized homotopy quotient. This construction applies to every
cube-index type, including the empty type. For a nonempty index type with
decidable equality, the action preserves the given homotopy-group multiplication.

The fundamental-group product traverses its right factor first, whereas
successive path transports compose in traversal order. Consequently the
resulting action is a left action. The multiplication-preserving action selects
this same underlying action.

## References

The construction uses Mathlib's path-homotopy quotient, fundamental group and
`MulAction.ofEndHom`, together with the change-of-basepoint coherence in
`HomotopyGroup.BasepointEquiv`. Mathlib's
`IsCoveringMap.fundamentalGroupMulAction` uses the same product convention for
its action on a covering fiber.
-/

public section

noncomputable section

universe u v w

namespace HomotopyGroup

variable {X : Type v} [TopologicalSpace X]

/-- Path transport as a monoid homomorphism from the fundamental group to
endomorphisms of the generalized homotopy quotient. -/
def fundamentalGroupEndHom (N : Type u) (x : X) :
    FundamentalGroup X x →* Function.End (HomotopyGroup N X x) where
  toFun g :=
    Quotient.liftOn' (FundamentalGroup.toPath g)
      (fun γ : Path x x => pathMap (N := N) γ)
      (fun _ _ h => pathMap_eq_of_homotopic h)
  map_one' := by
    change pathMap (N := N) (Path.refl x) = id
    exact pathMap_refl x
  map_mul' := by
    rintro ⟨γ⟩ ⟨δ⟩
    change pathMap (N := N) (δ.trans γ) = pathMap γ ∘ pathMap δ
    exact pathMap_trans δ γ

/-- On the class of a loop, the endomorphism is its path transport. -/
@[simp]
theorem fundamentalGroupEndHom_fromPath (N : Type u) {x : X} (γ : Path x x) :
    fundamentalGroupEndHom N x
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      (pathMap (N := N) γ : Function.End (HomotopyGroup N X x)) := by
  rfl

/-- The fundamental-group action induced by path transport, for every
cube-index type. No group structure on the homotopy quotient is required. -/
@[instance_reducible]
def fundamentalGroupMulAction (N : Type u) (x : X) :
    MulAction (FundamentalGroup X x) (HomotopyGroup N X x) :=
  MulAction.ofEndHom (fundamentalGroupEndHom N x)

attribute [local instance] fundamentalGroupMulAction

/-- The action evaluates the endomorphism induced by the fundamental group. -/
theorem fundamentalGroup_smul_def (N : Type u) {x : X}
    (g : FundamentalGroup X x) (a : HomotopyGroup N X x) :
    g • a = fundamentalGroupEndHom N x g a := by
  rfl

/-- A loop class acts by the prescribed path-induced change of basepoint. -/
@[simp]
theorem fundamentalGroup_fromPath_smul (N : Type u) {x : X}
    (γ : Path x x) (a : HomotopyGroup N X x) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) • a = pathMap γ a := by
  rfl

/-- The fundamental-group action preserves the given positive-degree
homotopy-group multiplication and has the all-index action as its parent. -/
@[instance_reducible]
def fundamentalGroupMulDistribMulAction (N : Type u) [DecidableEq N] [Nonempty N]
    (x : X) :
    MulDistribMulAction (FundamentalGroup X x) (HomotopyGroup N X x) where
  toMulAction := fundamentalGroupMulAction N x
  smul_one := by
    rintro ⟨γ⟩
    change pathMap (N := N) γ (1 : HomotopyGroup N X x) = 1
    simpa only [mulEquivOfPath_apply, equivOfPath_apply] using
      map_one (mulEquivOfPath (N := N) γ)
  smul_mul := by
    rintro ⟨γ⟩ a b
    change pathMap (N := N) γ (a * b) = pathMap γ a * pathMap γ b
    simpa only [mulEquivOfPath_apply, equivOfPath_apply] using
      map_mul (mulEquivOfPath (N := N) γ) a b

/-- Forgetting multiplicativity returns the selected all-index action. -/
@[simp]
theorem fundamentalGroupMulDistribMulAction_toMulAction (N : Type u)
    [DecidableEq N] [Nonempty N] (x : X) :
    (fundamentalGroupMulDistribMulAction N x).toMulAction =
      fundamentalGroupMulAction N x := by
  rfl

open scoped unitInterval

/-- The class of a loop acts on a representative by transporting that
representative along the loop. -/
theorem fundamentalGroup_fromPath_smul_mk (N : Type u) {x : X}
    (γ : Path x x) (p : GenLoop N X x) :
    @SMul.smul (FundamentalGroup X x) (HomotopyGroup N X x)
        (fundamentalGroupMulAction N x).toSMul
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
        (⟦p⟧ : HomotopyGroup N X x) =
      (⟦GenLoop.pathMap γ p⟧ : HomotopyGroup N X x) := by
  exact (fundamentalGroup_fromPath_smul N γ
    (⟦p⟧ : HomotopyGroup N X x)).trans (pathMap_class γ p)

/-- A loop class sends the class of `p` to the class of `q` exactly when the
original cube maps admit a homotopy whose value on the whole boundary follows
that loop at every time. No condition on the cube-index type is required. -/
theorem fundamentalGroup_fromPath_smul_mk_eq_iff (N : Type u) {x : X}
    (γ : Path x x) (p q : GenLoop N X x) :
    @SMul.smul (FundamentalGroup X x) (HomotopyGroup N X x)
        (fundamentalGroupMulAction N x).toSMul
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
        (⟦p⟧ : HomotopyGroup N X x) = (⟦q⟧ : HomotopyGroup N X x) ↔
      Nonempty {H : ContinuousMap.Homotopy p.val q.val //
        ∀ (t : I) (z : N → I), z ∈ Cube.boundary N → H (t, z) = γ t} := by
  constructor
  · intro h
    apply (pathMap_mk_eq_iff γ p q).mp
    exact (fundamentalGroup_fromPath_smul N γ
      (⟦p⟧ : HomotopyGroup N X x)).symm.trans h
  · intro h
    exact (fundamentalGroup_fromPath_smul N γ
      (⟦p⟧ : HomotopyGroup N X x)).trans ((pathMap_mk_eq_iff γ p q).mpr h)

/-- Based postcomposition is equivariant for the induced homomorphism on
fundamental groups, for every cube-index type and arbitrary basepoint equality. -/
theorem mapFun_fundamentalGroup_smul (N : Type u) {Y : Type w}
    [TopologicalSpace Y] {x : X} {y : Y} (f : C(X, Y)) (hf : f x = y)
    (g : FundamentalGroup X x) (a : HomotopyGroup N X x) :
    mapFun N f hf (g • a) =
      FundamentalGroup.mapOfEq f hf g • mapFun N f hf a := by
  subst y
  refine Quotient.inductionOn g ?_
  intro γ
  change mapFun N f rfl
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) • a) =
    FundamentalGroup.mapOfEq f rfl
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) • mapFun N f rfl a
  have hmap : FundamentalGroup.mapOfEq f rfl
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (γ.map f.continuous)) := by
    rw [FundamentalGroup.mapOfEq_apply]
    rfl
  rw [hmap]
  calc
    mapFun N f rfl
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) • a) =
        mapFun N f rfl (pathMap γ a) :=
      congrArg (mapFun N f rfl) (fundamentalGroup_fromPath_smul N γ a)
    _ = pathMap (γ.map f.continuous) (mapFun N f rfl a) := by
      simpa only [equivOfPath_apply] using (equivOfPath_mapFun f γ a).symm
    _ = FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (γ.map f.continuous)) • mapFun N f rfl a :=
      (fundamentalGroup_fromPath_smul N (γ.map f.continuous)
        (mapFun N f rfl a)).symm

/-- The induced positive-degree homomorphism is equivariant for the same
fundamental-group action, with the given homotopy-group structures. -/
theorem map_fundamentalGroup_smul (N : Type u) [DecidableEq N] [Nonempty N]
    {Y : Type w} [TopologicalSpace Y] {x : X} {y : Y}
    (f : C(X, Y)) (hf : f x = y)
    (g : FundamentalGroup X x) (a : HomotopyGroup N X x) :
    map N f hf (g • a) = FundamentalGroup.mapOfEq f hf g • map N f hf a := by
  simpa only [coe_map_eq_mapFun] using mapFun_fundamentalGroup_smul N f hf g a

/-- For an empty cube index, the fundamental-group action preserves every
represented free path component, not only the component of the basepoint. -/
theorem homotopyGroupEquivZerothHomotopyOfIsEmpty_fundamentalGroup_smul
    (N : Type u) [IsEmpty N] {x : X} (g : FundamentalGroup X x)
    (a : HomotopyGroup N X x) :
    homotopyGroupEquivZerothHomotopyOfIsEmpty N x (g • a) =
      homotopyGroupEquivZerothHomotopyOfIsEmpty N x a := by
  refine Quotient.inductionOn g ?_
  intro γ
  change homotopyGroupEquivZerothHomotopyOfIsEmpty N x
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) • a) =
    homotopyGroupEquivZerothHomotopyOfIsEmpty N x a
  exact (congrArg (homotopyGroupEquivZerothHomotopyOfIsEmpty N x)
    (fundamentalGroup_fromPath_smul N γ a)).trans (by
      simpa only [equivOfPath_apply] using
        homotopyGroupEquivZerothHomotopyOfIsEmpty_equivOfPath (N := N) γ a)

/-- The action on the homotopy quotient indexed by an empty type is the identity.
This follows from injectivity of the equivalence with free path components. -/
@[simp]
theorem fundamentalGroup_smul_eq_of_isEmpty (N : Type u) [IsEmpty N] {x : X}
    (g : FundamentalGroup X x) (a : HomotopyGroup N X x) : g • a = a := by
  apply (homotopyGroupEquivZerothHomotopyOfIsEmpty N x).injective
  exact homotopyGroupEquivZerothHomotopyOfIsEmpty_fundamentalGroup_smul N g a

/-- Under the degree-one comparison, the fundamental-group action is conjugation.
The reversed multiplication convention turns traversal of the reversed scalar
loop, the represented loop, and the scalar loop into `g * b * g⁻¹`. -/
theorem pi1MulEquivFundamentalGroup_fundamentalGroup_smul {x : X}
    (g : FundamentalGroup X x) (a : HomotopyGroup (Fin 1) X x) :
    pi1MulEquivFundamentalGroup (X := X) (x := x) (g • a) =
      g * pi1MulEquivFundamentalGroup (X := X) (x := x) a * g⁻¹ := by
  refine Quotient.inductionOn g ?_
  intro γ
  calc
    pi1MulEquivFundamentalGroup (X := X) (x := x)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) • a) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath γ
          (pi1MulEquivFundamentalGroup (X := X) (x := x) a) := by
      simpa only [fundamentalGroup_fromPath_smul, equivOfPath_apply] using
        pi1MulEquivFundamentalGroup_equivOfPath γ a
    _ = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) *
        pi1MulEquivFundamentalGroup (X := X) (x := x) a *
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))⁻¹ := by
      rfl

end HomotopyGroup
